-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1474_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:39.073402+00:00
-- url     : https://prove2.me/submissions/7da10e86-68b7-4b5f-9d0d-893132304165

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
theorem support_rectangle_w1474_s0_0 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-863445181/5000000000 : ℝ)*x 0 + (5942692609/10000000000 : ℝ)*x 1 + (967745919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863445181/5000000000 : ℝ)^4445 ≤ (1276047993659/12500000000000 : ℝ)^3421 := by
    have hnat : (863445181 : ℕ)^4445*12500000000000^3421 ≤ 1276047993659^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863445181 5000000000 1276047993659 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5942692609/10000000000 : ℝ)^4445 ≤ (6356824399621/12500000000000 : ℝ)^3421 := by
    have hnat : (5942692609 : ℕ)^4445*12500000000000^3421 ≤ 6356824399621^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5942692609 10000000000 6356824399621 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967745919/2000000000 : ℝ)^4445 ≤ (778740416757/2000000000000 : ℝ)^3421 := by
    have hnat : (967745919 : ℕ)^4445*2000000000000^3421 ≤ 778740416757^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967745919 2000000000 778740416757 2000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-863445181/5000000000 : ℝ), (5942692609/10000000000 : ℝ), (967745919/2000000000 : ℝ)] ![(1276047993659/12500000000000 : ℝ), (6356824399621/12500000000000 : ℝ), (778740416757/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-863445181/5000000000 : ℝ)|^4445 ≤ (1276047993659/12500000000000 : ℝ)^3421
        have hw : |(-863445181/5000000000 : ℝ)|=(863445181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5942692609/10000000000 : ℝ)|^4445 ≤ (6356824399621/12500000000000 : ℝ)^3421
        have hw : |(5942692609/10000000000 : ℝ)|=(5942692609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967745919/2000000000 : ℝ)|^4445 ≤ (778740416757/2000000000000 : ℝ)^3421
        have hw : |(967745919/2000000000 : ℝ)|=(967745919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s0_1 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5486294137/10000000000 : ℝ)*x 0 + (-2348785141/10000000000 : ℝ)*x 1 + (2419364757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5486294137/10000000000 : ℝ)^4445 ≤ (11459828283393/25000000000000 : ℝ)^3421 := by
    have hnat : (5486294137 : ℕ)^4445*25000000000000^3421 ≤ 11459828283393^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486294137 10000000000 11459828283393 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2348785141/10000000000 : ℝ)^4445 ≤ (15223666850421/100000000000000 : ℝ)^3421 := by
    have hnat : (2348785141 : ℕ)^4445*100000000000000^3421 ≤ 15223666850421^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348785141 10000000000 15223666850421 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2419364757/5000000000 : ℝ)^4445 ≤ (7787403998189/20000000000000 : ℝ)^3421 := by
    have hnat : (2419364757 : ℕ)^4445*20000000000000^3421 ≤ 7787403998189^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419364757 5000000000 7787403998189 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5486294137/10000000000 : ℝ), (-2348785141/10000000000 : ℝ), (2419364757/5000000000 : ℝ)] ![(11459828283393/25000000000000 : ℝ), (15223666850421/100000000000000 : ℝ), (7787403998189/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5486294137/10000000000 : ℝ)|^4445 ≤ (11459828283393/25000000000000 : ℝ)^3421
        have hw : |(5486294137/10000000000 : ℝ)|=(5486294137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2348785141/10000000000 : ℝ)|^4445 ≤ (15223666850421/100000000000000 : ℝ)^3421
        have hw : |(-2348785141/10000000000 : ℝ)|=(2348785141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2419364757/5000000000 : ℝ)|^4445 ≤ (7787403998189/20000000000000 : ℝ)^3421
        have hw : |(2419364757/5000000000 : ℝ)|=(2419364757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s0_2 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54862943/100000000 : ℝ)*x 0 + (1209682337/2500000000 : ℝ)*x 1 + (-1174392569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54862943/100000000 : ℝ)^4445 ≤ (11459828725783/25000000000000 : ℝ)^3421 := by
    have hnat : (54862943 : ℕ)^4445*25000000000000^3421 ≤ 11459828725783^3421*100000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54862943 100000000 11459828725783 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209682337/2500000000 : ℝ)^4445 ≤ (38937018255311/100000000000000 : ℝ)^3421 := by
    have hnat : (1209682337 : ℕ)^4445*100000000000000^3421 ≤ 38937018255311^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209682337 2500000000 38937018255311 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174392569/5000000000 : ℝ)^4445 ≤ (3805916706289/25000000000000 : ℝ)^3421 := by
    have hnat : (1174392569 : ℕ)^4445*25000000000000^3421 ≤ 3805916706289^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174392569 5000000000 3805916706289 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54862943/100000000 : ℝ), (1209682337/2500000000 : ℝ), (-1174392569/5000000000 : ℝ)] ![(11459828725783/25000000000000 : ℝ), (38937018255311/100000000000000 : ℝ), (3805916706289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54862943/100000000 : ℝ)|^4445 ≤ (11459828725783/25000000000000 : ℝ)^3421
        have hw : |(54862943/100000000 : ℝ)|=(54862943/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209682337/2500000000 : ℝ)|^4445 ≤ (38937018255311/100000000000000 : ℝ)^3421
        have hw : |(1209682337/2500000000 : ℝ)|=(1209682337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1174392569/5000000000 : ℝ)|^4445 ≤ (3805916706289/25000000000000 : ℝ)^3421
        have hw : |(-1174392569/5000000000 : ℝ)|=(1174392569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s0_3 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4155553811/10000000000 : ℝ)*x 0 + (1545813847/5000000000 : ℝ)*x 1 + (5528075593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155553811/10000000000 : ℝ)^4445 ≤ (15975114903347/50000000000000 : ℝ)^3421 := by
    have hnat : (4155553811 : ℕ)^4445*50000000000000^3421 ≤ 15975114903347^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155553811 10000000000 15975114903347 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545813847/5000000000 : ℝ)^4445 ≤ (1087817663223/5000000000000 : ℝ)^3421 := by
    have hnat : (1545813847 : ℕ)^4445*5000000000000^3421 ≤ 1087817663223^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545813847 5000000000 1087817663223 5000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5528075593/10000000000 : ℝ)^4445 ≤ (23146708456813/50000000000000 : ℝ)^3421 := by
    have hnat : (5528075593 : ℕ)^4445*50000000000000^3421 ≤ 23146708456813^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528075593 10000000000 23146708456813 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155553811/10000000000 : ℝ), (1545813847/5000000000 : ℝ), (5528075593/10000000000 : ℝ)] ![(15975114903347/50000000000000 : ℝ), (1087817663223/5000000000000 : ℝ), (23146708456813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155553811/10000000000 : ℝ)|^4445 ≤ (15975114903347/50000000000000 : ℝ)^3421
        have hw : |(4155553811/10000000000 : ℝ)|=(4155553811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1545813847/5000000000 : ℝ)|^4445 ≤ (1087817663223/5000000000000 : ℝ)^3421
        have hw : |(1545813847/5000000000 : ℝ)|=(1545813847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5528075593/10000000000 : ℝ)|^4445 ≤ (23146708456813/50000000000000 : ℝ)^3421
        have hw : |(5528075593/10000000000 : ℝ)|=(5528075593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s0_4 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1730749281/10000000000 : ℝ)*x 0 + (304192469/625000000 : ℝ)*x 1 + (2956661201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1730749281/10000000000 : ℝ)^4445 ≤ (10238033746627/100000000000000 : ℝ)^3421 := by
    have hnat : (1730749281 : ℕ)^4445*100000000000000^3421 ≤ 10238033746627^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730749281 10000000000 10238033746627 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (304192469/625000000 : ℝ)^4445 ≤ (784673929207/2000000000000 : ℝ)^3421 := by
    have hnat : (304192469 : ℕ)^4445*2000000000000^3421 ≤ 784673929207^3421*625000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304192469 625000000 784673929207 2000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956661201/5000000000 : ℝ)^4445 ≤ (50528269776417/100000000000000 : ℝ)^3421 := by
    have hnat : (2956661201 : ℕ)^4445*100000000000000^3421 ≤ 50528269776417^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956661201 5000000000 50528269776417 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1730749281/10000000000 : ℝ), (304192469/625000000 : ℝ), (2956661201/5000000000 : ℝ)] ![(10238033746627/100000000000000 : ℝ), (784673929207/2000000000000 : ℝ), (50528269776417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1730749281/10000000000 : ℝ)|^4445 ≤ (10238033746627/100000000000000 : ℝ)^3421
        have hw : |(-1730749281/10000000000 : ℝ)|=(1730749281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(304192469/625000000 : ℝ)|^4445 ≤ (784673929207/2000000000000 : ℝ)^3421
        have hw : |(304192469/625000000 : ℝ)|=(304192469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956661201/5000000000 : ℝ)|^4445 ≤ (50528269776417/100000000000000 : ℝ)^3421
        have hw : |(2956661201/5000000000 : ℝ)|=(2956661201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s0_5 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184902693/10000000000 : ℝ)*x 0 + (-1274192101/10000000000 : ℝ)*x 1 + (184791329/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184902693/10000000000 : ℝ)^4445 ≤ (42594603348211/100000000000000 : ℝ)^3421 := by
    have hnat : (5184902693 : ℕ)^4445*100000000000000^3421 ≤ 42594603348211^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184902693 10000000000 42594603348211 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1274192101/10000000000 : ℝ)^4445 ≤ (6877125466787/100000000000000 : ℝ)^3421 := by
    have hnat : (1274192101 : ℕ)^4445*100000000000000^3421 ≤ 6877125466787^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274192101 10000000000 6877125466787 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184791329/312500000 : ℝ)^4445 ≤ (10105654235067/20000000000000 : ℝ)^3421 := by
    have hnat : (184791329 : ℕ)^4445*20000000000000^3421 ≤ 10105654235067^3421*312500000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184791329 312500000 10105654235067 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184902693/10000000000 : ℝ), (-1274192101/10000000000 : ℝ), (184791329/312500000 : ℝ)] ![(42594603348211/100000000000000 : ℝ), (6877125466787/100000000000000 : ℝ), (10105654235067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184902693/10000000000 : ℝ)|^4445 ≤ (42594603348211/100000000000000 : ℝ)^3421
        have hw : |(5184902693/10000000000 : ℝ)|=(5184902693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1274192101/10000000000 : ℝ)|^4445 ≤ (6877125466787/100000000000000 : ℝ)^3421
        have hw : |(-1274192101/10000000000 : ℝ)|=(1274192101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184791329/312500000 : ℝ)|^4445 ≤ (10105654235067/20000000000000 : ℝ)^3421
        have hw : |(184791329/312500000 : ℝ)|=(184791329/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s0_6 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184902637/10000000000 : ℝ)*x 0 + (2956661191/5000000000 : ℝ)*x 1 + (-39818513/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184902637/10000000000 : ℝ)^4445 ≤ (42594602750459/100000000000000 : ℝ)^3421 := by
    have hnat : (5184902637 : ℕ)^4445*100000000000000^3421 ≤ 42594602750459^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184902637 10000000000 42594602750459 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2956661191/5000000000 : ℝ)^4445 ≤ (50528269554367/100000000000000 : ℝ)^3421 := by
    have hnat : (2956661191 : ℕ)^4445*100000000000000^3421 ≤ 50528269554367^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956661191 5000000000 50528269554367 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39818513/312500000 : ℝ)^4445 ≤ (1375425535163/20000000000000 : ℝ)^3421 := by
    have hnat : (39818513 : ℕ)^4445*20000000000000^3421 ≤ 1375425535163^3421*312500000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39818513 312500000 1375425535163 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184902637/10000000000 : ℝ), (2956661191/5000000000 : ℝ), (-39818513/312500000 : ℝ)] ![(42594602750459/100000000000000 : ℝ), (50528269554367/100000000000000 : ℝ), (1375425535163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184902637/10000000000 : ℝ)|^4445 ≤ (42594602750459/100000000000000 : ℝ)^3421
        have hw : |(5184902637/10000000000 : ℝ)|=(5184902637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2956661191/5000000000 : ℝ)|^4445 ≤ (50528269554367/100000000000000 : ℝ)^3421
        have hw : |(2956661191/5000000000 : ℝ)|=(2956661191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39818513/312500000 : ℝ)|^4445 ≤ (1375425535163/20000000000000 : ℝ)^3421
        have hw : |(-39818513/312500000 : ℝ)|=(39818513/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s0_7 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164069911/10000000000 : ℝ)*x 0 + (170797101/312500000 : ℝ)*x 1 + (1578223923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164069911/10000000000 : ℝ)^4445 ≤ (1281413255583/4000000000000 : ℝ)^3421 := by
    have hnat : (4164069911 : ℕ)^4445*4000000000000^3421 ≤ 1281413255583^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164069911 10000000000 1281413255583 4000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170797101/312500000 : ℝ)^4445 ≤ (912275489661/2000000000000 : ℝ)^3421 := by
    have hnat : (170797101 : ℕ)^4445*2000000000000^3421 ≤ 912275489661^3421*312500000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170797101 312500000 912275489661 2000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1578223923/5000000000 : ℝ)^4445 ≤ (2793861763747/12500000000000 : ℝ)^3421 := by
    have hnat : (1578223923 : ℕ)^4445*12500000000000^3421 ≤ 2793861763747^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578223923 5000000000 2793861763747 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164069911/10000000000 : ℝ), (170797101/312500000 : ℝ), (1578223923/5000000000 : ℝ)] ![(1281413255583/4000000000000 : ℝ), (912275489661/2000000000000 : ℝ), (2793861763747/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164069911/10000000000 : ℝ)|^4445 ≤ (1281413255583/4000000000000 : ℝ)^3421
        have hw : |(4164069911/10000000000 : ℝ)|=(4164069911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170797101/312500000 : ℝ)|^4445 ≤ (912275489661/2000000000000 : ℝ)^3421
        have hw : |(170797101/312500000 : ℝ)|=(170797101/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1578223923/5000000000 : ℝ)|^4445 ≤ (2793861763747/12500000000000 : ℝ)^3421
        have hw : |(1578223923/5000000000 : ℝ)|=(1578223923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1474_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (93/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5197/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4443/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4443 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4443*1^1024 ≤ 0^1024*1^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4443/1024 : ℝ) ≤ (375336802092001871/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4443 ≤ (375336802092001871/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4443*20000000000000000000^1024 ≤ 375336802092001871^1024*5^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 375336802092001871 20000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (375336802092001871/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4443 := by
      have hnat : (1 : ℕ)^1024*1^4443 ≤ 1^4443*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20375336802092001871/20000000000000000000 : ℝ) ≤ (5021471975223821/5000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (20375336802092001871/20000000000000000000 : ℝ)^1024 ≤ (5021471975223821/5000000000000000 : ℝ)^4443 := by
      have hnat : (20375336802092001871 : ℕ)^1024*5000000000000000^4443 ≤ 5021471975223821^4443*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20375336802092001871 20000000000000000000 5021471975223821 5000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021471975223821/5000000000000000 : ℝ)) (X := (20375336802092001871/20000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10375336802092001871/10000000000000000000 : ℝ) ≤ (2521471975223821/2500000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (10375336802092001871/10000000000000000000 : ℝ)^1024 ≤ (2521471975223821/2500000000000000 : ℝ)^4443 := by
      have hnat : (10375336802092001871 : ℕ)^1024*2500000000000000^4443 ≤ 2521471975223821^4443*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10375336802092001871 10000000000000000000 2521471975223821 2500000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2521471975223821/2500000000000000 : ℝ)) (X := (10375336802092001871/10000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(21471975223821/2000000000000000 : ℝ)*(0 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21471975223821/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(375336802092001871/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(21471975223821/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4443/1024 : ℝ) := by
    rw [show (1 : ℝ)+(21471975223821/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5021471975223821/5000000000000000 : ℝ) by norm_num, show 1+(375336802092001871/20000000000000000000 : ℝ)+(0 : ℝ)=(20375336802092001871/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(375336802092001871/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(21471975223821/2000000000000000 : ℝ)*(2/5 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21471975223821/2000000000000000 : ℝ)*(2/5 : ℝ)=(2521471975223821/2500000000000000 : ℝ) by norm_num, show 1+2*(375336802092001871/20000000000000000000 : ℝ)=(10375336802092001871/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(21471975223821/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21471975223821/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(21471975223821/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21471975223821/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(21471975223821/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21471975223821/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-863445181/5000000000 : ℝ)*X 0 0+(5942692609/10000000000 : ℝ)*X 0 1+(967745919/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5486294137/10000000000 : ℝ)*X 1 0+(-2348785141/10000000000 : ℝ)*X 1 1+(2419364757/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((54862943/100000000 : ℝ)*X 2 0+(1209682337/2500000000 : ℝ)*X 2 1+(-1174392569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4155553811/10000000000 : ℝ)*X 0 0+(1545813847/5000000000 : ℝ)*X 0 1+(5528075593/10000000000 : ℝ)*X 0 2+(4155553811/10000000000 : ℝ)*X 1 0+(1545813847/5000000000 : ℝ)*X 1 1+(5528075593/10000000000 : ℝ)*X 1 2+(4155553811/10000000000 : ℝ)*X 2 0+(1545813847/5000000000 : ℝ)*X 2 1+(5528075593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1730749281/10000000000 : ℝ)*X 0 0+(304192469/625000000 : ℝ)*X 0 1+(2956661201/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5184902693/10000000000 : ℝ)*X 1 0+(-1274192101/10000000000 : ℝ)*X 1 1+(184791329/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5184902637/10000000000 : ℝ)*X 2 0+(2956661191/5000000000 : ℝ)*X 2 1+(-39818513/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4164069911/10000000000 : ℝ)*X 0 0+(170797101/312500000 : ℝ)*X 0 1+(1578223923/5000000000 : ℝ)*X 0 2+(4164069911/10000000000 : ℝ)*X 1 0+(170797101/312500000 : ℝ)*X 1 1+(1578223923/5000000000 : ℝ)*X 1 2+(4164069911/10000000000 : ℝ)*X 2 0+(170797101/312500000 : ℝ)*X 2 1+(1578223923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82101710556982520992821/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86976963/100000000000000 : ℝ)*(base1) + (12016711/3125000000000 : ℝ)*(base19) + (82289459/20000000000000 : ℝ)*(base23) + (31065873/100000000000000 : ℝ)*(upper3) + (401433/1000000000000 : ℝ)*(upper5) + (658131964920333/100000000000000 : ℝ)*(major0) + (658131964920333/100000000000000 : ℝ)*(major1) + (658131964920333/100000000000000 : ℝ)*(major2) + (226457099049723/25000000000000 : ℝ)*(sp0) + (452914511295221/50000000000000 : ℝ)*(sp1) + (9058289956779/1000000000000 : ℝ)*(sp2) + (82086793578253/20000000000000 : ℝ)*(sp3) + (219580653/20000000000000 : ℝ)*(sp4) + (10327819/2500000000000 : ℝ)*(sp7) + (410434467980989/100000000000000 : ℝ)*(f.failure) + (181165881425039/20000000000000 : ℝ)*(f.sum) + (91746281747607/100000000000000000000000000000 : ℝ)*base66 + (3080739505252393/200000000000000000000000000000 : ℝ)*base67 + (909375833852393/200000000000000000000000000000 : ℝ)*base69 + (1188215343052393/200000000000000000000000000000 : ℝ)*base71 + (464893018052393/100000000000000000000000000000 : ℝ)*base73 + (1297445050252393/200000000000000000000000000000 : ℝ)*base75 + (206389053852393/200000000000000000000000000000 : ℝ)*base77 + (631451622852393/200000000000000000000000000000 : ℝ)*base79 + (120957881647607/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2402349/1250000000000000000000 : ℝ)*base90 + (2402349/1250000000000000000000 : ℝ)*base92 + (2402349/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (644618932708631817/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (612808633/100000000000000 : ℝ)*(base19) + (595772927/100000000000000 : ℝ)*(base23) + (8546251/10000000000000 : ℝ)*(base32) + (11692091/12500000000000 : ℝ)*(upper3) + (46242317/100000000000000 : ℝ)*(upper5) + (173609664992343/25000000000000 : ℝ)*(major0) + (173609664992343/25000000000000 : ℝ)*(major1) + (173609664992343/25000000000000 : ℝ)*(major2) + (1572143879/100000000000000 : ℝ)*(sp1) + (1456666159/100000000000000 : ℝ)*(sp2) + (38232024859321/4000000000000 : ℝ)*(sp4) + (477899218265257/50000000000000 : ℝ)*(sp5) + (955798569043939/100000000000000 : ℝ)*(sp6) + (216538263522007/50000000000000 : ℝ)*(sp7) + (108269153126631/25000000000000 : ℝ)*(f.failure) + (38232024859321/4000000000000 : ℝ)*(f.sum) + (7975482977603/25000000000000000000000000000 : ℝ)*base65 + (205120766197397/50000000000000000000000000000 : ℝ)*base68 + (206279681502603/50000000000000000000000000000 : ℝ)*base69 + (245258042747397/50000000000000000000000000000 : ℝ)*base72 + (17227758672397/25000000000000000000000000000 : ℝ)*base74 + (292327225897397/50000000000000000000000000000 : ℝ)*base76 + (78684496352603/50000000000000000000000000000 : ℝ)*base77 + (83143637697397/50000000000000000000000000000 : ℝ)*base80 + (102761119252603/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (745929/312500000000000000000 : ℝ)*base89 + (745929/312500000000000000000 : ℝ)*base91 + (745929/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1474_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (93/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5197/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1474_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1474_s1_0 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-945476237/5000000000 : ℝ)*x 0 + (5597114633/10000000000 : ℝ)*x 1 + (5079024619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (945476237/5000000000 : ℝ)^4445 ≤ (11486060473251/100000000000000 : ℝ)^3421 := by
    have hnat : (945476237 : ℕ)^4445*100000000000000^3421 ≤ 11486060473251^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945476237 5000000000 11486060473251 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5597114633/10000000000 : ℝ)^4445 ≤ (23523011165267/50000000000000 : ℝ)^3421 := by
    have hnat : (5597114633 : ℕ)^4445*50000000000000^3421 ≤ 23523011165267^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597114633 10000000000 23523011165267 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5079024619/10000000000 : ℝ)^4445 ≤ (41467917183301/100000000000000 : ℝ)^3421 := by
    have hnat : (5079024619 : ℕ)^4445*100000000000000^3421 ≤ 41467917183301^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079024619 10000000000 41467917183301 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-945476237/5000000000 : ℝ), (5597114633/10000000000 : ℝ), (5079024619/10000000000 : ℝ)] ![(11486060473251/100000000000000 : ℝ), (23523011165267/50000000000000 : ℝ), (41467917183301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-945476237/5000000000 : ℝ)|^4445 ≤ (11486060473251/100000000000000 : ℝ)^3421
        have hw : |(-945476237/5000000000 : ℝ)|=(945476237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5597114633/10000000000 : ℝ)|^4445 ≤ (23523011165267/50000000000000 : ℝ)^3421
        have hw : |(5597114633/10000000000 : ℝ)|=(5597114633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5079024619/10000000000 : ℝ)|^4445 ≤ (41467917183301/100000000000000 : ℝ)^3421
        have hw : |(5079024619/10000000000 : ℝ)|=(5079024619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s1_1 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393701433/10000000000 : ℝ)*x 0 + (-2165130271/10000000000 : ℝ)*x 1 + (2539511583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393701433/10000000000 : ℝ)^4445 ≤ (448366576409/1000000000000 : ℝ)^3421 := by
    have hnat : (5393701433 : ℕ)^4445*1000000000000^3421 ≤ 448366576409^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393701433 10000000000 448366576409 1000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2165130271/10000000000 : ℝ)^4445 ≤ (1711930071191/12500000000000 : ℝ)^3421 := by
    have hnat : (2165130271 : ℕ)^4445*12500000000000^3421 ≤ 1711930071191^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165130271 10000000000 1711930071191 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539511583/5000000000 : ℝ)^4445 ≤ (41467901769271/100000000000000 : ℝ)^3421 := by
    have hnat : (2539511583 : ℕ)^4445*100000000000000^3421 ≤ 41467901769271^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539511583 5000000000 41467901769271 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393701433/10000000000 : ℝ), (-2165130271/10000000000 : ℝ), (2539511583/5000000000 : ℝ)] ![(448366576409/1000000000000 : ℝ), (1711930071191/12500000000000 : ℝ), (41467901769271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393701433/10000000000 : ℝ)|^4445 ≤ (448366576409/1000000000000 : ℝ)^3421
        have hw : |(5393701433/10000000000 : ℝ)|=(5393701433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2165130271/10000000000 : ℝ)|^4445 ≤ (1711930071191/12500000000000 : ℝ)^3421
        have hw : |(-2165130271/10000000000 : ℝ)|=(2165130271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539511583/5000000000 : ℝ)|^4445 ≤ (41467901769271/100000000000000 : ℝ)^3421
        have hw : |(2539511583/5000000000 : ℝ)|=(2539511583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s1_2 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696850351/5000000000 : ℝ)*x 0 + (5079023961/10000000000 : ℝ)*x 1 + (-1082565103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696850351/5000000000 : ℝ)^4445 ≤ (896732994907/2000000000000 : ℝ)^3421 := by
    have hnat : (2696850351 : ℕ)^4445*2000000000000^3421 ≤ 896732994907^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696850351 5000000000 896732994907 2000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079023961/10000000000 : ℝ)^4445 ≤ (20733955101481/50000000000000 : ℝ)^3421 := by
    have hnat : (5079023961 : ℕ)^4445*50000000000000^3421 ≤ 20733955101481^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079023961 10000000000 20733955101481 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082565103/5000000000 : ℝ)^4445 ≤ (13695440035303/100000000000000 : ℝ)^3421 := by
    have hnat : (1082565103 : ℕ)^4445*100000000000000^3421 ≤ 13695440035303^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082565103 5000000000 13695440035303 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696850351/5000000000 : ℝ), (5079023961/10000000000 : ℝ), (-1082565103/5000000000 : ℝ)] ![(896732994907/2000000000000 : ℝ), (20733955101481/50000000000000 : ℝ), (13695440035303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696850351/5000000000 : ℝ)|^4445 ≤ (896732994907/2000000000000 : ℝ)^3421
        have hw : |(2696850351/5000000000 : ℝ)|=(2696850351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079023961/10000000000 : ℝ)|^4445 ≤ (20733955101481/50000000000000 : ℝ)^3421
        have hw : |(5079023961/10000000000 : ℝ)|=(5079023961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082565103/5000000000 : ℝ)|^4445 ≤ (13695440035303/100000000000000 : ℝ)^3421
        have hw : |(-1082565103/5000000000 : ℝ)|=(1082565103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s1_3 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2131722777/5000000000 : ℝ)*x 0 + (3725126711/10000000000 : ℝ)*x 1 + (4868554591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131722777/5000000000 : ℝ)^4445 ≤ (1321289085363/4000000000000 : ℝ)^3421 := by
    have hnat : (2131722777 : ℕ)^4445*4000000000000^3421 ≤ 1321289085363^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131722777 5000000000 1321289085363 4000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3725126711/10000000000 : ℝ)^4445 ≤ (27718625735961/100000000000000 : ℝ)^3421 := by
    have hnat : (3725126711 : ℕ)^4445*100000000000000^3421 ≤ 27718625735961^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3725126711 10000000000 27718625735961 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4868554591/10000000000 : ℝ)^4445 ≤ (39249147112367/100000000000000 : ℝ)^3421 := by
    have hnat : (4868554591 : ℕ)^4445*100000000000000^3421 ≤ 39249147112367^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4868554591 10000000000 39249147112367 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2131722777/5000000000 : ℝ), (3725126711/10000000000 : ℝ), (4868554591/10000000000 : ℝ)] ![(1321289085363/4000000000000 : ℝ), (27718625735961/100000000000000 : ℝ), (39249147112367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2131722777/5000000000 : ℝ)|^4445 ≤ (1321289085363/4000000000000 : ℝ)^3421
        have hw : |(2131722777/5000000000 : ℝ)|=(2131722777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3725126711/10000000000 : ℝ)|^4445 ≤ (27718625735961/100000000000000 : ℝ)^3421
        have hw : |(3725126711/10000000000 : ℝ)|=(3725126711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4868554591/10000000000 : ℝ)|^4445 ≤ (39249147112367/100000000000000 : ℝ)^3421
        have hw : |(4868554591/10000000000 : ℝ)|=(4868554591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s1_4 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1891336533/10000000000 : ℝ)*x 0 + (2542568771/5000000000 : ℝ)*x 1 + (2795448613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1891336533/10000000000 : ℝ)^4445 ≤ (11489091713251/100000000000000 : ℝ)^3421 := by
    have hnat : (1891336533 : ℕ)^4445*100000000000000^3421 ≤ 11489091713251^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891336533 10000000000 11489091713251 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542568771/5000000000 : ℝ)^4445 ≤ (41532777299349/100000000000000 : ℝ)^3421 := by
    have hnat : (2542568771 : ℕ)^4445*100000000000000^3421 ≤ 41532777299349^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542568771 5000000000 41532777299349 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2795448613/5000000000 : ℝ)^4445 ≤ (5872266372043/12500000000000 : ℝ)^3421 := by
    have hnat : (2795448613 : ℕ)^4445*12500000000000^3421 ≤ 5872266372043^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795448613 5000000000 5872266372043 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1891336533/10000000000 : ℝ), (2542568771/5000000000 : ℝ), (2795448613/5000000000 : ℝ)] ![(11489091713251/100000000000000 : ℝ), (41532777299349/100000000000000 : ℝ), (5872266372043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1891336533/10000000000 : ℝ)|^4445 ≤ (11489091713251/100000000000000 : ℝ)^3421
        have hw : |(-1891336533/10000000000 : ℝ)|=(1891336533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542568771/5000000000 : ℝ)|^4445 ≤ (41532777299349/100000000000000 : ℝ)^3421
        have hw : |(2542568771/5000000000 : ℝ)|=(2542568771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2795448613/5000000000 : ℝ)|^4445 ≤ (5872266372043/12500000000000 : ℝ)^3421
        have hw : |(2795448613/5000000000 : ℝ)|=(2795448613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s1_5 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628949487/5000000000 : ℝ)*x 0 + (-1653256481/10000000000 : ℝ)*x 1 + (5590897251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628949487/5000000000 : ℝ)^4445 ≤ (43375411845197/100000000000000 : ℝ)^3421 := by
    have hnat : (2628949487 : ℕ)^4445*100000000000000^3421 ≤ 43375411845197^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628949487 5000000000 43375411845197 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1653256481/10000000000 : ℝ)^4445 ≤ (1205807111847/12500000000000 : ℝ)^3421 := by
    have hnat : (1653256481 : ℕ)^4445*12500000000000^3421 ≤ 1205807111847^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653256481 10000000000 1205807111847 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5590897251/10000000000 : ℝ)^4445 ≤ (5872266406161/12500000000000 : ℝ)^3421 := by
    have hnat : (5590897251 : ℕ)^4445*12500000000000^3421 ≤ 5872266406161^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590897251 10000000000 5872266406161 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628949487/5000000000 : ℝ), (-1653256481/10000000000 : ℝ), (5590897251/10000000000 : ℝ)] ![(43375411845197/100000000000000 : ℝ), (1205807111847/12500000000000 : ℝ), (5872266406161/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628949487/5000000000 : ℝ)|^4445 ≤ (43375411845197/100000000000000 : ℝ)^3421
        have hw : |(2628949487/5000000000 : ℝ)|=(2628949487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1653256481/10000000000 : ℝ)|^4445 ≤ (1205807111847/12500000000000 : ℝ)^3421
        have hw : |(-1653256481/10000000000 : ℝ)|=(1653256481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5590897251/10000000000 : ℝ)|^4445 ≤ (5872266406161/12500000000000 : ℝ)^3421
        have hw : |(5590897251/10000000000 : ℝ)|=(5590897251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s1_6 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257899021/10000000000 : ℝ)*x 0 + (2795448607/5000000000 : ℝ)*x 1 + (-826628233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257899021/10000000000 : ℝ)^4445 ≤ (21687706174493/50000000000000 : ℝ)^3421 := by
    have hnat : (5257899021 : ℕ)^4445*50000000000000^3421 ≤ 21687706174493^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257899021 10000000000 21687706174493 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2795448607/5000000000 : ℝ)^4445 ≤ (46978130845331/100000000000000 : ℝ)^3421 := by
    have hnat : (2795448607 : ℕ)^4445*100000000000000^3421 ≤ 46978130845331^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795448607 5000000000 46978130845331 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826628233/5000000000 : ℝ)^4445 ≤ (37681471801/390625000000 : ℝ)^3421 := by
    have hnat : (826628233 : ℕ)^4445*390625000000^3421 ≤ 37681471801^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826628233 5000000000 37681471801 390625000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257899021/10000000000 : ℝ), (2795448607/5000000000 : ℝ), (-826628233/5000000000 : ℝ)] ![(21687706174493/50000000000000 : ℝ), (46978130845331/100000000000000 : ℝ), (37681471801/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257899021/10000000000 : ℝ)|^4445 ≤ (21687706174493/50000000000000 : ℝ)^3421
        have hw : |(5257899021/10000000000 : ℝ)|=(5257899021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2795448607/5000000000 : ℝ)|^4445 ≤ (46978130845331/100000000000000 : ℝ)^3421
        have hw : |(2795448607/5000000000 : ℝ)|=(2795448607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-826628233/5000000000 : ℝ)|^4445 ≤ (37681471801/390625000000 : ℝ)^3421
        have hw : |(-826628233/5000000000 : ℝ)|=(826628233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s1_7 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4264292439/10000000000 : ℝ)*x 0 + (1213765523/2500000000 : ℝ)*x 1 + (3738849391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4264292439/10000000000 : ℝ)^4445 ≤ (4130094111941/12500000000000 : ℝ)^3421 := by
    have hnat : (4264292439 : ℕ)^4445*12500000000000^3421 ≤ 4130094111941^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4264292439 10000000000 4130094111941 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1213765523/2500000000 : ℝ)^4445 ≤ (4888484190427/12500000000000 : ℝ)^3421 := by
    have hnat : (1213765523 : ℕ)^4445*12500000000000^3421 ≤ 4888484190427^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213765523 2500000000 4888484190427 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3738849391/10000000000 : ℝ)^4445 ≤ (27851373569353/100000000000000 : ℝ)^3421 := by
    have hnat : (3738849391 : ℕ)^4445*100000000000000^3421 ≤ 27851373569353^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3738849391 10000000000 27851373569353 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4264292439/10000000000 : ℝ), (1213765523/2500000000 : ℝ), (3738849391/10000000000 : ℝ)] ![(4130094111941/12500000000000 : ℝ), (4888484190427/12500000000000 : ℝ), (27851373569353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4264292439/10000000000 : ℝ)|^4445 ≤ (4130094111941/12500000000000 : ℝ)^3421
        have hw : |(4264292439/10000000000 : ℝ)|=(4264292439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1213765523/2500000000 : ℝ)|^4445 ≤ (4888484190427/12500000000000 : ℝ)^3421
        have hw : |(1213765523/2500000000 : ℝ)|=(1213765523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3738849391/10000000000 : ℝ)|^4445 ≤ (27851373569353/100000000000000 : ℝ)^3421
        have hw : |(3738849391/10000000000 : ℝ)|=(3738849391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1474_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5197/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (93/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (977/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1173/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5197/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (93/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5197/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (93/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5197/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (93/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5197/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (93/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5197/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (93/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5197/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (93/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (93/4000 : ℝ) ^ (4443/1024 : ℝ) ≤ (4084098193107/50000000000000000000 : ℝ) := by
    have hpowers : (93/4000 : ℝ)^4443 ≤ (4084098193107/50000000000000000000 : ℝ)^1024 := by
      have hnat : (93 : ℕ)^4443*50000000000000000000^1024 ≤ 4084098193107^1024*4000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93 4000 4084098193107 50000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93/4000 : ℝ)) (X := (4084098193107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5197/20000 : ℝ) ^ (4443/1024 : ℝ) ≤ (36096877220911991/12500000000000000000 : ℝ) := by
    have hpowers : (5197/20000 : ℝ)^4443 ≤ (36096877220911991/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5197 : ℕ)^4443*12500000000000000000^1024 ≤ 36096877220911991^1024*20000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5197 20000 36096877220911991 12500000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5197/20000 : ℝ)) (X := (36096877220911991/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000004084098193107/25000000000000000000 : ℝ) ≤ (10000000376512833/10000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (25000004084098193107/25000000000000000000 : ℝ)^1024 ≤ (10000000376512833/10000000000000000 : ℝ)^4443 := by
      have hnat : (25000004084098193107 : ℕ)^1024*10000000000000000^4443 ≤ 10000000376512833^4443*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000004084098193107 25000000000000000000 10000000376512833 10000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000376512833/10000000000000000 : ℝ)) (X := (25000004084098193107/25000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50144391592981841071/50000000000000000000 : ℝ) ≤ (10006648344912291/10000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (50144391592981841071/50000000000000000000 : ℝ)^1024 ≤ (10006648344912291/10000000000000000 : ℝ)^4443 := by
      have hnat : (50144391592981841071 : ℕ)^1024*10000000000000000^4443 ≤ 10006648344912291^4443*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50144391592981841071 50000000000000000000 10006648344912291 10000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006648344912291/10000000000000000 : ℝ)) (X := (50144391592981841071/50000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6286096877220911991/6250000000000000000 : ℝ) ≤ (10013296313311749/10000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (6286096877220911991/6250000000000000000 : ℝ)^1024 ≤ (10013296313311749/10000000000000000 : ℝ)^4443 := by
      have hnat : (6286096877220911991 : ℕ)^1024*10000000000000000^4443 ≤ 10013296313311749^4443*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6286096877220911991 6250000000000000000 10013296313311749 10000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013296313311749/10000000000000000 : ℝ)) (X := (6286096877220911991/6250000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4084098193107/50000000000000000000 : ℝ) ≤ ((5914227396380903727/5915000000000000000 : ℝ)+2*(3323984199729/1183000000000000 : ℝ)*(93/4000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (5914227396380903727/5915000000000000000 : ℝ)+2*(3323984199729/1183000000000000 : ℝ)*(93/4000 : ℝ)=(10000000376512833/10000000000000000 : ℝ) by norm_num, show 1+2*(4084098193107/50000000000000000000 : ℝ)=(25000004084098193107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36096877220911991/12500000000000000000 : ℝ)+(4084098193107/50000000000000000000 : ℝ) ≤ ((5914227396380903727/5915000000000000000 : ℝ)+(3323984199729/1183000000000000 : ℝ)*((5197/20000 : ℝ)+(93/4000 : ℝ)))^(4443/1024 : ℝ) := by
    rw [show (5914227396380903727/5915000000000000000 : ℝ)+(3323984199729/1183000000000000 : ℝ)*((5197/20000 : ℝ)+(93/4000 : ℝ))=(10006648344912291/10000000000000000 : ℝ) by norm_num, show 1+(36096877220911991/12500000000000000000 : ℝ)+(4084098193107/50000000000000000000 : ℝ)=(50144391592981841071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36096877220911991/12500000000000000000 : ℝ) ≤ ((5914227396380903727/5915000000000000000 : ℝ)+2*(3323984199729/1183000000000000 : ℝ)*(5197/20000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (5914227396380903727/5915000000000000000 : ℝ)+2*(3323984199729/1183000000000000 : ℝ)*(5197/20000 : ℝ)=(10013296313311749/10000000000000000 : ℝ) by norm_num, show 1+2*(36096877220911991/12500000000000000000 : ℝ)=(6286096877220911991/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5914227396380903727/5915000000000000000 : ℝ)*(X 1 0+X 2 0)+(3323984199729/1183000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (93/4000 : ℝ)) (hi := (5197/20000 : ℝ)) (c := (5914227396380903727/5915000000000000000 : ℝ)) (alpha := (3323984199729/1183000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5914227396380903727/5915000000000000000 : ℝ)*(X 0 1+X 2 1)+(3323984199729/1183000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (93/4000 : ℝ)) (hi := (5197/20000 : ℝ)) (c := (5914227396380903727/5915000000000000000 : ℝ)) (alpha := (3323984199729/1183000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5914227396380903727/5915000000000000000 : ℝ)*(X 0 2+X 1 2)+(3323984199729/1183000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (93/4000 : ℝ)) (hi := (5197/20000 : ℝ)) (c := (5914227396380903727/5915000000000000000 : ℝ)) (alpha := (3323984199729/1183000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-945476237/5000000000 : ℝ)*X 0 0+(5597114633/10000000000 : ℝ)*X 0 1+(5079024619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5393701433/10000000000 : ℝ)*X 1 0+(-2165130271/10000000000 : ℝ)*X 1 1+(2539511583/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2696850351/5000000000 : ℝ)*X 2 0+(5079023961/10000000000 : ℝ)*X 2 1+(-1082565103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2131722777/5000000000 : ℝ)*X 0 0+(3725126711/10000000000 : ℝ)*X 0 1+(4868554591/10000000000 : ℝ)*X 0 2+(2131722777/5000000000 : ℝ)*X 1 0+(3725126711/10000000000 : ℝ)*X 1 1+(4868554591/10000000000 : ℝ)*X 1 2+(2131722777/5000000000 : ℝ)*X 2 0+(3725126711/10000000000 : ℝ)*X 2 1+(4868554591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1891336533/10000000000 : ℝ)*X 0 0+(2542568771/5000000000 : ℝ)*X 0 1+(2795448613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628949487/5000000000 : ℝ)*X 1 0+(-1653256481/10000000000 : ℝ)*X 1 1+(5590897251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257899021/10000000000 : ℝ)*X 2 0+(2795448607/5000000000 : ℝ)*X 2 1+(-826628233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4264292439/10000000000 : ℝ)*X 0 0+(1213765523/2500000000 : ℝ)*X 0 1+(3738849391/10000000000 : ℝ)*X 0 2+(4264292439/10000000000 : ℝ)*X 1 0+(1213765523/2500000000 : ℝ)*X 1 1+(3738849391/10000000000 : ℝ)*X 1 2+(4264292439/10000000000 : ℝ)*X 2 0+(1213765523/2500000000 : ℝ)*X 2 1+(3738849391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (226050364382295399436916967/21125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201231021/100000000000000 : ℝ)*(base1) + (971755011/50000000000000 : ℝ)*(base19) + (840957897/50000000000000 : ℝ)*(base23) + (108041049/50000000000000 : ℝ)*(upper3) + (94953809/50000000000000 : ℝ)*(upper5) + (701188344518949/50000000000000 : ℝ)*(major0) + (701188344518949/50000000000000 : ℝ)*(major1) + (701188344518949/50000000000000 : ℝ)*(major2) + (482543581105713/25000000000000 : ℝ)*(sp0) + (482544791710717/25000000000000 : ℝ)*(sp1) + (386035885687419/20000000000000 : ℝ)*(sp2) + (218641876745293/25000000000000 : ℝ)*(sp3) + (6987161059/100000000000000 : ℝ)*(sp4) + (2101411871/50000000000000 : ℝ)*(sp7) + (174914382207187/20000000000000 : ℝ)*(f.failure) + (1930181110352889/100000000000000 : ℝ)*(f.sum) + (809425631433/264062500000000000000000000 : ℝ)*base65 + (107875659840403989/42250000000000000000000000000000 : ℝ)*base67 + (121012601703096011/42250000000000000000000000000000 : ℝ)*base70 + (10110930504596011/42250000000000000000000000000000 : ℝ)*base72 + (33257746180603/4225000000000000000000000000 : ℝ)*base73 + (332320246166596011/42250000000000000000000000000000 : ℝ)*base76 + (207607086251903989/42250000000000000000000000000000 : ℝ)*base77 + (17018001951846011/42250000000000000000000000000000 : ℝ)*base80 + (5050302945497/4225000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (704067/250000000000000000000 : ℝ)*base90 + (704067/250000000000000000000 : ℝ)*base92 + (704067/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53332385531364415774764273/10562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (481487251/50000000000000 : ℝ)*(base19) + (20852989/2000000000000 : ℝ)*(base23) + (4224843/3125000000000 : ℝ)*(upper3) + (23778017/100000000000000 : ℝ)*(lower4) + (51990043/50000000000000 : ℝ)*(upper5) + (359138752112277/25000000000000 : ℝ)*(major0) + (359138752112277/25000000000000 : ℝ)*(major1) + (359138752112277/25000000000000 : ℝ)*(major2) + (2875056999/50000000000000 : ℝ)*(sp1) + (6399720761/100000000000000 : ℝ)*(sp2) + (247152890458747/12500000000000 : ℝ)*(sp4) + (1977216410581477/100000000000000 : ℝ)*(sp5) + (988607840649883/50000000000000 : ℝ)*(sp6) + (447943362460451/50000000000000 : ℝ)*(sp7) + (447943362460451/50000000000000 : ℝ)*(f.failure) + (247152890458747/12500000000000 : ℝ)*(f.sum) + (40666914944221/7393750000000000000000000000 : ℝ)*base66 + (752899721404578621/147875000000000000000000000000000 : ℝ)*base68 + (245211024730328621/147875000000000000000000000000000 : ℝ)*base70 + (1524931101319828621/147875000000000000000000000000000 : ℝ)*base72 + (96762266011309/29575000000000000000000000000 : ℝ)*base74 + (1176204049589953621/147875000000000000000000000000000 : ℝ)*base76 + (1122850041120828621/147875000000000000000000000000000 : ℝ)*base78 + (557788603941953621/147875000000000000000000000000000 : ℝ)*base80 + (17623377926933/14787500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1875309/625000000000000000000 : ℝ)*base89 + (1875309/625000000000000000000 : ℝ)*base91 + (1875309/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1474_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5197/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (93/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (977/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1173/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1474_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1474_s2_0 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-96009487/500000000 : ℝ)*x 0 + (1367789989/2500000000 : ℝ)*x 1 + (648264723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96009487/500000000 : ℝ)^4445 ≤ (11717344775073/100000000000000 : ℝ)^3421 := by
    have hnat : (96009487 : ℕ)^4445*100000000000000^3421 ≤ 11717344775073^3421*500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96009487 500000000 11717344775073 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367789989/2500000000 : ℝ)^4445 ≤ (1827003254513/4000000000000 : ℝ)^3421 := by
    have hnat : (1367789989 : ℕ)^4445*4000000000000^3421 ≤ 1827003254513^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367789989 2500000000 1827003254513 4000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648264723/1250000000 : ℝ)^4445 ≤ (42607573847513/100000000000000 : ℝ)^3421 := by
    have hnat : (648264723 : ℕ)^4445*100000000000000^3421 ≤ 42607573847513^3421*1250000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648264723 1250000000 42607573847513 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96009487/500000000 : ℝ), (1367789989/2500000000 : ℝ), (648264723/1250000000 : ℝ)] ![(11717344775073/100000000000000 : ℝ), (1827003254513/4000000000000 : ℝ), (42607573847513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96009487/500000000 : ℝ)|^4445 ≤ (11717344775073/100000000000000 : ℝ)^3421
        have hw : |(-96009487/500000000 : ℝ)|=(96009487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367789989/2500000000 : ℝ)|^4445 ≤ (1827003254513/4000000000000 : ℝ)^3421
        have hw : |(1367789989/2500000000 : ℝ)|=(1367789989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648264723/1250000000 : ℝ)|^4445 ≤ (42607573847513/100000000000000 : ℝ)^3421
        have hw : |(648264723/1250000000 : ℝ)|=(648264723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s2_1 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340524529/2500000000 : ℝ)*x 0 + (-2067289947/10000000000 : ℝ)*x 1 + (5186119061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340524529/2500000000 : ℝ)^4445 ≤ (8899121826781/20000000000000 : ℝ)^3421 := by
    have hnat : (1340524529 : ℕ)^4445*20000000000000^3421 ≤ 8899121826781^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340524529 2500000000 8899121826781 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067289947/10000000000 : ℝ)^4445 ≤ (12896803371937/100000000000000 : ℝ)^3421 := by
    have hnat : (2067289947 : ℕ)^4445*100000000000000^3421 ≤ 12896803371937^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067289947 10000000000 12896803371937 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5186119061/10000000000 : ℝ)^4445 ≤ (42607587479339/100000000000000 : ℝ)^3421 := by
    have hnat : (5186119061 : ℕ)^4445*100000000000000^3421 ≤ 42607587479339^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186119061 10000000000 42607587479339 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340524529/2500000000 : ℝ), (-2067289947/10000000000 : ℝ), (5186119061/10000000000 : ℝ)] ![(8899121826781/20000000000000 : ℝ), (12896803371937/100000000000000 : ℝ), (42607587479339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340524529/2500000000 : ℝ)|^4445 ≤ (8899121826781/20000000000000 : ℝ)^3421
        have hw : |(1340524529/2500000000 : ℝ)|=(1340524529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2067289947/10000000000 : ℝ)|^4445 ≤ (12896803371937/100000000000000 : ℝ)^3421
        have hw : |(-2067289947/10000000000 : ℝ)|=(2067289947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5186119061/10000000000 : ℝ)|^4445 ≤ (42607587479339/100000000000000 : ℝ)^3421
        have hw : |(5186119061/10000000000 : ℝ)|=(5186119061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s2_2 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681049427/5000000000 : ℝ)*x 0 + (1037223699/2000000000 : ℝ)*x 1 + (-2067289711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681049427/5000000000 : ℝ)^4445 ≤ (22247808545527/50000000000000 : ℝ)^3421 := by
    have hnat : (2681049427 : ℕ)^4445*50000000000000^3421 ≤ 22247808545527^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681049427 5000000000 22247808545527 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037223699/2000000000 : ℝ)^4445 ≤ (8521516287471/20000000000000 : ℝ)^3421 := by
    have hnat : (1037223699 : ℕ)^4445*20000000000000^3421 ≤ 8521516287471^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037223699 2000000000 8521516287471 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067289711/10000000000 : ℝ)^4445 ≤ (12896801458953/100000000000000 : ℝ)^3421 := by
    have hnat : (2067289711 : ℕ)^4445*100000000000000^3421 ≤ 12896801458953^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067289711 10000000000 12896801458953 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681049427/5000000000 : ℝ), (1037223699/2000000000 : ℝ), (-2067289711/10000000000 : ℝ)] ![(22247808545527/50000000000000 : ℝ), (8521516287471/20000000000000 : ℝ), (12896801458953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681049427/5000000000 : ℝ)|^4445 ≤ (22247808545527/50000000000000 : ℝ)^3421
        have hw : |(2681049427/5000000000 : ℝ)|=(2681049427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037223699/2000000000 : ℝ)|^4445 ≤ (8521516287471/20000000000000 : ℝ)^3421
        have hw : |(1037223699/2000000000 : ℝ)|=(1037223699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067289711/10000000000 : ℝ)|^4445 ≤ (12896801458953/100000000000000 : ℝ)^3421
        have hw : |(-2067289711/10000000000 : ℝ)|=(2067289711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s2_3 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142142037/5000000000 : ℝ)*x 0 + (1989924907/5000000000 : ℝ)*x 1 + (4608937169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142142037/5000000000 : ℝ)^4445 ≤ (33242159747433/100000000000000 : ℝ)^3421 := by
    have hnat : (2142142037 : ℕ)^4445*100000000000000^3421 ≤ 33242159747433^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142142037 5000000000 33242159747433 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989924907/5000000000 : ℝ)^4445 ≤ (30206173007187/100000000000000 : ℝ)^3421 := by
    have hnat : (1989924907 : ℕ)^4445*100000000000000^3421 ≤ 30206173007187^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989924907 5000000000 30206173007187 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4608937169/10000000000 : ℝ)^4445 ≤ (36551667232701/100000000000000 : ℝ)^3421 := by
    have hnat : (4608937169 : ℕ)^4445*100000000000000^3421 ≤ 36551667232701^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4608937169 10000000000 36551667232701 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142142037/5000000000 : ℝ), (1989924907/5000000000 : ℝ), (4608937169/10000000000 : ℝ)] ![(33242159747433/100000000000000 : ℝ), (30206173007187/100000000000000 : ℝ), (36551667232701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142142037/5000000000 : ℝ)|^4445 ≤ (33242159747433/100000000000000 : ℝ)^3421
        have hw : |(2142142037/5000000000 : ℝ)|=(2142142037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1989924907/5000000000 : ℝ)|^4445 ≤ (30206173007187/100000000000000 : ℝ)^3421
        have hw : |(1989924907/5000000000 : ℝ)|=(1989924907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4608937169/10000000000 : ℝ)|^4445 ≤ (36551667232701/100000000000000 : ℝ)^3421
        have hw : |(4608937169/10000000000 : ℝ)|=(4608937169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s2_4 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-480063379/2500000000 : ℝ)*x 0 + (1296994591/2500000000 : ℝ)*x 1 + (2734641063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480063379/2500000000 : ℝ)^4445 ≤ (5858925220209/50000000000000 : ℝ)^3421 := by
    have hnat : (480063379 : ℕ)^4445*50000000000000^3421 ≤ 5858925220209^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480063379 2500000000 5858925220209 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296994591/2500000000 : ℝ)^4445 ≤ (1705097455501/4000000000000 : ℝ)^3421 := by
    have hnat : (1296994591 : ℕ)^4445*4000000000000^3421 ≤ 1705097455501^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296994591 2500000000 1705097455501 4000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734641063/5000000000 : ℝ)^4445 ≤ (178338723307/390625000000 : ℝ)^3421 := by
    have hnat : (2734641063 : ℕ)^4445*390625000000^3421 ≤ 178338723307^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734641063 5000000000 178338723307 390625000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480063379/2500000000 : ℝ), (1296994591/2500000000 : ℝ), (2734641063/5000000000 : ℝ)] ![(5858925220209/50000000000000 : ℝ), (1705097455501/4000000000000 : ℝ), (178338723307/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480063379/2500000000 : ℝ)|^4445 ≤ (5858925220209/50000000000000 : ℝ)^3421
        have hw : |(-480063379/2500000000 : ℝ)|=(480063379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296994591/2500000000 : ℝ)|^4445 ≤ (1705097455501/4000000000000 : ℝ)^3421
        have hw : |(1296994591/2500000000 : ℝ)|=(1296994591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734641063/5000000000 : ℝ)|^4445 ≤ (178338723307/390625000000 : ℝ)^3421
        have hw : |(2734641063/5000000000 : ℝ)|=(2734641063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s2_5 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264384979/500000000 : ℝ)*x 0 + (-223015851/1250000000 : ℝ)*x 1 + (5469282171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264384979/500000000 : ℝ)^4445 ≤ (43695112049583/100000000000000 : ℝ)^3421 := by
    have hnat : (264384979 : ℕ)^4445*100000000000000^3421 ≤ 43695112049583^3421*500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264384979 500000000 43695112049583 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223015851/1250000000 : ℝ)^4445 ≤ (10650174277999/100000000000000 : ℝ)^3421 := by
    have hnat : (223015851 : ℕ)^4445*100000000000000^3421 ≤ 10650174277999^3421*1250000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223015851 1250000000 10650174277999 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469282171/10000000000 : ℝ)^4445 ≤ (45654713654667/100000000000000 : ℝ)^3421 := by
    have hnat : (5469282171 : ℕ)^4445*100000000000000^3421 ≤ 45654713654667^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469282171 10000000000 45654713654667 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264384979/500000000 : ℝ), (-223015851/1250000000 : ℝ), (5469282171/10000000000 : ℝ)] ![(43695112049583/100000000000000 : ℝ), (10650174277999/100000000000000 : ℝ), (45654713654667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264384979/500000000 : ℝ)|^4445 ≤ (43695112049583/100000000000000 : ℝ)^3421
        have hw : |(264384979/500000000 : ℝ)|=(264384979/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223015851/1250000000 : ℝ)|^4445 ≤ (10650174277999/100000000000000 : ℝ)^3421
        have hw : |(-223015851/1250000000 : ℝ)|=(223015851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469282171/10000000000 : ℝ)|^4445 ≤ (45654713654667/100000000000000 : ℝ)^3421
        have hw : |(5469282171/10000000000 : ℝ)|=(5469282171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s2_6 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057539977/2000000000 : ℝ)*x 0 + (5469282201/10000000000 : ℝ)*x 1 + (-356825269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057539977/2000000000 : ℝ)^4445 ≤ (21847557662191/50000000000000 : ℝ)^3421 := by
    have hnat : (1057539977 : ℕ)^4445*50000000000000^3421 ≤ 21847557662191^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057539977 2000000000 21847557662191 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469282201/10000000000 : ℝ)^4445 ≤ (45654713980051/100000000000000 : ℝ)^3421 := by
    have hnat : (5469282201 : ℕ)^4445*100000000000000^3421 ≤ 45654713980051^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469282201 10000000000 45654713980051 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356825269/2000000000 : ℝ)^4445 ≤ (10650170686873/100000000000000 : ℝ)^3421 := by
    have hnat : (356825269 : ℕ)^4445*100000000000000^3421 ≤ 10650170686873^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356825269 2000000000 10650170686873 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057539977/2000000000 : ℝ), (5469282201/10000000000 : ℝ), (-356825269/2000000000 : ℝ)] ![(21847557662191/50000000000000 : ℝ), (45654713980051/100000000000000 : ℝ), (10650170686873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057539977/2000000000 : ℝ)|^4445 ≤ (21847557662191/50000000000000 : ℝ)^3421
        have hw : |(1057539977/2000000000 : ℝ)|=(1057539977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469282201/10000000000 : ℝ)|^4445 ≤ (45654713980051/100000000000000 : ℝ)^3421
        have hw : |(5469282201/10000000000 : ℝ)|=(5469282201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356825269/2000000000 : ℝ)|^4445 ≤ (10650170686873/100000000000000 : ℝ)^3421
        have hw : |(-356825269/2000000000 : ℝ)|=(356825269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s2_7 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284426301/10000000000 : ℝ)*x 0 + (287801941/625000000 : ℝ)*x 1 + (3983993699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284426301/10000000000 : ℝ)^4445 ≤ (16621796815473/50000000000000 : ℝ)^3421 := by
    have hnat : (4284426301 : ℕ)^4445*50000000000000^3421 ≤ 16621796815473^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284426301 10000000000 16621796815473 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287801941/625000000 : ℝ)^4445 ≤ (36509361612257/100000000000000 : ℝ)^3421 := by
    have hnat : (287801941 : ℕ)^4445*100000000000000^3421 ≤ 36509361612257^3421*625000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287801941 625000000 36509361612257 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983993699/10000000000 : ℝ)^4445 ≤ (30247044741163/100000000000000 : ℝ)^3421 := by
    have hnat : (3983993699 : ℕ)^4445*100000000000000^3421 ≤ 30247044741163^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983993699 10000000000 30247044741163 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284426301/10000000000 : ℝ), (287801941/625000000 : ℝ), (3983993699/10000000000 : ℝ)] ![(16621796815473/50000000000000 : ℝ), (36509361612257/100000000000000 : ℝ), (30247044741163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284426301/10000000000 : ℝ)|^4445 ≤ (16621796815473/50000000000000 : ℝ)^3421
        have hw : |(4284426301/10000000000 : ℝ)|=(4284426301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(287801941/625000000 : ℝ)|^4445 ≤ (36509361612257/100000000000000 : ℝ)^3421
        have hw : |(287801941/625000000 : ℝ)|=(287801941/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983993699/10000000000 : ℝ)|^4445 ≤ (30247044741163/100000000000000 : ℝ)^3421
        have hw : |(3983993699/10000000000 : ℝ)|=(3983993699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1474_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1173/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (977/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10131/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16159/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1173/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (977/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1173/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (977/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1173/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (977/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1173/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (977/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1173/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (977/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1173/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (977/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (977/12500 : ℝ) ^ (4443/1024 : ℝ) ≤ (393320877764267/25000000000000000000 : ℝ) := by
    have hpowers : (977/12500 : ℝ)^4443 ≤ (393320877764267/25000000000000000000 : ℝ)^1024 := by
      have hnat : (977 : ℕ)^4443*25000000000000000000^1024 ≤ 393320877764267^1024*12500^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        977 12500 393320877764267 25000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (977/12500 : ℝ)) (X := (393320877764267/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1173/6250 : ℝ) ^ (4443/1024 : ℝ) ≤ (70381282844353631/100000000000000000000 : ℝ) := by
    have hpowers : (1173/6250 : ℝ)^4443 ≤ (70381282844353631/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1173 : ℕ)^4443*100000000000000000000^1024 ≤ 70381282844353631^1024*6250^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1173 6250 70381282844353631 100000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1173/6250 : ℝ)) (X := (70381282844353631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500393320877764267/12500000000000000000 : ℝ) ≤ (1250009064949421/1250000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (12500393320877764267/12500000000000000000 : ℝ)^1024 ≤ (1250009064949421/1250000000000000 : ℝ)^4443 := by
      have hnat : (12500393320877764267 : ℕ)^1024*1250000000000000^4443 ≤ 1250009064949421^4443*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500393320877764267 12500000000000000000 1250009064949421 1250000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250009064949421/1250000000000000 : ℝ)) (X := (12500393320877764267/12500000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100071954566355410699/100000000000000000000 : ℝ) ≤ (2500414478311803/2500000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (100071954566355410699/100000000000000000000 : ℝ)^1024 ≤ (2500414478311803/2500000000000000 : ℝ)^4443 := by
      have hnat : (100071954566355410699 : ℕ)^1024*2500000000000000^4443 ≤ 2500414478311803^4443*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100071954566355410699 100000000000000000000 2500414478311803 2500000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500414478311803/2500000000000000 : ℝ)) (X := (100071954566355410699/100000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50070381282844353631/50000000000000000000 : ℝ) ≤ (625202706681191/625000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (50070381282844353631/50000000000000000000 : ℝ)^1024 ≤ (625202706681191/625000000000000 : ℝ)^4443 := by
      have hnat : (50070381282844353631 : ℕ)^1024*625000000000000^4443 ≤ 625202706681191^4443*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50070381282844353631 50000000000000000000 625202706681191 625000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625202706681191/625000000000000 : ℝ)) (X := (50070381282844353631/50000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(393320877764267/25000000000000000000 : ℝ) ≤ ((427718794379073613/427812500000000000 : ℝ)+2*(396348412961/273800000000000 : ℝ)*(977/12500 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (427718794379073613/427812500000000000 : ℝ)+2*(396348412961/273800000000000 : ℝ)*(977/12500 : ℝ)=(1250009064949421/1250000000000000 : ℝ) by norm_num, show 1+2*(393320877764267/25000000000000000000 : ℝ)=(12500393320877764267/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(70381282844353631/100000000000000000000 : ℝ)+(393320877764267/25000000000000000000 : ℝ) ≤ ((427718794379073613/427812500000000000 : ℝ)+(396348412961/273800000000000 : ℝ)*((1173/6250 : ℝ)+(977/12500 : ℝ)))^(4443/1024 : ℝ) := by
    rw [show (427718794379073613/427812500000000000 : ℝ)+(396348412961/273800000000000 : ℝ)*((1173/6250 : ℝ)+(977/12500 : ℝ))=(2500414478311803/2500000000000000 : ℝ) by norm_num, show 1+(70381282844353631/100000000000000000000 : ℝ)+(393320877764267/25000000000000000000 : ℝ)=(100071954566355410699/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(70381282844353631/100000000000000000000 : ℝ) ≤ ((427718794379073613/427812500000000000 : ℝ)+2*(396348412961/273800000000000 : ℝ)*(1173/6250 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (427718794379073613/427812500000000000 : ℝ)+2*(396348412961/273800000000000 : ℝ)*(1173/6250 : ℝ)=(625202706681191/625000000000000 : ℝ) by norm_num, show 1+2*(70381282844353631/100000000000000000000 : ℝ)=(50070381282844353631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (427718794379073613/427812500000000000 : ℝ)*(X 1 0+X 2 0)+(396348412961/273800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (977/12500 : ℝ)) (hi := (1173/6250 : ℝ)) (c := (427718794379073613/427812500000000000 : ℝ)) (alpha := (396348412961/273800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (427718794379073613/427812500000000000 : ℝ)*(X 0 1+X 2 1)+(396348412961/273800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (977/12500 : ℝ)) (hi := (1173/6250 : ℝ)) (c := (427718794379073613/427812500000000000 : ℝ)) (alpha := (396348412961/273800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (427718794379073613/427812500000000000 : ℝ)*(X 0 2+X 1 2)+(396348412961/273800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (977/12500 : ℝ)) (hi := (1173/6250 : ℝ)) (c := (427718794379073613/427812500000000000 : ℝ)) (alpha := (396348412961/273800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-96009487/500000000 : ℝ)*X 0 0+(1367789989/2500000000 : ℝ)*X 0 1+(648264723/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340524529/2500000000 : ℝ)*X 1 0+(-2067289947/10000000000 : ℝ)*X 1 1+(5186119061/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681049427/5000000000 : ℝ)*X 2 0+(1037223699/2000000000 : ℝ)*X 2 1+(-2067289711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2142142037/5000000000 : ℝ)*X 0 0+(1989924907/5000000000 : ℝ)*X 0 1+(4608937169/10000000000 : ℝ)*X 0 2+(2142142037/5000000000 : ℝ)*X 1 0+(1989924907/5000000000 : ℝ)*X 1 1+(4608937169/10000000000 : ℝ)*X 1 2+(2142142037/5000000000 : ℝ)*X 2 0+(1989924907/5000000000 : ℝ)*X 2 1+(4608937169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-480063379/2500000000 : ℝ)*X 0 0+(1296994591/2500000000 : ℝ)*X 0 1+(2734641063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264384979/500000000 : ℝ)*X 1 0+(-223015851/1250000000 : ℝ)*X 1 1+(5469282171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057539977/2000000000 : ℝ)*X 2 0+(5469282201/10000000000 : ℝ)*X 2 1+(-356825269/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4284426301/10000000000 : ℝ)*X 0 0+(287801941/625000000 : ℝ)*X 0 1+(3983993699/10000000000 : ℝ)*X 0 2+(4284426301/10000000000 : ℝ)*X 1 0+(287801941/625000000 : ℝ)*X 1 1+(3983993699/10000000000 : ℝ)*X 1 2+(4284426301/10000000000 : ℝ)*X 2 0+(287801941/625000000 : ℝ)*X 2 1+(3983993699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153004655487346617987680889/21390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1112790081/100000000000000 : ℝ)*(base19) + (19424339/1562500000000 : ℝ)*(base23) + (712611/500000000000 : ℝ)*(upper3) + (37801709/20000000000000 : ℝ)*(upper4) + (30820579/20000000000000 : ℝ)*(upper5) + (1274483227222529/50000000000000 : ℝ)*(major0) + (1274483227222529/50000000000000 : ℝ)*(major1) + (1274483227222529/50000000000000 : ℝ)*(major2) + (877069238126851/25000000000000 : ℝ)*(sp0) + (877076386468727/25000000000000 : ℝ)*(sp1) + (877076353876823/25000000000000 : ℝ)*(sp2) + (1589614327203473/100000000000000 : ℝ)*(sp3) + (1856634849/6250000000000 : ℝ)*(sp4) + (584229609/5000000000000 : ℝ)*(sp7) + (397406502948913/25000000000000 : ℝ)*(f.failure) + (877076664666247/25000000000000 : ℝ)*(f.sum) + (41431450041541/6845000000000000000000000000 : ℝ)*base66 + (486259758077270179/42781250000000000000000000000000 : ℝ)*base67 + (197396258559301429/42781250000000000000000000000000 : ℝ)*base69 + (175752777847520179/42781250000000000000000000000000 : ℝ)*base71 + (6306889368601/6845000000000000000000000000 : ℝ)*base74 + (81296285493926429/42781250000000000000000000000000 : ℝ)*base75 + (239780478323770179/42781250000000000000000000000000 : ℝ)*base77 + (874553560106645179/42781250000000000000000000000000 : ℝ)*base79 + (2865623724789/1711250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4766033/312500000000000000000 : ℝ)*base90 + (4766033/312500000000000000000 : ℝ)*base92 + (4766033/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80854258666343521589431623/21390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151368891/100000000000000 : ℝ)*(base19) + (484351689/100000000000000 : ℝ)*(base23) + (50953891/100000000000000 : ℝ)*(upper3) + (11807229/50000000000000 : ℝ)*(lower4) + (110662589/100000000000000 : ℝ)*(upper5) + (161425195444659/6250000000000 : ℝ)*(major0) + (161425195444659/6250000000000 : ℝ)*(major1) + (161425195444659/6250000000000 : ℝ)*(major2) + (593722009/50000000000000 : ℝ)*(sp1) + (56847537/800000000000 : ℝ)*(sp2) + (888719591398587/25000000000000 : ℝ)*(sp4) + (3554877026781439/100000000000000 : ℝ)*(sp5) + (1777435387650267/50000000000000 : ℝ)*(sp6) + (805363881319163/50000000000000 : ℝ)*(sp7) + (805363881319163/50000000000000 : ℝ)*(f.failure) + (888719591398587/25000000000000 : ℝ)*(f.sum) + (1095261401441/3422500000000000000000000000 : ℝ)*base65 + (27539939490262191/5347656250000000000000000000000 : ℝ)*base68 + (9774458160102507/10695312500000000000000000000000 : ℝ)*base70 + (30842577904852507/10695312500000000000000000000000 : ℝ)*base72 + (1844542683209/3422500000000000000000000000 : ℝ)*base74 + (202944163190689389/21390625000000000000000000000000 : ℝ)*base76 + (73620593984602507/10695312500000000000000000000000 : ℝ)*base78 + (120200742729064389/21390625000000000000000000000000 : ℝ)*base80 + (5368798603587/6845000000000000000000000000 : ℝ)*base81 + (5253717/625000000000000000000 : ℝ)*base89 + (5253717/625000000000000000000 : ℝ)*base91 + (5253717/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1474_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1173/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (977/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1474_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1474_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1474_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1474_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1474_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1474_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

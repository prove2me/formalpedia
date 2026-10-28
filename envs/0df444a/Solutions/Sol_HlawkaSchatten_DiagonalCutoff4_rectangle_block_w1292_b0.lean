-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1292_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:26:25.349416+00:00
-- url     : https://prove2.me/submissions/b47c0267-f797-4780-8523-529958b391ef

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
theorem support_rectangle_w1292_s0_0 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-183907749/1000000000 : ℝ)*x 0 + (48150347/80000000 : ℝ)*x 1 + (4798840081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183907749/1000000000 : ℝ)^1063 ≤ (10747644598931/100000000000000 : ℝ)^807 := by
    have hnat : (183907749 : ℕ)^1063*100000000000000^807 ≤ 10747644598931^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183907749 1000000000 10747644598931 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48150347/80000000 : ℝ)^1063 ≤ (51234732332899/100000000000000 : ℝ)^807 := by
    have hnat : (48150347 : ℕ)^1063*100000000000000^807 ≤ 51234732332899^807*80000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48150347 80000000 51234732332899 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4798840081/10000000000 : ℝ)^1063 ≤ (7603524611313/20000000000000 : ℝ)^807 := by
    have hnat : (4798840081 : ℕ)^1063*20000000000000^807 ≤ 7603524611313^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4798840081 10000000000 7603524611313 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-183907749/1000000000 : ℝ), (48150347/80000000 : ℝ), (4798840081/10000000000 : ℝ)] ![(10747644598931/100000000000000 : ℝ), (51234732332899/100000000000000 : ℝ), (7603524611313/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-183907749/1000000000 : ℝ)|^1063 ≤ (10747644598931/100000000000000 : ℝ)^807
        have hw : |(-183907749/1000000000 : ℝ)|=(183907749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48150347/80000000 : ℝ)|^1063 ≤ (51234732332899/100000000000000 : ℝ)^807
        have hw : |(48150347/80000000 : ℝ)|=(48150347/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4798840081/10000000000 : ℝ)|^1063 ≤ (7603524611313/20000000000000 : ℝ)^807
        have hw : |(4798840081/10000000000 : ℝ)|=(4798840081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s0_1 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1376854699/2500000000 : ℝ)*x 0 + (-2535053023/10000000000 : ℝ)*x 1 + (599855013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1376854699/2500000000 : ℝ)^1063 ≤ (22789802059189/50000000000000 : ℝ)^807 := by
    have hnat : (1376854699 : ℕ)^1063*50000000000000^807 ≤ 22789802059189^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376854699 2500000000 22789802059189 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2535053023/10000000000 : ℝ)^1063 ≤ (16402772567527/100000000000000 : ℝ)^807 := by
    have hnat : (2535053023 : ℕ)^1063*100000000000000^807 ≤ 16402772567527^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2535053023 10000000000 16402772567527 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599855013/1250000000 : ℝ)^1063 ≤ (38017623296579/100000000000000 : ℝ)^807 := by
    have hnat : (599855013 : ℕ)^1063*100000000000000^807 ≤ 38017623296579^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599855013 1250000000 38017623296579 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1376854699/2500000000 : ℝ), (-2535053023/10000000000 : ℝ), (599855013/1250000000 : ℝ)] ![(22789802059189/50000000000000 : ℝ), (16402772567527/100000000000000 : ℝ), (38017623296579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1376854699/2500000000 : ℝ)|^1063 ≤ (22789802059189/50000000000000 : ℝ)^807
        have hw : |(1376854699/2500000000 : ℝ)|=(1376854699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2535053023/10000000000 : ℝ)|^1063 ≤ (16402772567527/100000000000000 : ℝ)^807
        have hw : |(-2535053023/10000000000 : ℝ)|=(2535053023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599855013/1250000000 : ℝ)|^1063 ≤ (38017623296579/100000000000000 : ℝ)^807
        have hw : |(599855013/1250000000 : ℝ)|=(599855013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s0_2 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5507418469/10000000000 : ℝ)*x 0 + (599855069/1250000000 : ℝ)*x 1 + (-1267526447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5507418469/10000000000 : ℝ)^1063 ≤ (45579600553621/100000000000000 : ℝ)^807 := by
    have hnat : (5507418469 : ℕ)^1063*100000000000000^807 ≤ 45579600553621^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507418469 10000000000 45579600553621 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (599855069/1250000000 : ℝ)^1063 ≤ (3801762797163/10000000000000 : ℝ)^807 := by
    have hnat : (599855069 : ℕ)^1063*10000000000000^807 ≤ 3801762797163^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599855069 1250000000 3801762797163 10000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1267526447/5000000000 : ℝ)^1063 ≤ (16402771468067/100000000000000 : ℝ)^807 := by
    have hnat : (1267526447 : ℕ)^1063*100000000000000^807 ≤ 16402771468067^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267526447 5000000000 16402771468067 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5507418469/10000000000 : ℝ), (599855069/1250000000 : ℝ), (-1267526447/5000000000 : ℝ)] ![(45579600553621/100000000000000 : ℝ), (3801762797163/10000000000000 : ℝ), (16402771468067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5507418469/10000000000 : ℝ)|^1063 ≤ (45579600553621/100000000000000 : ℝ)^807
        have hw : |(5507418469/10000000000 : ℝ)|=(5507418469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(599855069/1250000000 : ℝ)|^1063 ≤ (3801762797163/10000000000000 : ℝ)^807
        have hw : |(599855069/1250000000 : ℝ)|=(599855069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1267526447/5000000000 : ℝ)|^1063 ≤ (16402771468067/100000000000000 : ℝ)^807
        have hw : |(-1267526447/5000000000 : ℝ)|=(1267526447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s0_3 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4186332031/10000000000 : ℝ)*x 0 + (1554716901/5000000000 : ℝ)*x 1 + (1123345149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186332031/10000000000 : ℝ)^1063 ≤ (254073934643/800000000000 : ℝ)^807 := by
    have hnat : (4186332031 : ℕ)^1063*800000000000^807 ≤ 254073934643^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186332031 10000000000 254073934643 800000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1554716901/5000000000 : ℝ)^1063 ≤ (21465821177471/100000000000000 : ℝ)^807 := by
    have hnat : (1554716901 : ℕ)^1063*100000000000000^807 ≤ 21465821177471^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554716901 5000000000 21465821177471 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123345149/2000000000 : ℝ)^1063 ≤ (9354987395993/20000000000000 : ℝ)^807 := by
    have hnat : (1123345149 : ℕ)^1063*20000000000000^807 ≤ 9354987395993^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123345149 2000000000 9354987395993 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186332031/10000000000 : ℝ), (1554716901/5000000000 : ℝ), (1123345149/2000000000 : ℝ)] ![(254073934643/800000000000 : ℝ), (21465821177471/100000000000000 : ℝ), (9354987395993/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186332031/10000000000 : ℝ)|^1063 ≤ (254073934643/800000000000 : ℝ)^807
        have hw : |(4186332031/10000000000 : ℝ)|=(4186332031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1554716901/5000000000 : ℝ)|^1063 ≤ (21465821177471/100000000000000 : ℝ)^807
        have hw : |(1554716901/5000000000 : ℝ)|=(1554716901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123345149/2000000000 : ℝ)|^1063 ≤ (9354987395993/20000000000000 : ℝ)^807
        have hw : |(1123345149/2000000000 : ℝ)|=(1123345149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s0_4 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1843801147/10000000000 : ℝ)*x 0 + (4830326837/10000000000 : ℝ)*x 1 + (5986186989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1843801147/10000000000 : ℝ)^1063 ≤ (5392010852323/50000000000000 : ℝ)^807 := by
    have hnat : (1843801147 : ℕ)^1063*50000000000000^807 ≤ 5392010852323^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843801147 10000000000 5392010852323 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4830326837/10000000000 : ℝ)^1063 ≤ (599164701121/1562500000000 : ℝ)^807 := by
    have hnat : (4830326837 : ℕ)^1063*1562500000000^807 ≤ 599164701121^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4830326837 10000000000 599164701121 1562500000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5986186989/10000000000 : ℝ)^1063 ≤ (50869437411417/100000000000000 : ℝ)^807 := by
    have hnat : (5986186989 : ℕ)^1063*100000000000000^807 ≤ 50869437411417^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5986186989 10000000000 50869437411417 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1843801147/10000000000 : ℝ), (4830326837/10000000000 : ℝ), (5986186989/10000000000 : ℝ)] ![(5392010852323/50000000000000 : ℝ), (599164701121/1562500000000 : ℝ), (50869437411417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1843801147/10000000000 : ℝ)|^1063 ≤ (5392010852323/50000000000000 : ℝ)^807
        have hw : |(-1843801147/10000000000 : ℝ)|=(1843801147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4830326837/10000000000 : ℝ)|^1063 ≤ (599164701121/1562500000000 : ℝ)^807
        have hw : |(4830326837/10000000000 : ℝ)|=(4830326837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5986186989/10000000000 : ℝ)|^1063 ≤ (50869437411417/100000000000000 : ℝ)^807
        have hw : |(5986186989/10000000000 : ℝ)|=(5986186989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s0_5 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (646911857/1250000000 : ℝ)*x 0 + (-1347703861/10000000000 : ℝ)*x 1 + (5986189617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646911857/1250000000 : ℝ)^1063 ≤ (41994108267829/100000000000000 : ℝ)^807 := by
    have hnat : (646911857 : ℕ)^1063*100000000000000^807 ≤ 41994108267829^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646911857 1250000000 41994108267829 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347703861/10000000000 : ℝ)^1063 ≤ (356821244541/5000000000000 : ℝ)^807 := by
    have hnat : (1347703861 : ℕ)^1063*5000000000000^807 ≤ 356821244541^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347703861 10000000000 356821244541 5000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5986189617/10000000000 : ℝ)^1063 ≤ (5086946682797/10000000000000 : ℝ)^807 := by
    have hnat : (5986189617 : ℕ)^1063*10000000000000^807 ≤ 5086946682797^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5986189617 10000000000 5086946682797 10000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646911857/1250000000 : ℝ), (-1347703861/10000000000 : ℝ), (5986189617/10000000000 : ℝ)] ![(41994108267829/100000000000000 : ℝ), (356821244541/5000000000000 : ℝ), (5086946682797/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646911857/1250000000 : ℝ)|^1063 ≤ (41994108267829/100000000000000 : ℝ)^807
        have hw : |(646911857/1250000000 : ℝ)|=(646911857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1347703861/10000000000 : ℝ)|^1063 ≤ (356821244541/5000000000000 : ℝ)^807
        have hw : |(-1347703861/10000000000 : ℝ)|=(1347703861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5986189617/10000000000 : ℝ)|^1063 ≤ (5086946682797/10000000000000 : ℝ)^807
        have hw : |(5986189617/10000000000 : ℝ)|=(5986189617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s0_6 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5175296149/10000000000 : ℝ)*x 0 + (5986187381/10000000000 : ℝ)*x 1 + (-1347705469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175296149/10000000000 : ℝ)^1063 ≤ (2099706104397/5000000000000 : ℝ)^807 := by
    have hnat : (5175296149 : ℕ)^1063*5000000000000^807 ≤ 2099706104397^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175296149 10000000000 2099706104397 5000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5986187381/10000000000 : ℝ)^1063 ≤ (25434720899637/50000000000000 : ℝ)^807 := by
    have hnat : (5986187381 : ℕ)^1063*50000000000000^807 ≤ 25434720899637^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5986187381 10000000000 25434720899637 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347705469/10000000000 : ℝ)^1063 ≤ (7136436106667/100000000000000 : ℝ)^807 := by
    have hnat : (1347705469 : ℕ)^1063*100000000000000^807 ≤ 7136436106667^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347705469 10000000000 7136436106667 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175296149/10000000000 : ℝ), (5986187381/10000000000 : ℝ), (-1347705469/10000000000 : ℝ)] ![(2099706104397/5000000000000 : ℝ), (25434720899637/50000000000000 : ℝ), (7136436106667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175296149/10000000000 : ℝ)|^1063 ≤ (2099706104397/5000000000000 : ℝ)^807
        have hw : |(5175296149/10000000000 : ℝ)|=(5175296149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5986187381/10000000000 : ℝ)|^1063 ≤ (25434720899637/50000000000000 : ℝ)^807
        have hw : |(5986187381/10000000000 : ℝ)|=(5986187381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1347705469/10000000000 : ℝ)|^1063 ≤ (7136436106667/100000000000000 : ℝ)^807
        have hw : |(-1347705469/10000000000 : ℝ)|=(1347705469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s0_7 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (419604473/1000000000 : ℝ)*x 0 + (34700133/62500000 : ℝ)*x 1 + (3176439903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419604473/1000000000 : ℝ)^1063 ≤ (6371267319311/20000000000000 : ℝ)^807 := by
    have hnat : (419604473 : ℕ)^1063*20000000000000^807 ≤ 6371267319311^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419604473 1000000000 6371267319311 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34700133/62500000 : ℝ)^1063 ≤ (46066456959921/100000000000000 : ℝ)^807 := by
    have hnat : (34700133 : ℕ)^1063*100000000000000^807 ≤ 46066456959921^807*62500000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34700133 62500000 46066456959921 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3176439903/10000000000 : ℝ)^1063 ≤ (22077206428047/100000000000000 : ℝ)^807 := by
    have hnat : (3176439903 : ℕ)^1063*100000000000000^807 ≤ 22077206428047^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3176439903 10000000000 22077206428047 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419604473/1000000000 : ℝ), (34700133/62500000 : ℝ), (3176439903/10000000000 : ℝ)] ![(6371267319311/20000000000000 : ℝ), (46066456959921/100000000000000 : ℝ), (22077206428047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419604473/1000000000 : ℝ)|^1063 ≤ (6371267319311/20000000000000 : ℝ)^807
        have hw : |(419604473/1000000000 : ℝ)|=(419604473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34700133/62500000 : ℝ)|^1063 ≤ (46066456959921/100000000000000 : ℝ)^807
        have hw : |(34700133/62500000 : ℝ)|=(34700133/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3176439903/10000000000 : ℝ)|^1063 ≤ (22077206428047/100000000000000 : ℝ)^807
        have hw : |(3176439903/10000000000 : ℝ)|=(3176439903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1292_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (129/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5447/20000 : ℝ)*pair X 0 0 := by
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
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (4251/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4251 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4251*1^1024 ≤ 0^1024*1^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4251/1024 : ℝ) ≤ (1114230159920125449/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4251 ≤ (1114230159920125449/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4251*50000000000000000000^1024 ≤ 1114230159920125449^1024*5^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1114230159920125449 50000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1114230159920125449/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4251 := by
      have hnat : (1 : ℕ)^1024*1^4251 ≤ 1^4251*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51114230159920125449/50000000000000000000 : ℝ) ≤ (10053231955276633/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (51114230159920125449/50000000000000000000 : ℝ)^1024 ≤ (10053231955276633/10000000000000000 : ℝ)^4251 := by
      have hnat : (51114230159920125449 : ℕ)^1024*10000000000000000^4251 ≤ 10053231955276633^4251*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51114230159920125449 50000000000000000000 10053231955276633 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10053231955276633/10000000000000000 : ℝ)) (X := (51114230159920125449/50000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26114230159920125449/25000000000000000000 : ℝ) ≤ (5053231955276633/5000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (26114230159920125449/25000000000000000000 : ℝ)^1024 ≤ (5053231955276633/5000000000000000 : ℝ)^4251 := by
      have hnat : (26114230159920125449 : ℕ)^1024*5000000000000000^4251 ≤ 5053231955276633^4251*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26114230159920125449 25000000000000000000 5053231955276633 5000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5053231955276633/5000000000000000 : ℝ)) (X := (26114230159920125449/25000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(53231955276633/4000000000000000 : ℝ)*(0 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(53231955276633/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1114230159920125449/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(53231955276633/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4251/1024 : ℝ) := by
    rw [show (1 : ℝ)+(53231955276633/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10053231955276633/10000000000000000 : ℝ) by norm_num, show 1+(1114230159920125449/50000000000000000000 : ℝ)+(0 : ℝ)=(51114230159920125449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1114230159920125449/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(53231955276633/4000000000000000 : ℝ)*(2/5 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(53231955276633/4000000000000000 : ℝ)*(2/5 : ℝ)=(5053231955276633/5000000000000000 : ℝ) by norm_num, show 1+2*(1114230159920125449/50000000000000000000 : ℝ)=(26114230159920125449/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(53231955276633/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (53231955276633/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(53231955276633/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (53231955276633/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(53231955276633/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (53231955276633/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-183907749/1000000000 : ℝ)*X 0 0+(48150347/80000000 : ℝ)*X 0 1+(4798840081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1376854699/2500000000 : ℝ)*X 1 0+(-2535053023/10000000000 : ℝ)*X 1 1+(599855013/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5507418469/10000000000 : ℝ)*X 2 0+(599855069/1250000000 : ℝ)*X 2 1+(-1267526447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4186332031/10000000000 : ℝ)*X 0 0+(1554716901/5000000000 : ℝ)*X 0 1+(1123345149/2000000000 : ℝ)*X 0 2+(4186332031/10000000000 : ℝ)*X 1 0+(1554716901/5000000000 : ℝ)*X 1 1+(1123345149/2000000000 : ℝ)*X 1 2+(4186332031/10000000000 : ℝ)*X 2 0+(1554716901/5000000000 : ℝ)*X 2 1+(1123345149/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1843801147/10000000000 : ℝ)*X 0 0+(4830326837/10000000000 : ℝ)*X 0 1+(5986186989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646911857/1250000000 : ℝ)*X 1 0+(-1347703861/10000000000 : ℝ)*X 1 1+(5986189617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175296149/10000000000 : ℝ)*X 2 0+(5986187381/10000000000 : ℝ)*X 2 1+(-1347705469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((419604473/1000000000 : ℝ)*X 0 0+(34700133/62500000 : ℝ)*X 0 1+(3176439903/10000000000 : ℝ)*X 0 2+(419604473/1000000000 : ℝ)*X 1 0+(34700133/62500000 : ℝ)*X 1 1+(3176439903/10000000000 : ℝ)*X 1 2+(419604473/1000000000 : ℝ)*X 2 0+(34700133/62500000 : ℝ)*X 2 1+(3176439903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3317502486844954449/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (32916581/25000000000000 : ℝ)*(base1) + (338661339/20000000000000 : ℝ)*(base19) + (1644636731/100000000000000 : ℝ)*(base23) + (90810887/50000000000000 : ℝ)*(upper3) + (7907889/4000000000000 : ℝ)*(upper5) + (609277797536309/100000000000000 : ℝ)*(major0) + (609277797536309/100000000000000 : ℝ)*(major1) + (609277797536309/100000000000000 : ℝ)*(major2) + (163941712698229/20000000000000 : ℝ)*(sp0) + (409856055057493/50000000000000 : ℝ)*(sp1) + (16394243175699/2000000000000 : ℝ)*(sp2) + (99709758230221/25000000000000 : ℝ)*(sp3) + (268579843/5000000000000 : ℝ)*(sp4) + (1202948447/50000000000000 : ℝ)*(sp7) + (199420785242051/50000000000000 : ℝ)*(f.failure) + (819713803421681/100000000000000 : ℝ)*(f.sum) + (77184045967597/200000000000000000000000000000 : ℝ)*base65 + (146391363567597/400000000000000000000000000000 : ℝ)*base67 + (2429942902032403/400000000000000000000000000000 : ℝ)*base70 + (1258592395232403/400000000000000000000000000000 : ℝ)*base72 + (988855434767597/200000000000000000000000000000 : ℝ)*base73 + (617287405632403/400000000000000000000000000000 : ℝ)*base76 + (703218272832403/400000000000000000000000000000 : ℝ)*base78 + (23512881567597/400000000000000000000000000000 : ℝ)*base79 + (402514955632403/200000000000000000000000000000 : ℝ)*base82 + (25732809/5000000000000000000000 : ℝ)*base89 + (25732809/5000000000000000000000 : ℝ)*base91 + (25732809/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (492596636608358793707943/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71623069/20000000000000 : ℝ)*(base1) + (266073749/100000000000000 : ℝ)*(base19) + (477023717/100000000000000 : ℝ)*(base23) + (107189/400000000000 : ℝ)*(base59) + (7180769/50000000000000 : ℝ)*(upper3) + (643054095833643/100000000000000 : ℝ)*(major0) + (643054095833643/100000000000000 : ℝ)*(major1) + (643054095833643/100000000000000 : ℝ)*(major2) + (177578553/20000000000000 : ℝ)*(sp1) + (489725261/50000000000000 : ℝ)*(sp3) + (216289117716813/25000000000000 : ℝ)*(sp4) + (865154958785393/100000000000000 : ℝ)*(sp5) + (865155635728189/100000000000000 : ℝ)*(sp6) + (105237664812517/25000000000000 : ℝ)*(sp7) + (84190399363187/20000000000000 : ℝ)*(f.failure) + (865156112751907/100000000000000 : ℝ)*(f.sum) + (1097460057564019/200000000000000000000000000000 : ℝ)*base65 + (192978630035981/400000000000000000000000000000 : ℝ)*base68 + (2400779795635981/400000000000000000000000000000 : ℝ)*base70 + (1832930345164019/400000000000000000000000000000 : ℝ)*base71 + (387112669964019/200000000000000000000000000000 : ℝ)*base73 + (2309870920835981/400000000000000000000000000000 : ℝ)*base76 + (173652419964019/400000000000000000000000000000 : ℝ)*base77 + (3111924935964019/400000000000000000000000000000 : ℝ)*base79 + (406442517435981/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2284633/2000000000000000000000 : ℝ)*base89 + (2284633/2000000000000000000000 : ℝ)*base91 + (2284633/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1292_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (129/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5447/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1292_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1292_s1_0 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1015562813/5000000000 : ℝ)*x 0 + (708163461/1250000000 : ℝ)*x 1 + (502937397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1015562813/5000000000 : ℝ)^1063 ≤ (153124291971/1250000000000 : ℝ)^807 := by
    have hnat : (1015562813 : ℕ)^1063*1250000000000^807 ≤ 153124291971^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015562813 5000000000 153124291971 1250000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708163461/1250000000 : ℝ)^1063 ≤ (47308589842533/100000000000000 : ℝ)^807 := by
    have hnat : (708163461 : ℕ)^1063*100000000000000^807 ≤ 47308589842533^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708163461 1250000000 47308589842533 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502937397/1000000000 : ℝ)^1063 ≤ (20220733391921/50000000000000 : ℝ)^807 := by
    have hnat : (502937397 : ℕ)^1063*50000000000000^807 ≤ 20220733391921^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502937397 1000000000 20220733391921 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1015562813/5000000000 : ℝ), (708163461/1250000000 : ℝ), (502937397/1000000000 : ℝ)] ![(153124291971/1250000000000 : ℝ), (47308589842533/100000000000000 : ℝ), (20220733391921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1015562813/5000000000 : ℝ)|^1063 ≤ (153124291971/1250000000000 : ℝ)^807
        have hw : |(-1015562813/5000000000 : ℝ)|=(1015562813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708163461/1250000000 : ℝ)|^1063 ≤ (47308589842533/100000000000000 : ℝ)^807
        have hw : |(708163461/1250000000 : ℝ)|=(708163461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502937397/1000000000 : ℝ)|^1063 ≤ (20220733391921/50000000000000 : ℝ)^807
        have hw : |(502937397/1000000000 : ℝ)|=(502937397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s1_1 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2705491991/5000000000 : ℝ)*x 0 + (-2371976231/10000000000 : ℝ)*x 1 + (2514686971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705491991/5000000000 : ℝ)^1063 ≤ (1781250451949/4000000000000 : ℝ)^807 := by
    have hnat : (2705491991 : ℕ)^1063*4000000000000^807 ≤ 1781250451949^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705491991 5000000000 1781250451949 4000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2371976231/10000000000 : ℝ)^1063 ≤ (601090888181/4000000000000 : ℝ)^807 := by
    have hnat : (2371976231 : ℕ)^1063*4000000000000^807 ≤ 601090888181^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371976231 10000000000 601090888181 4000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2514686971/5000000000 : ℝ)^1063 ≤ (4044146648727/10000000000000 : ℝ)^807 := by
    have hnat : (2514686971 : ℕ)^1063*10000000000000^807 ≤ 4044146648727^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2514686971 5000000000 4044146648727 10000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705491991/5000000000 : ℝ), (-2371976231/10000000000 : ℝ), (2514686971/5000000000 : ℝ)] ![(1781250451949/4000000000000 : ℝ), (601090888181/4000000000000 : ℝ), (4044146648727/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705491991/5000000000 : ℝ)|^1063 ≤ (1781250451949/4000000000000 : ℝ)^807
        have hw : |(2705491991/5000000000 : ℝ)|=(2705491991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2371976231/10000000000 : ℝ)|^1063 ≤ (601090888181/4000000000000 : ℝ)^807
        have hw : |(-2371976231/10000000000 : ℝ)|=(2371976231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2514686971/5000000000 : ℝ)|^1063 ≤ (4044146648727/10000000000000 : ℝ)^807
        have hw : |(2514686971/5000000000 : ℝ)|=(2514686971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s1_2 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1082196769/2000000000 : ℝ)*x 0 + (1257343493/2500000000 : ℝ)*x 1 + (-2371976371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082196769/2000000000 : ℝ)^1063 ≤ (44531259813579/100000000000000 : ℝ)^807 := by
    have hnat : (1082196769 : ℕ)^1063*100000000000000^807 ≤ 44531259813579^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082196769 2000000000 44531259813579 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1257343493/2500000000 : ℝ)^1063 ≤ (20220733402513/50000000000000 : ℝ)^807 := by
    have hnat : (1257343493 : ℕ)^1063*50000000000000^807 ≤ 20220733402513^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257343493 2500000000 20220733402513 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2371976371/10000000000 : ℝ)^1063 ≤ (15027273372833/100000000000000 : ℝ)^807 := by
    have hnat : (2371976371 : ℕ)^1063*100000000000000^807 ≤ 15027273372833^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371976371 10000000000 15027273372833 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082196769/2000000000 : ℝ), (1257343493/2500000000 : ℝ), (-2371976371/10000000000 : ℝ)] ![(44531259813579/100000000000000 : ℝ), (20220733402513/50000000000000 : ℝ), (15027273372833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082196769/2000000000 : ℝ)|^1063 ≤ (44531259813579/100000000000000 : ℝ)^807
        have hw : |(1082196769/2000000000 : ℝ)|=(1082196769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1257343493/2500000000 : ℝ)|^1063 ≤ (20220733402513/50000000000000 : ℝ)^807
        have hw : |(1257343493/2500000000 : ℝ)|=(1257343493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2371976371/10000000000 : ℝ)|^1063 ≤ (15027273372833/100000000000000 : ℝ)^807
        have hw : |(-2371976371/10000000000 : ℝ)|=(2371976371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s1_3 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (107528537/250000000 : ℝ)*x 0 + (738935219/2000000000 : ℝ)*x 1 + (1250417569/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107528537/250000000 : ℝ)^1063 ≤ (8227873315643/25000000000000 : ℝ)^807 := by
    have hnat : (107528537 : ℕ)^1063*25000000000000^807 ≤ 8227873315643^807*250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107528537 250000000 8227873315643 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (738935219/2000000000 : ℝ)^1063 ≤ (3367527151031/12500000000000 : ℝ)^807 := by
    have hnat : (738935219 : ℕ)^1063*12500000000000^807 ≤ 3367527151031^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738935219 2000000000 3367527151031 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1250417569/2500000000 : ℝ)^1063 ≤ (20074144757033/50000000000000 : ℝ)^807 := by
    have hnat : (1250417569 : ℕ)^1063*50000000000000^807 ≤ 20074144757033^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250417569 2500000000 20074144757033 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107528537/250000000 : ℝ), (738935219/2000000000 : ℝ), (1250417569/2500000000 : ℝ)] ![(8227873315643/25000000000000 : ℝ), (3367527151031/12500000000000 : ℝ), (20074144757033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107528537/250000000 : ℝ)|^1063 ≤ (8227873315643/25000000000000 : ℝ)^807
        have hw : |(107528537/250000000 : ℝ)|=(107528537/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(738935219/2000000000 : ℝ)|^1063 ≤ (3367527151031/12500000000000 : ℝ)^807
        have hw : |(738935219/2000000000 : ℝ)|=(738935219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1250417569/2500000000 : ℝ)|^1063 ≤ (20074144757033/50000000000000 : ℝ)^807
        have hw : |(1250417569/2500000000 : ℝ)|=(1250417569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s1_4 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-406352533/2000000000 : ℝ)*x 0 + (5037665017/10000000000 : ℝ)*x 1 + (1414214939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406352533/2000000000 : ℝ)^1063 ≤ (2451000890907/20000000000000 : ℝ)^807 := by
    have hnat : (406352533 : ℕ)^1063*20000000000000^807 ≤ 2451000890907^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406352533 2000000000 2451000890907 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5037665017/10000000000 : ℝ)^1063 ≤ (40529307440981/100000000000000 : ℝ)^807 := by
    have hnat : (5037665017 : ℕ)^1063*100000000000000^807 ≤ 40529307440981^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037665017 10000000000 40529307440981 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414214939/2500000000 : ℝ)^1063 ≤ (4721568809677/10000000000000 : ℝ)^807 := by
    have hnat : (1414214939 : ℕ)^1063*10000000000000^807 ≤ 4721568809677^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414214939 2500000000 4721568809677 10000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406352533/2000000000 : ℝ), (5037665017/10000000000 : ℝ), (1414214939/2500000000 : ℝ)] ![(2451000890907/20000000000000 : ℝ), (40529307440981/100000000000000 : ℝ), (4721568809677/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406352533/2000000000 : ℝ)|^1063 ≤ (2451000890907/20000000000000 : ℝ)^807
        have hw : |(-406352533/2000000000 : ℝ)|=(406352533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5037665017/10000000000 : ℝ)|^1063 ≤ (40529307440981/100000000000000 : ℝ)^807
        have hw : |(5037665017/10000000000 : ℝ)|=(5037665017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414214939/2500000000 : ℝ)|^1063 ≤ (4721568809677/10000000000000 : ℝ)^807
        have hw : |(1414214939/2500000000 : ℝ)|=(1414214939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s1_5 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (20494847/39062500 : ℝ)*x 0 + (-174449009/1000000000 : ℝ)*x 1 + (707107551/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20494847/39062500 : ℝ)^1063 ≤ (10689693691719/25000000000000 : ℝ)^807 := by
    have hnat : (20494847 : ℕ)^1063*25000000000000^807 ≤ 10689693691719^807*39062500^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20494847 39062500 10689693691719 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174449009/1000000000 : ℝ)^1063 ≤ (1253191244623/12500000000000 : ℝ)^807 := by
    have hnat : (174449009 : ℕ)^1063*12500000000000^807 ≤ 1253191244623^807*1000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174449009 1000000000 1253191244623 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (707107551/1250000000 : ℝ)^1063 ≤ (2950980954069/6250000000000 : ℝ)^807 := by
    have hnat : (707107551 : ℕ)^1063*6250000000000^807 ≤ 2950980954069^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707107551 1250000000 2950980954069 6250000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20494847/39062500 : ℝ), (-174449009/1000000000 : ℝ), (707107551/1250000000 : ℝ)] ![(10689693691719/25000000000000 : ℝ), (1253191244623/12500000000000 : ℝ), (2950980954069/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20494847/39062500 : ℝ)|^1063 ≤ (10689693691719/25000000000000 : ℝ)^807
        have hw : |(20494847/39062500 : ℝ)|=(20494847/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174449009/1000000000 : ℝ)|^1063 ≤ (1253191244623/12500000000000 : ℝ)^807
        have hw : |(-174449009/1000000000 : ℝ)|=(174449009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(707107551/1250000000 : ℝ)|^1063 ≤ (2950980954069/6250000000000 : ℝ)^807
        have hw : |(707107551/1250000000 : ℝ)|=(707107551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s1_6 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (262334037/500000000 : ℝ)*x 0 + (5656860017/10000000000 : ℝ)*x 1 + (-436122697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262334037/500000000 : ℝ)^1063 ≤ (2137938688963/5000000000000 : ℝ)^807 := by
    have hnat : (262334037 : ℕ)^1063*5000000000000^807 ≤ 2137938688963^807*500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262334037 500000000 2137938688963 5000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5656860017/10000000000 : ℝ)^1063 ≤ (23607845483151/50000000000000 : ℝ)^807 := by
    have hnat : (5656860017 : ℕ)^1063*50000000000000^807 ≤ 23607845483151^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5656860017 10000000000 23607845483151 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436122697/2500000000 : ℝ)^1063 ≤ (10025535240877/100000000000000 : ℝ)^807 := by
    have hnat : (436122697 : ℕ)^1063*100000000000000^807 ≤ 10025535240877^807*2500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436122697 2500000000 10025535240877 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262334037/500000000 : ℝ), (5656860017/10000000000 : ℝ), (-436122697/2500000000 : ℝ)] ![(2137938688963/5000000000000 : ℝ), (23607845483151/50000000000000 : ℝ), (10025535240877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262334037/500000000 : ℝ)|^1063 ≤ (2137938688963/5000000000000 : ℝ)^807
        have hw : |(262334037/500000000 : ℝ)|=(262334037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5656860017/10000000000 : ℝ)|^1063 ≤ (23607845483151/50000000000000 : ℝ)^807
        have hw : |(5656860017/10000000000 : ℝ)|=(5656860017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436122697/2500000000 : ℝ)|^1063 ≤ (10025535240877/100000000000000 : ℝ)^807
        have hw : |(-436122697/2500000000 : ℝ)|=(436122697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s1_7 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4302450029/10000000000 : ℝ)*x 0 + (4984630667/10000000000 : ℝ)*x 1 + (3712037789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302450029/10000000000 : ℝ)^1063 ≤ (32924682950919/100000000000000 : ℝ)^807 := by
    have hnat : (4302450029 : ℕ)^1063*100000000000000^807 ≤ 32924682950919^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302450029 10000000000 32924682950919 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4984630667/10000000000 : ℝ)^1063 ≤ (9992055390671/25000000000000 : ℝ)^807 := by
    have hnat : (4984630667 : ℕ)^1063*25000000000000^807 ≤ 9992055390671^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4984630667 10000000000 9992055390671 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3712037789/10000000000 : ℝ)^1063 ≤ (27107095474519/100000000000000 : ℝ)^807 := by
    have hnat : (3712037789 : ℕ)^1063*100000000000000^807 ≤ 27107095474519^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3712037789 10000000000 27107095474519 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302450029/10000000000 : ℝ), (4984630667/10000000000 : ℝ), (3712037789/10000000000 : ℝ)] ![(32924682950919/100000000000000 : ℝ), (9992055390671/25000000000000 : ℝ), (27107095474519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302450029/10000000000 : ℝ)|^1063 ≤ (32924682950919/100000000000000 : ℝ)^807
        have hw : |(4302450029/10000000000 : ℝ)|=(4302450029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4984630667/10000000000 : ℝ)|^1063 ≤ (9992055390671/25000000000000 : ℝ)^807
        have hw : |(4984630667/10000000000 : ℝ)|=(4984630667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3712037789/10000000000 : ℝ)|^1063 ≤ (27107095474519/100000000000000 : ℝ)^807
        have hw : |(3712037789/10000000000 : ℝ)|=(3712037789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1292_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5447/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (129/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (6409/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (397/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5447/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (129/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5447/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (129/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5447/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (129/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5447/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (129/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5447/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (129/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5447/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (129/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (129/12500 : ℝ) ^ (4251/1024 : ℝ) ≤ (70952072307/12500000000000000000 : ℝ) := by
    have hpowers : (129/12500 : ℝ)^4251 ≤ (70952072307/12500000000000000000 : ℝ)^1024 := by
      have hnat : (129 : ℕ)^4251*12500000000000000000^1024 ≤ 70952072307^1024*12500^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129 12500 70952072307 12500000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (129/12500 : ℝ)) (X := (70952072307/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5447/20000 : ℝ) ^ (4251/1024 : ℝ) ≤ (45186253932748071/10000000000000000000 : ℝ) := by
    have hpowers : (5447/20000 : ℝ)^4251 ≤ (45186253932748071/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5447 : ℕ)^4251*10000000000000000000^1024 ≤ 45186253932748071^1024*20000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5447 20000 45186253932748071 10000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5447/20000 : ℝ)) (X := (45186253932748071/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000070952072307/6250000000000000000 : ℝ) ≤ (10000000027346007/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (6250000070952072307/6250000000000000000 : ℝ)^1024 ≤ (10000000027346007/10000000000000000 : ℝ)^4251 := by
      have hnat : (6250000070952072307 : ℕ)^1024*10000000000000000^4251 ≤ 10000000027346007^4251*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000070952072307 6250000000000000000 10000000027346007 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000027346007/10000000000000000 : ℝ)) (X := (6250000070952072307/6250000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50225931553472029583/50000000000000000000 : ℝ) ≤ (156419782233611/156250000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (50225931553472029583/50000000000000000000 : ℝ)^1024 ≤ (156419782233611/156250000000000 : ℝ)^4251 := by
      have hnat : (50225931553472029583 : ℕ)^1024*156250000000000^4251 ≤ 156419782233611^4251*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50225931553472029583 50000000000000000000 156419782233611 156250000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156419782233611/156250000000000 : ℝ)) (X := (50225931553472029583/50000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5045186253932748071/5000000000000000000 : ℝ) ≤ (10021732098556201/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (5045186253932748071/5000000000000000000 : ℝ)^1024 ≤ (10021732098556201/10000000000000000 : ℝ)^4251 := by
      have hnat : (5045186253932748071 : ℕ)^1024*10000000000000000^4251 ≤ 10021732098556201^4251*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5045186253932748071 5000000000000000000 10021732098556201 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10021732098556201/10000000000000000 : ℝ)) (X := (5045186253932748071/5000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(70952072307/12500000000000000000 : ℝ) ≤ ((262007573219058501213/262030000000000000000 : ℝ)+2*(10866035605097/2620300000000000 : ℝ)*(129/12500 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (262007573219058501213/262030000000000000000 : ℝ)+2*(10866035605097/2620300000000000 : ℝ)*(129/12500 : ℝ)=(10000000027346007/10000000000000000 : ℝ) by norm_num, show 1+2*(70952072307/12500000000000000000 : ℝ)=(6250000070952072307/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45186253932748071/10000000000000000000 : ℝ)+(70952072307/12500000000000000000 : ℝ) ≤ ((262007573219058501213/262030000000000000000 : ℝ)+(10866035605097/2620300000000000 : ℝ)*((5447/20000 : ℝ)+(129/12500 : ℝ)))^(4251/1024 : ℝ) := by
    rw [show (262007573219058501213/262030000000000000000 : ℝ)+(10866035605097/2620300000000000 : ℝ)*((5447/20000 : ℝ)+(129/12500 : ℝ))=(156419782233611/156250000000000 : ℝ) by norm_num, show 1+(45186253932748071/10000000000000000000 : ℝ)+(70952072307/12500000000000000000 : ℝ)=(50225931553472029583/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45186253932748071/10000000000000000000 : ℝ) ≤ ((262007573219058501213/262030000000000000000 : ℝ)+2*(10866035605097/2620300000000000 : ℝ)*(5447/20000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (262007573219058501213/262030000000000000000 : ℝ)+2*(10866035605097/2620300000000000 : ℝ)*(5447/20000 : ℝ)=(10021732098556201/10000000000000000 : ℝ) by norm_num, show 1+2*(45186253932748071/10000000000000000000 : ℝ)=(5045186253932748071/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (262007573219058501213/262030000000000000000 : ℝ)*(X 1 0+X 2 0)+(10866035605097/2620300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (129/12500 : ℝ)) (hi := (5447/20000 : ℝ)) (c := (262007573219058501213/262030000000000000000 : ℝ)) (alpha := (10866035605097/2620300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (262007573219058501213/262030000000000000000 : ℝ)*(X 0 1+X 2 1)+(10866035605097/2620300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (129/12500 : ℝ)) (hi := (5447/20000 : ℝ)) (c := (262007573219058501213/262030000000000000000 : ℝ)) (alpha := (10866035605097/2620300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (262007573219058501213/262030000000000000000 : ℝ)*(X 0 2+X 1 2)+(10866035605097/2620300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (129/12500 : ℝ)) (hi := (5447/20000 : ℝ)) (c := (262007573219058501213/262030000000000000000 : ℝ)) (alpha := (10866035605097/2620300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1015562813/5000000000 : ℝ)*X 0 0+(708163461/1250000000 : ℝ)*X 0 1+(502937397/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2705491991/5000000000 : ℝ)*X 1 0+(-2371976231/10000000000 : ℝ)*X 1 1+(2514686971/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1082196769/2000000000 : ℝ)*X 2 0+(1257343493/2500000000 : ℝ)*X 2 1+(-2371976371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107528537/250000000 : ℝ)*X 0 0+(738935219/2000000000 : ℝ)*X 0 1+(1250417569/2500000000 : ℝ)*X 0 2+(107528537/250000000 : ℝ)*X 1 0+(738935219/2000000000 : ℝ)*X 1 1+(1250417569/2500000000 : ℝ)*X 1 2+(107528537/250000000 : ℝ)*X 2 0+(738935219/2000000000 : ℝ)*X 2 1+(1250417569/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-406352533/2000000000 : ℝ)*X 0 0+(5037665017/10000000000 : ℝ)*X 0 1+(1414214939/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20494847/39062500 : ℝ)*X 1 0+(-174449009/1000000000 : ℝ)*X 1 1+(707107551/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262334037/500000000 : ℝ)*X 2 0+(5656860017/10000000000 : ℝ)*X 2 1+(-436122697/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302450029/10000000000 : ℝ)*X 0 0+(4984630667/10000000000 : ℝ)*X 0 1+(3712037789/10000000000 : ℝ)*X 0 2+(4302450029/10000000000 : ℝ)*X 1 0+(4984630667/10000000000 : ℝ)*X 1 1+(3712037789/10000000000 : ℝ)*X 1 2+(4302450029/10000000000 : ℝ)*X 2 0+(4984630667/10000000000 : ℝ)*X 2 1+(3712037789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4333102123253269213717788357/1310150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29812073/100000000000000 : ℝ)*(base1) + (612154369/100000000000000 : ℝ)*(base19) + (572340521/100000000000000 : ℝ)*(base23) + (23870373/25000000000000 : ℝ)*(upper3) + (1261371/4000000000000 : ℝ)*(upper5) + (116880756606963/10000000000000 : ℝ)*(major0) + (116880756606963/10000000000000 : ℝ)*(major1) + (116880756606963/10000000000000 : ℝ)*(major2) + (1572494631792881/100000000000000 : ℝ)*(sp0) + (786248504118351/50000000000000 : ℝ)*(sp1) + (31449940961011/2000000000000 : ℝ)*(sp2) + (153023142698579/20000000000000 : ℝ)*(sp3) + (3018410263/100000000000000 : ℝ)*(sp4) + (829099393/50000000000000 : ℝ)*(sp7) + (153023480300751/20000000000000 : ℝ)*(f.failure) + (157249762039107/10000000000000 : ℝ)*(f.sum) + (55764576514243/26203000000000000000000000000 : ℝ)*base65 + (14458360506344953881/2620300000000000000000000000000000 : ℝ)*base68 + (607204523529246119/2620300000000000000000000000000000 : ℝ)*base69 + (3252131021846553881/2620300000000000000000000000000000 : ℝ)*base72 + (51071215649553/26203000000000000000000000000 : ℝ)*base74 + (10953653108556553881/2620300000000000000000000000000000 : ℝ)*base76 + (1446440569617646119/2620300000000000000000000000000000 : ℝ)*base77 + (21502895562765253881/2620300000000000000000000000000000 : ℝ)*base80 + (2264288295093/524060000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1856109/2000000000000000000000 : ℝ)*base89 + (1856109/2000000000000000000000 : ℝ)*base91 + (1856109/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17804816316166516755472022343/3275375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (960192831/100000000000000 : ℝ)*(base19) + (937074083/100000000000000 : ℝ)*(base23) + (1158983/5000000000000 : ℝ)*(upper2) + (42546979/25000000000000 : ℝ)*(upper3) + (57574227/50000000000000 : ℝ)*(upper5) + (600199351539337/50000000000000 : ℝ)*(major0) + (600199351539337/50000000000000 : ℝ)*(major1) + (600199351539337/50000000000000 : ℝ)*(major2) + (2805918871/50000000000000 : ℝ)*(sp1) + (1091776737/25000000000000 : ℝ)*(sp2) + (1614999833556933/100000000000000 : ℝ)*(sp4) + (40374831538159/2500000000000 : ℝ)*(sp5) + (807497264687951/50000000000000 : ℝ)*(sp6) + (157159478280331/20000000000000 : ℝ)*(sp7) + (157159478280331/20000000000000 : ℝ)*(f.failure) + (1614999833556933/100000000000000 : ℝ)*(f.sum) + (42906616751367/8188437500000000000000000000 : ℝ)*base66 + (17293037585018384219/13101500000000000000000000000000000 : ℝ)*base68 + (53284985729313884219/13101500000000000000000000000000000 : ℝ)*base70 + (18363579662437884219/13101500000000000000000000000000000 : ℝ)*base72 + (397877141537867/131015000000000000000000000000 : ℝ)*base74 + (43547760905157884219/13101500000000000000000000000000000 : ℝ)*base76 + (105344469291601884219/13101500000000000000000000000000000 : ℝ)*base78 + (46291752712688115781/13101500000000000000000000000000000 : ℝ)*base79 + (167546643704287/131015000000000000000000000000 : ℝ)*base82 + (6695329/2000000000000000000000 : ℝ)*base89 + (6695329/2000000000000000000000 : ℝ)*base91 + (6695329/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1292_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5447/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (129/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (397/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1292_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1292_s2_0 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075817499/10000000000 : ℝ)*x 0 + (5494248929/10000000000 : ℝ)*x 1 + (2585943533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075817499/10000000000 : ℝ)^1063 ≤ (6303111556209/50000000000000 : ℝ)^807 := by
    have hnat : (2075817499 : ℕ)^1063*50000000000000^807 ≤ 6303111556209^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075817499 10000000000 6303111556209 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494248929/10000000000 : ℝ)^1063 ≤ (2271804432357/5000000000000 : ℝ)^807 := by
    have hnat : (5494248929 : ℕ)^1063*5000000000000^807 ≤ 2271804432357^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494248929 10000000000 2271804432357 5000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585943533/5000000000 : ℝ)^1063 ≤ (41957688225041/100000000000000 : ℝ)^807 := by
    have hnat : (2585943533 : ℕ)^1063*100000000000000^807 ≤ 41957688225041^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585943533 5000000000 41957688225041 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075817499/10000000000 : ℝ), (5494248929/10000000000 : ℝ), (2585943533/5000000000 : ℝ)] ![(6303111556209/50000000000000 : ℝ), (2271804432357/5000000000000 : ℝ), (41957688225041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075817499/10000000000 : ℝ)|^1063 ≤ (6303111556209/50000000000000 : ℝ)^807
        have hw : |(-2075817499/10000000000 : ℝ)|=(2075817499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494248929/10000000000 : ℝ)|^1063 ≤ (2271804432357/5000000000000 : ℝ)^807
        have hw : |(5494248929/10000000000 : ℝ)|=(5494248929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585943533/5000000000 : ℝ)|^1063 ≤ (41957688225041/100000000000000 : ℝ)^807
        have hw : |(2585943533/5000000000 : ℝ)|=(2585943533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s2_1 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369583313/10000000000 : ℝ)*x 0 + (-1121435841/5000000000 : ℝ)*x 1 + (1034377451/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369583313/10000000000 : ℝ)^1063 ≤ (44083003819297/100000000000000 : ℝ)^807 := by
    have hnat : (5369583313 : ℕ)^1063*100000000000000^807 ≤ 44083003819297^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369583313 10000000000 44083003819297 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121435841/5000000000 : ℝ)^1063 ≤ (13959305914091/100000000000000 : ℝ)^807 := by
    have hnat : (1121435841 : ℕ)^1063*100000000000000^807 ≤ 13959305914091^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121435841 5000000000 13959305914091 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034377451/2000000000 : ℝ)^1063 ≤ (5244711280591/12500000000000 : ℝ)^807 := by
    have hnat : (1034377451 : ℕ)^1063*12500000000000^807 ≤ 5244711280591^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034377451 2000000000 5244711280591 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369583313/10000000000 : ℝ), (-1121435841/5000000000 : ℝ), (1034377451/2000000000 : ℝ)] ![(44083003819297/100000000000000 : ℝ), (13959305914091/100000000000000 : ℝ), (5244711280591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369583313/10000000000 : ℝ)|^1063 ≤ (44083003819297/100000000000000 : ℝ)^807
        have hw : |(5369583313/10000000000 : ℝ)|=(5369583313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1121435841/5000000000 : ℝ)|^1063 ≤ (13959305914091/100000000000000 : ℝ)^807
        have hw : |(-1121435841/5000000000 : ℝ)|=(1121435841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034377451/2000000000 : ℝ)|^1063 ≤ (5244711280591/12500000000000 : ℝ)^807
        have hw : |(1034377451/2000000000 : ℝ)|=(1034377451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s2_2 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369583367/10000000000 : ℝ)*x 0 + (206875483/400000000 : ℝ)*x 1 + (-2242871847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369583367/10000000000 : ℝ)^1063 ≤ (22041502201629/50000000000000 : ℝ)^807 := by
    have hnat : (5369583367 : ℕ)^1063*50000000000000^807 ≤ 22041502201629^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369583367 10000000000 22041502201629 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206875483/400000000 : ℝ)^1063 ≤ (41957688321217/100000000000000 : ℝ)^807 := by
    have hnat : (206875483 : ℕ)^1063*100000000000000^807 ≤ 41957688321217^807*400000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206875483 400000000 41957688321217 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242871847/10000000000 : ℝ)^1063 ≤ (3489826816699/25000000000000 : ℝ)^807 := by
    have hnat : (2242871847 : ℕ)^1063*25000000000000^807 ≤ 3489826816699^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242871847 10000000000 3489826816699 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369583367/10000000000 : ℝ), (206875483/400000000 : ℝ), (-2242871847/10000000000 : ℝ)] ![(22041502201629/50000000000000 : ℝ), (41957688321217/100000000000000 : ℝ), (3489826816699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369583367/10000000000 : ℝ)|^1063 ≤ (22041502201629/50000000000000 : ℝ)^807
        have hw : |(5369583367/10000000000 : ℝ)|=(5369583367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206875483/400000000 : ℝ)|^1063 ≤ (41957688321217/100000000000000 : ℝ)^807
        have hw : |(206875483/400000000 : ℝ)|=(206875483/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2242871847/10000000000 : ℝ)|^1063 ≤ (3489826816699/25000000000000 : ℝ)^807
        have hw : |(-2242871847/10000000000 : ℝ)|=(2242871847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s2_3 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4332210249/10000000000 : ℝ)*x 0 + (501626213/1250000000 : ℝ)*x 1 + (233777359/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332210249/10000000000 : ℝ)^1063 ≤ (33224998004111/100000000000000 : ℝ)^807 := by
    have hnat : (4332210249 : ℕ)^1063*100000000000000^807 ≤ 33224998004111^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332210249 10000000000 33224998004111 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501626213/1250000000 : ℝ)^1063 ≤ (3754839196621/12500000000000 : ℝ)^807 := by
    have hnat : (501626213 : ℕ)^1063*12500000000000^807 ≤ 3754839196621^807*1250000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501626213 1250000000 3754839196621 12500000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233777359/500000000 : ℝ)^1063 ≤ (7347257681689/20000000000000 : ℝ)^807 := by
    have hnat : (233777359 : ℕ)^1063*20000000000000^807 ≤ 7347257681689^807*500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233777359 500000000 7347257681689 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332210249/10000000000 : ℝ), (501626213/1250000000 : ℝ), (233777359/500000000 : ℝ)] ![(33224998004111/100000000000000 : ℝ), (3754839196621/12500000000000 : ℝ), (7347257681689/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332210249/10000000000 : ℝ)|^1063 ≤ (33224998004111/100000000000000 : ℝ)^807
        have hw : |(4332210249/10000000000 : ℝ)|=(4332210249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501626213/1250000000 : ℝ)|^1063 ≤ (3754839196621/12500000000000 : ℝ)^807
        have hw : |(501626213/1250000000 : ℝ)|=(501626213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(233777359/500000000 : ℝ)|^1063 ≤ (7347257681689/20000000000000 : ℝ)^807
        have hw : |(233777359/500000000 : ℝ)|=(233777359/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s2_4 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-415179941/2000000000 : ℝ)*x 0 + (2587013469/5000000000 : ℝ)*x 1 + (5492089069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415179941/2000000000 : ℝ)^1063 ≤ (3151720178101/25000000000000 : ℝ)^807 := by
    have hnat : (415179941 : ℕ)^1063*25000000000000^807 ≤ 3151720178101^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415179941 2000000000 3151720178101 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587013469/5000000000 : ℝ)^1063 ≤ (8396111354093/20000000000000 : ℝ)^807 := by
    have hnat : (2587013469 : ℕ)^1063*20000000000000^807 ≤ 8396111354093^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587013469 5000000000 8396111354093 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492089069/10000000000 : ℝ)^1063 ≤ (22706281248759/50000000000000 : ℝ)^807 := by
    have hnat : (5492089069 : ℕ)^1063*50000000000000^807 ≤ 22706281248759^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492089069 10000000000 22706281248759 50000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415179941/2000000000 : ℝ), (2587013469/5000000000 : ℝ), (5492089069/10000000000 : ℝ)] ![(3151720178101/25000000000000 : ℝ), (8396111354093/20000000000000 : ℝ), (22706281248759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415179941/2000000000 : ℝ)|^1063 ≤ (3151720178101/25000000000000 : ℝ)^807
        have hw : |(-415179941/2000000000 : ℝ)|=(415179941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587013469/5000000000 : ℝ)|^1063 ≤ (8396111354093/20000000000000 : ℝ)^807
        have hw : |(2587013469/5000000000 : ℝ)|=(2587013469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492089069/10000000000 : ℝ)|^1063 ≤ (22706281248759/50000000000000 : ℝ)^807
        have hw : |(5492089069/10000000000 : ℝ)|=(5492089069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s2_5 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (264348101/500000000 : ℝ)*x 0 + (-1922669249/10000000000 : ℝ)*x 1 + (5492089207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264348101/500000000 : ℝ)^1063 ≤ (43191717268389/100000000000000 : ℝ)^807 := by
    have hnat : (264348101 : ℕ)^1063*100000000000000^807 ≤ 43191717268389^807*500000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264348101 500000000 43191717268389 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1922669249/10000000000 : ℝ)^1063 ≤ (2279143743871/20000000000000 : ℝ)^807 := by
    have hnat : (1922669249 : ℕ)^1063*20000000000000^807 ≤ 2279143743871^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922669249 10000000000 2279143743871 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492089207/10000000000 : ℝ)^1063 ≤ (45412564000581/100000000000000 : ℝ)^807 := by
    have hnat : (5492089207 : ℕ)^1063*100000000000000^807 ≤ 45412564000581^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492089207 10000000000 45412564000581 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264348101/500000000 : ℝ), (-1922669249/10000000000 : ℝ), (5492089207/10000000000 : ℝ)] ![(43191717268389/100000000000000 : ℝ), (2279143743871/20000000000000 : ℝ), (45412564000581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264348101/500000000 : ℝ)|^1063 ≤ (43191717268389/100000000000000 : ℝ)^807
        have hw : |(264348101/500000000 : ℝ)|=(264348101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1922669249/10000000000 : ℝ)|^1063 ≤ (2279143743871/20000000000000 : ℝ)^807
        have hw : |(-1922669249/10000000000 : ℝ)|=(1922669249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492089207/10000000000 : ℝ)|^1063 ≤ (45412564000581/100000000000000 : ℝ)^807
        have hw : |(5492089207/10000000000 : ℝ)|=(5492089207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s2_6 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2643481093/5000000000 : ℝ)*x 0 + (5492089077/10000000000 : ℝ)*x 1 + (-961334601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643481093/5000000000 : ℝ)^1063 ≤ (67487061023/156250000000 : ℝ)^807 := by
    have hnat : (2643481093 : ℕ)^1063*156250000000^807 ≤ 67487061023^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643481093 5000000000 67487061023 156250000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492089077/10000000000 : ℝ)^1063 ≤ (11353140646163/25000000000000 : ℝ)^807 := by
    have hnat : (5492089077 : ℕ)^1063*25000000000000^807 ≤ 11353140646163^807*10000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492089077 10000000000 11353140646163 25000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961334601/5000000000 : ℝ)^1063 ≤ (2279143670483/20000000000000 : ℝ)^807 := by
    have hnat : (961334601 : ℕ)^1063*20000000000000^807 ≤ 2279143670483^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961334601 5000000000 2279143670483 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643481093/5000000000 : ℝ), (5492089077/10000000000 : ℝ), (-961334601/5000000000 : ℝ)] ![(67487061023/156250000000 : ℝ), (11353140646163/25000000000000 : ℝ), (2279143670483/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643481093/5000000000 : ℝ)|^1063 ≤ (67487061023/156250000000 : ℝ)^807
        have hw : |(2643481093/5000000000 : ℝ)|=(2643481093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492089077/10000000000 : ℝ)|^1063 ≤ (11353140646163/25000000000000 : ℝ)^807
        have hw : |(5492089077/10000000000 : ℝ)|=(5492089077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-961334601/5000000000 : ℝ)|^1063 ≤ (2279143670483/20000000000000 : ℝ)^807
        have hw : |(-961334601/5000000000 : ℝ)|=(961334601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1292_s2_7 (p : ℝ) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2166189417/5000000000 : ℝ)*x 0 + (934229523/2000000000 : ℝ)*x 1 + (803490717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166189417/5000000000 : ℝ)^1063 ≤ (6645340218179/20000000000000 : ℝ)^807 := by
    have hnat : (2166189417 : ℕ)^1063*20000000000000^807 ≤ 6645340218179^807*5000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166189417 5000000000 6645340218179 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934229523/2000000000 : ℝ)^1063 ≤ (7338152314607/20000000000000 : ℝ)^807 := by
    have hnat : (934229523 : ℕ)^1063*20000000000000^807 ≤ 7338152314607^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934229523 2000000000 7338152314607 20000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803490717/2000000000 : ℝ)^1063 ≤ (30082537321703/100000000000000 : ℝ)^807 := by
    have hnat : (803490717 : ℕ)^1063*100000000000000^807 ≤ 30082537321703^807*2000000000^1063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803490717 2000000000 30082537321703 100000000000000 1063 807 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1063/256 : ℝ)) 1063 807 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166189417/5000000000 : ℝ), (934229523/2000000000 : ℝ), (803490717/2000000000 : ℝ)] ![(6645340218179/20000000000000 : ℝ), (7338152314607/20000000000000 : ℝ), (30082537321703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166189417/5000000000 : ℝ)|^1063 ≤ (6645340218179/20000000000000 : ℝ)^807
        have hw : |(2166189417/5000000000 : ℝ)|=(2166189417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(934229523/2000000000 : ℝ)|^1063 ≤ (7338152314607/20000000000000 : ℝ)^807
        have hw : |(934229523/2000000000 : ℝ)|=(934229523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803490717/2000000000 : ℝ)|^1063 ≤ (30082537321703/100000000000000 : ℝ)^807
        have hw : |(803490717/2000000000 : ℝ)|=(803490717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1292_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (397/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1901/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16317/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (397/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (397/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (397/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (397/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (397/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (397/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6409/100000 : ℝ) ^ (4251/1024 : ℝ) ≤ (1113136146418077/100000000000000000000 : ℝ) := by
    have hpowers : (6409/100000 : ℝ)^4251 ≤ (1113136146418077/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6409 : ℕ)^4251*100000000000000000000^1024 ≤ 1113136146418077^1024*100000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6409 100000 1113136146418077 100000000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6409/100000 : ℝ)) (X := (1113136146418077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (397/2000 : ℝ) ^ (4251/1024 : ℝ) ≤ (759671870359761/625000000000000000 : ℝ) := by
    have hpowers : (397/2000 : ℝ)^4251 ≤ (759671870359761/625000000000000000 : ℝ)^1024 := by
      have hnat : (397 : ℕ)^4251*625000000000000000^1024 ≤ 759671870359761^1024*2000^4251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        397 2000 759671870359761 625000000000000000 4251 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (397/2000 : ℝ)) (X := (759671870359761/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001113136146418077/50000000000000000000 : ℝ) ≤ (1000005362699517/1000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (50001113136146418077/50000000000000000000 : ℝ)^1024 ≤ (1000005362699517/1000000000000000 : ℝ)^4251 := by
      have hnat : (50001113136146418077 : ℕ)^1024*1000000000000000^4251 ≤ 1000005362699517^4251*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001113136146418077 50000000000000000000 1000005362699517 1000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000005362699517/1000000000000000 : ℝ)) (X := (50001113136146418077/50000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100122660635403979837/100000000000000000000 : ℝ) ≤ (10002953329928317/10000000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (100122660635403979837/100000000000000000000 : ℝ)^1024 ≤ (10002953329928317/10000000000000000 : ℝ)^4251 := by
      have hnat : (100122660635403979837 : ℕ)^1024*10000000000000000^4251 ≤ 10002953329928317^4251*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100122660635403979837 100000000000000000000 10002953329928317 10000000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002953329928317/10000000000000000 : ℝ)) (X := (100122660635403979837/100000000000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (313259671870359761/312500000000000000 : ℝ) ≤ (1250731629107683/1250000000000000 : ℝ) ^ (4251/1024 : ℝ) := by
    have hpowers : (313259671870359761/312500000000000000 : ℝ)^1024 ≤ (1250731629107683/1250000000000000 : ℝ)^4251 := by
      have hnat : (313259671870359761 : ℕ)^1024*1250000000000000^4251 ≤ 1250731629107683^4251*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        313259671870359761 312500000000000000 1250731629107683 1250000000000000 1024 4251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250731629107683/1250000000000000 : ℝ)) (X := (313259671870359761/312500000000000000 : ℝ)) (by norm_num) 4251 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1113136146418077/100000000000000000000 : ℝ) ≤ ((33593388102061250431/33602500000000000000 : ℝ)+2*(2899702933147/1344100000000000 : ℝ)*(6409/100000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (33593388102061250431/33602500000000000000 : ℝ)+2*(2899702933147/1344100000000000 : ℝ)*(6409/100000 : ℝ)=(1000005362699517/1000000000000000 : ℝ) by norm_num, show 1+2*(1113136146418077/100000000000000000000 : ℝ)=(50001113136146418077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(759671870359761/625000000000000000 : ℝ)+(1113136146418077/100000000000000000000 : ℝ) ≤ ((33593388102061250431/33602500000000000000 : ℝ)+(2899702933147/1344100000000000 : ℝ)*((397/2000 : ℝ)+(6409/100000 : ℝ)))^(4251/1024 : ℝ) := by
    rw [show (33593388102061250431/33602500000000000000 : ℝ)+(2899702933147/1344100000000000 : ℝ)*((397/2000 : ℝ)+(6409/100000 : ℝ))=(10002953329928317/10000000000000000 : ℝ) by norm_num, show 1+(759671870359761/625000000000000000 : ℝ)+(1113136146418077/100000000000000000000 : ℝ)=(100122660635403979837/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(759671870359761/625000000000000000 : ℝ) ≤ ((33593388102061250431/33602500000000000000 : ℝ)+2*(2899702933147/1344100000000000 : ℝ)*(397/2000 : ℝ))^(4251/1024 : ℝ) := by
    rw [show (33593388102061250431/33602500000000000000 : ℝ)+2*(2899702933147/1344100000000000 : ℝ)*(397/2000 : ℝ)=(1250731629107683/1250000000000000 : ℝ) by norm_num, show 1+2*(759671870359761/625000000000000000 : ℝ)=(313259671870359761/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33593388102061250431/33602500000000000000 : ℝ)*(X 1 0+X 2 0)+(2899702933147/1344100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (6409/100000 : ℝ)) (hi := (397/2000 : ℝ)) (c := (33593388102061250431/33602500000000000000 : ℝ)) (alpha := (2899702933147/1344100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33593388102061250431/33602500000000000000 : ℝ)*(X 0 1+X 2 1)+(2899702933147/1344100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (6409/100000 : ℝ)) (hi := (397/2000 : ℝ)) (c := (33593388102061250431/33602500000000000000 : ℝ)) (alpha := (2899702933147/1344100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33593388102061250431/33602500000000000000 : ℝ)*(X 0 2+X 1 2)+(2899702933147/1344100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4251/1024 : ℝ)) (lo := (6409/100000 : ℝ)) (hi := (397/2000 : ℝ)) (c := (33593388102061250431/33602500000000000000 : ℝ)) (alpha := (2899702933147/1344100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2075817499/10000000000 : ℝ)*X 0 0+(5494248929/10000000000 : ℝ)*X 0 1+(2585943533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369583313/10000000000 : ℝ)*X 1 0+(-1121435841/5000000000 : ℝ)*X 1 1+(1034377451/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369583367/10000000000 : ℝ)*X 2 0+(206875483/400000000 : ℝ)*X 2 1+(-2242871847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4332210249/10000000000 : ℝ)*X 0 0+(501626213/1250000000 : ℝ)*X 0 1+(233777359/500000000 : ℝ)*X 0 2+(4332210249/10000000000 : ℝ)*X 1 0+(501626213/1250000000 : ℝ)*X 1 1+(233777359/500000000 : ℝ)*X 1 2+(4332210249/10000000000 : ℝ)*X 2 0+(501626213/1250000000 : ℝ)*X 2 1+(233777359/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-415179941/2000000000 : ℝ)*X 0 0+(2587013469/5000000000 : ℝ)*X 0 1+(5492089069/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264348101/500000000 : ℝ)*X 1 0+(-1922669249/10000000000 : ℝ)*X 1 1+(5492089207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643481093/5000000000 : ℝ)*X 2 0+(5492089077/10000000000 : ℝ)*X 2 1+(-961334601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2166189417/5000000000 : ℝ)*X 0 0+(934229523/2000000000 : ℝ)*X 0 1+(803490717/2000000000 : ℝ)*X 0 2+(2166189417/5000000000 : ℝ)*X 1 0+(934229523/2000000000 : ℝ)*X 1 1+(803490717/2000000000 : ℝ)*X 1 2+(2166189417/5000000000 : ℝ)*X 2 0+(934229523/2000000000 : ℝ)*X 2 1+(803490717/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1292_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (731828090963538651258536361/420031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1259681529/100000000000000 : ℝ)*(base19) + (551559553/50000000000000 : ℝ)*(base23) + (100818941/100000000000000 : ℝ)*(lower2) + (234239087/50000000000000 : ℝ)*(upper3) + (25611133/12500000000000 : ℝ)*(upper5) + (1152873453727677/50000000000000 : ℝ)*(major0) + (1152873453727677/50000000000000 : ℝ)*(major1) + (1152873453727677/50000000000000 : ℝ)*(major2) + (310211413487587/10000000000000 : ℝ)*(sp0) + (1551059534709973/50000000000000 : ℝ)*(sp1) + (96941225811949/3125000000000 : ℝ)*(sp2) + (754679787256591/50000000000000 : ℝ)*(sp3) + (1238845121/20000000000000 : ℝ)*(sp4) + (3463304693/25000000000000 : ℝ)*(sp7) + (754686713865977/50000000000000 : ℝ)*(f.failure) + (1551060164550737/50000000000000 : ℝ)*(f.sum) + (53636150887283/67205000000000000000000000000 : ℝ)*base65 + (19974497846732646213/1680125000000000000000000000000000 : ℝ)*base68 + (5101856474282271213/1680125000000000000000000000000000 : ℝ)*base70 + (12593032699917146213/1680125000000000000000000000000000 : ℝ)*base72 + (131957071264421/33602500000000000000000000000 : ℝ)*base74 + (7204161713365396213/1680125000000000000000000000000000 : ℝ)*base76 + (7245382928351896213/1680125000000000000000000000000000 : ℝ)*base78 + (9222205527007353787/1680125000000000000000000000000000 : ℝ)*base79 + (38257973550409/33602500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (23371243/5000000000000000000000 : ℝ)*base89 + (23371243/5000000000000000000000 : ℝ)*base91 + (23371243/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1417844919306875543530732701/336025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (405173247/50000000000000 : ℝ)*(base19) + (1086517631/100000000000000 : ℝ)*(base23) + (29379757/20000000000000 : ℝ)*(upper3) + (62705623/100000000000000 : ℝ)*(lower4) + (30006957/100000000000000 : ℝ)*(upper5) + (467380609386943/20000000000000 : ℝ)*(major0) + (467380609386943/20000000000000 : ℝ)*(major1) + (467380609386943/20000000000000 : ℝ)*(major2) + (1021956217/12500000000000 : ℝ)*(sp1) + (1194152407/10000000000000 : ℝ)*(sp2) + (3144037290916871/100000000000000 : ℝ)*(sp4) + (9825088452877/312500000000 : ℝ)*(sp5) + (314402426287517/10000000000000 : ℝ)*(sp6) + (764884331151899/50000000000000 : ℝ)*(sp7) + (764884331151899/50000000000000 : ℝ)*(f.failure) + (3144037290916871/100000000000000 : ℝ)*(f.sum) + (3297108747533/1680125000000000000000000000 : ℝ)*base65 + (1250597449339352567/672050000000000000000000000000000 : ℝ)*base68 + (1583857743839402567/672050000000000000000000000000000 : ℝ)*base70 + (2240872375010047433/672050000000000000000000000000000 : ℝ)*base71 + (44188084062357/13441000000000000000000000000 : ℝ)*base74 + (3327978243965547433/672050000000000000000000000000000 : ℝ)*base75 + (777203159728947433/672050000000000000000000000000000 : ℝ)*base77 + (138367034719547433/672050000000000000000000000000000 : ℝ)*base79 + (13734511192579/13441000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (47379759/5000000000000000000000 : ℝ)*base90 + (47379759/5000000000000000000000 : ℝ)*base92 + (47379759/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1292_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (397/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1901/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1292_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1292_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1901/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1292_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1292_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1292_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4251/1024 : ℝ) ≤ p) (hpb : p ≤ (1063/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152761859/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1901/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1292_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

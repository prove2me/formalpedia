-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1103_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:02:23.065199+00:00
-- url     : https://prove2.me/submissions/a8d9047f-abe4-4f4b-986e-c266b23f76f7

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
theorem support_rectangle_w1103_box_0 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1028742259/5000000000 : ℝ)*x 0 + (5376859181/10000000000 : ℝ)*x 1 + (1344214717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028742259/5000000000 : ℝ)^1037 ≤ (1531682298331/12500000000000 : ℝ)^781 := by
    have hnat : (1028742259 : ℕ)^1037*12500000000000^781 ≤ 1531682298331^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028742259 5000000000 1531682298331 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376859181/10000000000 : ℝ)^1037 ≤ (43873272493887/100000000000000 : ℝ)^781 := by
    have hnat : (5376859181 : ℕ)^1037*100000000000000^781 ≤ 43873272493887^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376859181 10000000000 43873272493887 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344214717/2500000000 : ℝ)^1037 ≤ (8774653820553/20000000000000 : ℝ)^781 := by
    have hnat : (1344214717 : ℕ)^1037*20000000000000^781 ≤ 8774653820553^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344214717 2500000000 8774653820553 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1028742259/5000000000 : ℝ), (5376859181/10000000000 : ℝ), (1344214717/2500000000 : ℝ)] ![(1531682298331/12500000000000 : ℝ), (43873272493887/100000000000000 : ℝ), (8774653820553/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1028742259/5000000000 : ℝ)|^1037 ≤ (1531682298331/12500000000000 : ℝ)^781
        have hw : |(-1028742259/5000000000 : ℝ)|=(1028742259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376859181/10000000000 : ℝ)|^1037 ≤ (43873272493887/100000000000000 : ℝ)^781
        have hw : |(5376859181/10000000000 : ℝ)|=(5376859181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344214717/2500000000 : ℝ)|^1037 ≤ (8774653820553/20000000000000 : ℝ)^781
        have hw : |(1344214717/2500000000 : ℝ)|=(1344214717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_1 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (82743771/156250000 : ℝ)*x 0 + (-2167583853/10000000000 : ℝ)*x 1 + (1075371819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82743771/156250000 : ℝ)^1037 ≤ (42995092243277/100000000000000 : ℝ)^781 := by
    have hnat : (82743771 : ℕ)^1037*100000000000000^781 ≤ 42995092243277^781*156250000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82743771 156250000 42995092243277 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2167583853/10000000000 : ℝ)^1037 ≤ (2626327237971/20000000000000 : ℝ)^781 := by
    have hnat : (2167583853 : ℕ)^1037*20000000000000^781 ≤ 2626327237971^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167583853 10000000000 2626327237971 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075371819/2000000000 : ℝ)^1037 ≤ (43873271562141/100000000000000 : ℝ)^781 := by
    have hnat : (1075371819 : ℕ)^1037*100000000000000^781 ≤ 43873271562141^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075371819 2000000000 43873271562141 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82743771/156250000 : ℝ), (-2167583853/10000000000 : ℝ), (1075371819/2000000000 : ℝ)] ![(42995092243277/100000000000000 : ℝ), (2626327237971/20000000000000 : ℝ), (43873271562141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82743771/156250000 : ℝ)|^1037 ≤ (42995092243277/100000000000000 : ℝ)^781
        have hw : |(82743771/156250000 : ℝ)|=(82743771/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2167583853/10000000000 : ℝ)|^1037 ≤ (2626327237971/20000000000000 : ℝ)^781
        have hw : |(-2167583853/10000000000 : ℝ)|=(2167583853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075371819/2000000000 : ℝ)|^1037 ≤ (43873271562141/100000000000000 : ℝ)^781
        have hw : |(1075371819/2000000000 : ℝ)|=(1075371819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_2 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1323900383/2500000000 : ℝ)*x 0 + (5376858981/10000000000 : ℝ)*x 1 + (-1083791877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323900383/2500000000 : ℝ)^1037 ≤ (5374386783747/12500000000000 : ℝ)^781 := by
    have hnat : (1323900383 : ℕ)^1037*12500000000000^781 ≤ 5374386783747^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323900383 2500000000 5374386783747 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376858981/10000000000 : ℝ)^1037 ≤ (10968317581759/25000000000000 : ℝ)^781 := by
    have hnat : (5376858981 : ℕ)^1037*25000000000000^781 ≤ 10968317581759^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376858981 10000000000 10968317581759 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083791877/5000000000 : ℝ)^1037 ≤ (6565817696751/50000000000000 : ℝ)^781 := by
    have hnat : (1083791877 : ℕ)^1037*50000000000000^781 ≤ 6565817696751^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083791877 5000000000 6565817696751 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323900383/2500000000 : ℝ), (5376858981/10000000000 : ℝ), (-1083791877/5000000000 : ℝ)] ![(5374386783747/12500000000000 : ℝ), (10968317581759/25000000000000 : ℝ), (6565817696751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323900383/2500000000 : ℝ)|^1037 ≤ (5374386783747/12500000000000 : ℝ)^781
        have hw : |(1323900383/2500000000 : ℝ)|=(1323900383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376858981/10000000000 : ℝ)|^1037 ≤ (10968317581759/25000000000000 : ℝ)^781
        have hw : |(5376858981/10000000000 : ℝ)|=(5376858981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1083791877/5000000000 : ℝ)|^1037 ≤ (6565817696751/50000000000000 : ℝ)^781
        have hw : |(-1083791877/5000000000 : ℝ)|=(1083791877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_3 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1119542419/2500000000 : ℝ)*x 0 + (2159174843/5000000000 : ℝ)*x 1 + (539793541/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119542419/2500000000 : ℝ)^1037 ≤ (34414112559993/100000000000000 : ℝ)^781 := by
    have hnat : (1119542419 : ℕ)^1037*100000000000000^781 ≤ 34414112559993^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119542419 2500000000 34414112559993 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159174843/5000000000 : ℝ)^1037 ≤ (4099118820393/12500000000000 : ℝ)^781 := by
    have hnat : (2159174843 : ℕ)^1037*12500000000000^781 ≤ 4099118820393^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159174843 5000000000 4099118820393 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539793541/1250000000 : ℝ)^1037 ≤ (3279293687041/10000000000000 : ℝ)^781 := by
    have hnat : (539793541 : ℕ)^1037*10000000000000^781 ≤ 3279293687041^781*1250000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539793541 1250000000 3279293687041 10000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119542419/2500000000 : ℝ), (2159174843/5000000000 : ℝ), (539793541/1250000000 : ℝ)] ![(34414112559993/100000000000000 : ℝ), (4099118820393/12500000000000 : ℝ), (3279293687041/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119542419/2500000000 : ℝ)|^1037 ≤ (34414112559993/100000000000000 : ℝ)^781
        have hw : |(1119542419/2500000000 : ℝ)|=(1119542419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2159174843/5000000000 : ℝ)|^1037 ≤ (4099118820393/12500000000000 : ℝ)^781
        have hw : |(2159174843/5000000000 : ℝ)|=(2159174843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539793541/1250000000 : ℝ)|^1037 ≤ (3279293687041/10000000000000 : ℝ)^781
        have hw : |(539793541/1250000000 : ℝ)|=(539793541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_4 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-289408261/1250000000 : ℝ)*x 0 + (330038789/625000000 : ℝ)*x 1 + (165019403/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (289408261/1250000000 : ℝ)^1037 ≤ (14332656391559/100000000000000 : ℝ)^781 := by
    have hnat : (289408261 : ℕ)^1037*100000000000000^781 ≤ 14332656391559^781*1250000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289408261 1250000000 14332656391559 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330038789/625000000 : ℝ)^1037 ≤ (10708417583299/25000000000000 : ℝ)^781 := by
    have hnat : (330038789 : ℕ)^1037*25000000000000^781 ≤ 10708417583299^781*625000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330038789 625000000 10708417583299 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165019403/312500000 : ℝ)^1037 ≤ (42833673262719/100000000000000 : ℝ)^781 := by
    have hnat : (165019403 : ℕ)^1037*100000000000000^781 ≤ 42833673262719^781*312500000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165019403 312500000 42833673262719 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-289408261/1250000000 : ℝ), (330038789/625000000 : ℝ), (165019403/312500000 : ℝ)] ![(14332656391559/100000000000000 : ℝ), (10708417583299/25000000000000 : ℝ), (42833673262719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-289408261/1250000000 : ℝ)|^1037 ≤ (14332656391559/100000000000000 : ℝ)^781
        have hw : |(-289408261/1250000000 : ℝ)|=(289408261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330038789/625000000 : ℝ)|^1037 ≤ (10708417583299/25000000000000 : ℝ)^781
        have hw : |(330038789/625000000 : ℝ)|=(330038789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165019403/312500000 : ℝ)|^1037 ≤ (42833673262719/100000000000000 : ℝ)^781
        have hw : |(165019403/312500000 : ℝ)|=(165019403/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_5 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1072730651/2000000000 : ℝ)*x 0 + (-441064599/2000000000 : ℝ)*x 1 + (528062101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072730651/2000000000 : ℝ)^1037 ≤ (43730253736493/100000000000000 : ℝ)^781 := by
    have hnat : (1072730651 : ℕ)^1037*100000000000000^781 ≤ 43730253736493^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072730651 2000000000 43730253736493 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441064599/2000000000 : ℝ)^1037 ≤ (13436071750369/100000000000000 : ℝ)^781 := by
    have hnat : (441064599 : ℕ)^1037*100000000000000^781 ≤ 13436071750369^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441064599 2000000000 13436071750369 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528062101/1000000000 : ℝ)^1037 ≤ (21416837245267/50000000000000 : ℝ)^781 := by
    have hnat : (528062101 : ℕ)^1037*50000000000000^781 ≤ 21416837245267^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528062101 1000000000 21416837245267 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072730651/2000000000 : ℝ), (-441064599/2000000000 : ℝ), (528062101/1000000000 : ℝ)] ![(43730253736493/100000000000000 : ℝ), (13436071750369/100000000000000 : ℝ), (21416837245267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072730651/2000000000 : ℝ)|^1037 ≤ (43730253736493/100000000000000 : ℝ)^781
        have hw : |(1072730651/2000000000 : ℝ)|=(1072730651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441064599/2000000000 : ℝ)|^1037 ≤ (13436071750369/100000000000000 : ℝ)^781
        have hw : |(-441064599/2000000000 : ℝ)|=(441064599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528062101/1000000000 : ℝ)|^1037 ≤ (21416837245267/50000000000000 : ℝ)^781
        have hw : |(528062101/1000000000 : ℝ)|=(528062101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_6 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5363653989/10000000000 : ℝ)*x 0 + (2640310383/5000000000 : ℝ)*x 1 + (-1102661169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363653989/10000000000 : ℝ)^1037 ≤ (4373026168243/10000000000000 : ℝ)^781 := by
    have hnat : (5363653989 : ℕ)^1037*10000000000000^781 ≤ 4373026168243^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363653989 10000000000 4373026168243 10000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640310383/5000000000 : ℝ)^1037 ≤ (42833671862579/100000000000000 : ℝ)^781 := by
    have hnat : (2640310383 : ℕ)^1037*100000000000000^781 ≤ 42833671862579^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640310383 5000000000 42833671862579 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102661169/5000000000 : ℝ)^1037 ≤ (13436066435493/100000000000000 : ℝ)^781 := by
    have hnat : (1102661169 : ℕ)^1037*100000000000000^781 ≤ 13436066435493^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102661169 5000000000 13436066435493 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363653989/10000000000 : ℝ), (2640310383/5000000000 : ℝ), (-1102661169/5000000000 : ℝ)] ![(4373026168243/10000000000000 : ℝ), (42833671862579/100000000000000 : ℝ), (13436066435493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363653989/10000000000 : ℝ)|^1037 ≤ (4373026168243/10000000000000 : ℝ)^781
        have hw : |(5363653989/10000000000 : ℝ)|=(5363653989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640310383/5000000000 : ℝ)|^1037 ≤ (42833671862579/100000000000000 : ℝ)^781
        have hw : |(2640310383/5000000000 : ℝ)|=(2640310383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102661169/5000000000 : ℝ)|^1037 ≤ (13436066435493/100000000000000 : ℝ)^781
        have hw : |(-1102661169/5000000000 : ℝ)|=(1102661169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_7 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2130942023/5000000000 : ℝ)*x 0 + (2213235639/5000000000 : ℝ)*x 1 + (442647007/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130942023/5000000000 : ℝ)^1037 ≤ (8056207595071/25000000000000 : ℝ)^781 := by
    have hnat : (2130942023 : ℕ)^1037*25000000000000^781 ≤ 8056207595071^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130942023 5000000000 8056207595071 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213235639/5000000000 : ℝ)^1037 ≤ (33887590941569/100000000000000 : ℝ)^781 := by
    have hnat : (2213235639 : ℕ)^1037*100000000000000^781 ≤ 33887590941569^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213235639 5000000000 33887590941569 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442647007/1000000000 : ℝ)^1037 ≤ (33887578662153/100000000000000 : ℝ)^781 := by
    have hnat : (442647007 : ℕ)^1037*100000000000000^781 ≤ 33887578662153^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442647007 1000000000 33887578662153 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130942023/5000000000 : ℝ), (2213235639/5000000000 : ℝ), (442647007/1000000000 : ℝ)] ![(8056207595071/25000000000000 : ℝ), (33887590941569/100000000000000 : ℝ), (33887578662153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130942023/5000000000 : ℝ)|^1037 ≤ (8056207595071/25000000000000 : ℝ)^781
        have hw : |(2130942023/5000000000 : ℝ)|=(2130942023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2213235639/5000000000 : ℝ)|^1037 ≤ (33887590941569/100000000000000 : ℝ)^781
        have hw : |(2213235639/5000000000 : ℝ)|=(2213235639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442647007/1000000000 : ℝ)|^1037 ≤ (33887578662153/100000000000000 : ℝ)^781
        have hw : |(442647007/1000000000 : ℝ)|=(442647007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_8 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-113070303/500000000 : ℝ)*x 0 + (260762263/500000000 : ℝ)*x 1 + (53864643/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113070303/500000000 : ℝ)^1037 ≤ (3472910602531/25000000000000 : ℝ)^781 := by
    have hnat : (113070303 : ℕ)^1037*25000000000000^781 ≤ 3472910602531^781*500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113070303 500000000 3472910602531 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260762263/500000000 : ℝ)^1037 ≤ (42130990302553/100000000000000 : ℝ)^781 := by
    have hnat : (260762263 : ℕ)^1037*100000000000000^781 ≤ 42130990302553^781*500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260762263 500000000 42130990302553 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53864643/100000000 : ℝ)^1037 ≤ (43977367266327/100000000000000 : ℝ)^781 := by
    have hnat : (53864643 : ℕ)^1037*100000000000000^781 ≤ 43977367266327^781*100000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53864643 100000000 43977367266327 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-113070303/500000000 : ℝ), (260762263/500000000 : ℝ), (53864643/100000000 : ℝ)] ![(3472910602531/25000000000000 : ℝ), (42130990302553/100000000000000 : ℝ), (43977367266327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-113070303/500000000 : ℝ)|^1037 ≤ (3472910602531/25000000000000 : ℝ)^781
        have hw : |(-113070303/500000000 : ℝ)|=(113070303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260762263/500000000 : ℝ)|^1037 ≤ (42130990302553/100000000000000 : ℝ)^781
        have hw : |(260762263/500000000 : ℝ)|=(260762263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53864643/100000000 : ℝ)|^1037 ≤ (43977367266327/100000000000000 : ℝ)^781
        have hw : |(53864643/100000000 : ℝ)|=(53864643/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_9 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5288805607/10000000000 : ℝ)*x 0 + (-2163747709/10000000000 : ℝ)*x 1 + (1346616027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288805607/10000000000 : ℝ)^1037 ≤ (10730461872931/25000000000000 : ℝ)^781 := by
    have hnat : (5288805607 : ℕ)^1037*25000000000000^781 ≤ 10730461872931^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288805607 10000000000 10730461872931 25000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2163747709/10000000000 : ℝ)^1037 ≤ (13100787301281/100000000000000 : ℝ)^781 := by
    have hnat : (2163747709 : ℕ)^1037*100000000000000^781 ≤ 13100787301281^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163747709 10000000000 13100787301281 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346616027/2500000000 : ℝ)^1037 ≤ (43977365184933/100000000000000 : ℝ)^781 := by
    have hnat : (1346616027 : ℕ)^1037*100000000000000^781 ≤ 43977365184933^781*2500000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346616027 2500000000 43977365184933 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288805607/10000000000 : ℝ), (-2163747709/10000000000 : ℝ), (1346616027/2500000000 : ℝ)] ![(10730461872931/25000000000000 : ℝ), (13100787301281/100000000000000 : ℝ), (43977365184933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288805607/10000000000 : ℝ)|^1037 ≤ (10730461872931/25000000000000 : ℝ)^781
        have hw : |(5288805607/10000000000 : ℝ)|=(5288805607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2163747709/10000000000 : ℝ)|^1037 ≤ (13100787301281/100000000000000 : ℝ)^781
        have hw : |(-2163747709/10000000000 : ℝ)|=(2163747709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346616027/2500000000 : ℝ)|^1037 ≤ (43977365184933/100000000000000 : ℝ)^781
        have hw : |(1346616027/2500000000 : ℝ)|=(1346616027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_10 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (528880577/1000000000 : ℝ)*x 0 + (2693232173/5000000000 : ℝ)*x 1 + (-216374717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528880577/1000000000 : ℝ)^1037 ≤ (2682615578011/6250000000000 : ℝ)^781 := by
    have hnat : (528880577 : ℕ)^1037*6250000000000^781 ≤ 2682615578011^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528880577 1000000000 2682615578011 6250000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693232173/5000000000 : ℝ)^1037 ≤ (8795473552999/20000000000000 : ℝ)^781 := by
    have hnat : (2693232173 : ℕ)^1037*20000000000000^781 ≤ 8795473552999^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693232173 5000000000 8795473552999 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216374717/1000000000 : ℝ)^1037 ≤ (2620156593619/20000000000000 : ℝ)^781 := by
    have hnat : (216374717 : ℕ)^1037*20000000000000^781 ≤ 2620156593619^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216374717 1000000000 2620156593619 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528880577/1000000000 : ℝ), (2693232173/5000000000 : ℝ), (-216374717/1000000000 : ℝ)] ![(2682615578011/6250000000000 : ℝ), (8795473552999/20000000000000 : ℝ), (2620156593619/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528880577/1000000000 : ℝ)|^1037 ≤ (2682615578011/6250000000000 : ℝ)^781
        have hw : |(528880577/1000000000 : ℝ)|=(528880577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693232173/5000000000 : ℝ)|^1037 ≤ (8795473552999/20000000000000 : ℝ)^781
        have hw : |(2693232173/5000000000 : ℝ)|=(2693232173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216374717/1000000000 : ℝ)|^1037 ≤ (2620156593619/20000000000000 : ℝ)^781
        have hw : |(-216374717/1000000000 : ℝ)|=(216374717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_11 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (449948333/1000000000 : ℝ)*x 0 + (269221969/625000000 : ℝ)*x 1 + (861510357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449948333/1000000000 : ℝ)^1037 ≤ (1385270527791/4000000000000 : ℝ)^781 := by
    have hnat : (449948333 : ℕ)^1037*4000000000000^781 ≤ 1385270527791^781*1000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449948333 1000000000 1385270527791 4000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269221969/625000000 : ℝ)^1037 ≤ (32684116978339/100000000000000 : ℝ)^781 := by
    have hnat : (269221969 : ℕ)^1037*100000000000000^781 ≤ 32684116978339^781*625000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269221969 625000000 32684116978339 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861510357/2000000000 : ℝ)^1037 ≤ (16342059904671/50000000000000 : ℝ)^781 := by
    have hnat : (861510357 : ℕ)^1037*50000000000000^781 ≤ 16342059904671^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861510357 2000000000 16342059904671 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(449948333/1000000000 : ℝ), (269221969/625000000 : ℝ), (861510357/2000000000 : ℝ)] ![(1385270527791/4000000000000 : ℝ), (32684116978339/100000000000000 : ℝ), (16342059904671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(449948333/1000000000 : ℝ)|^1037 ≤ (1385270527791/4000000000000 : ℝ)^781
        have hw : |(449948333/1000000000 : ℝ)|=(449948333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269221969/625000000 : ℝ)|^1037 ≤ (32684116978339/100000000000000 : ℝ)^781
        have hw : |(269221969/625000000 : ℝ)|=(269221969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(861510357/2000000000 : ℝ)|^1037 ≤ (16342059904671/50000000000000 : ℝ)^781
        have hw : |(861510357/2000000000 : ℝ)|=(861510357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_12 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055844259/5000000000 : ℝ)*x 0 + (2720463851/5000000000 : ℝ)*x 1 + (1054520123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055844259/5000000000 : ℝ)^1037 ≤ (1585490861613/12500000000000 : ℝ)^781 := by
    have hnat : (1055844259 : ℕ)^1037*12500000000000^781 ≤ 1585490861613^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055844259 5000000000 1585490861613 12500000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720463851/5000000000 : ℝ)^1037 ≤ (22284379602337/50000000000000 : ℝ)^781 := by
    have hnat : (2720463851 : ℕ)^1037*50000000000000^781 ≤ 22284379602337^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720463851 5000000000 22284379602337 50000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054520123/2000000000 : ℝ)^1037 ≤ (42747313889649/100000000000000 : ℝ)^781 := by
    have hnat : (1054520123 : ℕ)^1037*100000000000000^781 ≤ 42747313889649^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054520123 2000000000 42747313889649 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055844259/5000000000 : ℝ), (2720463851/5000000000 : ℝ), (1054520123/2000000000 : ℝ)] ![(1585490861613/12500000000000 : ℝ), (22284379602337/50000000000000 : ℝ), (42747313889649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055844259/5000000000 : ℝ)|^1037 ≤ (1585490861613/12500000000000 : ℝ)^781
        have hw : |(-1055844259/5000000000 : ℝ)|=(1055844259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720463851/5000000000 : ℝ)|^1037 ≤ (22284379602337/50000000000000 : ℝ)^781
        have hw : |(2720463851/5000000000 : ℝ)|=(2720463851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054520123/2000000000 : ℝ)|^1037 ≤ (42747313889649/100000000000000 : ℝ)^781
        have hw : |(1054520123/2000000000 : ℝ)|=(1054520123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_13 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369322391/10000000000 : ℝ)*x 0 + (-1104204997/5000000000 : ℝ)*x 1 + (5272600637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369322391/10000000000 : ℝ)^1037 ≤ (136848861709/312500000000 : ℝ)^781 := by
    have hnat : (5369322391 : ℕ)^1037*312500000000^781 ≤ 136848861709^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369322391 10000000000 136848861709 312500000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104204997/5000000000 : ℝ)^1037 ≤ (538442004393/4000000000000 : ℝ)^781 := by
    have hnat : (1104204997 : ℕ)^1037*4000000000000^781 ≤ 538442004393^781*5000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104204997 5000000000 538442004393 4000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272600637/10000000000 : ℝ)^1037 ≤ (42747314126477/100000000000000 : ℝ)^781 := by
    have hnat : (5272600637 : ℕ)^1037*100000000000000^781 ≤ 42747314126477^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272600637 10000000000 42747314126477 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369322391/10000000000 : ℝ), (-1104204997/5000000000 : ℝ), (5272600637/10000000000 : ℝ)] ![(136848861709/312500000000 : ℝ), (538442004393/4000000000000 : ℝ), (42747314126477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369322391/10000000000 : ℝ)|^1037 ≤ (136848861709/312500000000 : ℝ)^781
        have hw : |(5369322391/10000000000 : ℝ)|=(5369322391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1104204997/5000000000 : ℝ)|^1037 ≤ (538442004393/4000000000000 : ℝ)^781
        have hw : |(-1104204997/5000000000 : ℝ)|=(1104204997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272600637/10000000000 : ℝ)|^1037 ≤ (42747314126477/100000000000000 : ℝ)^781
        have hw : |(5272600637/10000000000 : ℝ)|=(5272600637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_14 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369321971/10000000000 : ℝ)*x 0 + (5272600941/10000000000 : ℝ)*x 1 + (-2208410151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369321971/10000000000 : ℝ)^1037 ≤ (8758326239717/20000000000000 : ℝ)^781 := by
    have hnat : (5369321971 : ℕ)^1037*20000000000000^781 ≤ 8758326239717^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369321971 10000000000 8758326239717 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272600941/10000000000 : ℝ)^1037 ≤ (42747317399019/100000000000000 : ℝ)^781 := by
    have hnat : (5272600941 : ℕ)^1037*100000000000000^781 ≤ 42747317399019^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272600941 10000000000 42747317399019 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208410151/10000000000 : ℝ)^1037 ≤ (13461051380477/100000000000000 : ℝ)^781 := by
    have hnat : (2208410151 : ℕ)^1037*100000000000000^781 ≤ 13461051380477^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208410151 10000000000 13461051380477 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369321971/10000000000 : ℝ), (5272600941/10000000000 : ℝ), (-2208410151/10000000000 : ℝ)] ![(8758326239717/20000000000000 : ℝ), (42747317399019/100000000000000 : ℝ), (13461051380477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369321971/10000000000 : ℝ)|^1037 ≤ (8758326239717/20000000000000 : ℝ)^781
        have hw : |(5369321971/10000000000 : ℝ)|=(5369321971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272600941/10000000000 : ℝ)|^1037 ≤ (42747317399019/100000000000000 : ℝ)^781
        have hw : |(5272600941/10000000000 : ℝ)|=(5272600941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2208410151/10000000000 : ℝ)|^1037 ≤ (13461051380477/100000000000000 : ℝ)^781
        have hw : |(-2208410151/10000000000 : ℝ)|=(2208410151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1103_box_15 (p : ℝ) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4243628017/10000000000 : ℝ)*x 0 + (69304327/156250000 : ℝ)*x 1 + (887095287/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243628017/10000000000 : ℝ)^1037 ≤ (32041675811687/100000000000000 : ℝ)^781 := by
    have hnat : (4243628017 : ℕ)^1037*100000000000000^781 ≤ 32041675811687^781*10000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243628017 10000000000 32041675811687 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69304327/156250000 : ℝ)^1037 ≤ (6795832919497/20000000000000 : ℝ)^781 := by
    have hnat : (69304327 : ℕ)^1037*20000000000000^781 ≤ 6795832919497^781*156250000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69304327 156250000 6795832919497 20000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887095287/2000000000 : ℝ)^1037 ≤ (33979159582761/100000000000000 : ℝ)^781 := by
    have hnat : (887095287 : ℕ)^1037*100000000000000^781 ≤ 33979159582761^781*2000000000^1037 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887095287 2000000000 33979159582761 100000000000000 1037 781 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1037/256 : ℝ)) 1037 781 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243628017/10000000000 : ℝ), (69304327/156250000 : ℝ), (887095287/2000000000 : ℝ)] ![(32041675811687/100000000000000 : ℝ), (6795832919497/20000000000000 : ℝ), (33979159582761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243628017/10000000000 : ℝ)|^1037 ≤ (32041675811687/100000000000000 : ℝ)^781
        have hw : |(4243628017/10000000000 : ℝ)|=(4243628017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(69304327/156250000 : ℝ)|^1037 ≤ (6795832919497/20000000000000 : ℝ)^781
        have hw : |(69304327/156250000 : ℝ)|=(69304327/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(887095287/2000000000 : ℝ)|^1037 ≤ (33979159582761/100000000000000 : ℝ)^781
        have hw : |(887095287/2000000000 : ℝ)|=(887095287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1103_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62227/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59269/100000 : ℝ) ∧ (9961/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83037/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (561/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (561/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (561/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (561/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (561/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (561/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5651/50000 : ℝ) ^ (8295/2048 : ℝ) ≤ (2924364995308881/20000000000000000000 : ℝ) := by
    have hpowers : (5651/50000 : ℝ)^8295 ≤ (2924364995308881/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5651 : ℕ)^8295*20000000000000000000^2048 ≤ 2924364995308881^2048*50000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5651 50000 2924364995308881 20000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5651/50000 : ℝ)) (X := (2924364995308881/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (561/4000 : ℝ) ^ (8295/2048 : ℝ) ≤ (35051506814692099/100000000000000000000 : ℝ) := by
    have hpowers : (561/4000 : ℝ)^8295 ≤ (35051506814692099/100000000000000000000 : ℝ)^2048 := by
      have hnat : (561 : ℕ)^8295*100000000000000000000^2048 ≤ 35051506814692099^2048*4000^8295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 4000 35051506814692099 100000000000000000000 8295 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/4000 : ℝ)) (X := (35051506814692099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002924364995308881/10000000000000000000 : ℝ) ≤ (10000721933709207/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (10002924364995308881/10000000000000000000 : ℝ)^2048 ≤ (10000721933709207/10000000000000000 : ℝ)^8295 := by
      have hnat : (10002924364995308881 : ℕ)^2048*10000000000000000^8295 ≤ 10000721933709207^8295*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002924364995308881 10000000000000000000 10000721933709207 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000721933709207/10000000000000000 : ℝ)) (X := (10002924364995308881/10000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506209166473904563/12500000000000000000 : ℝ) ≤ (10001226183974167/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (12506209166473904563/12500000000000000000 : ℝ)^2048 ≤ (10001226183974167/10000000000000000 : ℝ)^8295 := by
      have hnat : (12506209166473904563 : ℕ)^2048*10000000000000000^8295 ≤ 10001226183974167^8295*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506209166473904563 12500000000000000000 10001226183974167 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001226183974167/10000000000000000 : ℝ)) (X := (12506209166473904563/12500000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035051506814692099/50000000000000000000 : ℝ) ≤ (10001730434239127/10000000000000000 : ℝ) ^ (8295/2048 : ℝ) := by
    have hpowers : (50035051506814692099/50000000000000000000 : ℝ)^2048 ≤ (10001730434239127/10000000000000000 : ℝ)^8295 := by
      have hnat : (50035051506814692099 : ℕ)^2048*10000000000000000^8295 ≤ 10001730434239127^8295*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035051506814692099 50000000000000000000 10001730434239127 10000000000000000 2048 8295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001730434239127/10000000000000000 : ℝ)) (X := (50035051506814692099/50000000000000000000 : ℝ)) (by norm_num) 8295 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2924364995308881/20000000000000000000 : ℝ) ≤ ((27220567752501014821/27230000000000000000 : ℝ)+2*(787891039/425468750000 : ℝ)*(5651/50000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (27220567752501014821/27230000000000000000 : ℝ)+2*(787891039/425468750000 : ℝ)*(5651/50000 : ℝ)=(10000721933709207/10000000000000000 : ℝ) by norm_num, show 1+2*(2924364995308881/20000000000000000000 : ℝ)=(10002924364995308881/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35051506814692099/100000000000000000000 : ℝ)+(2924364995308881/20000000000000000000 : ℝ) ≤ ((27220567752501014821/27230000000000000000 : ℝ)+(787891039/425468750000 : ℝ)*((561/4000 : ℝ)+(5651/50000 : ℝ)))^(8295/2048 : ℝ) := by
    rw [show (27220567752501014821/27230000000000000000 : ℝ)+(787891039/425468750000 : ℝ)*((561/4000 : ℝ)+(5651/50000 : ℝ))=(10001226183974167/10000000000000000 : ℝ) by norm_num, show 1+(35051506814692099/100000000000000000000 : ℝ)+(2924364995308881/20000000000000000000 : ℝ)=(12506209166473904563/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35051506814692099/100000000000000000000 : ℝ) ≤ ((27220567752501014821/27230000000000000000 : ℝ)+2*(787891039/425468750000 : ℝ)*(561/4000 : ℝ))^(8295/2048 : ℝ) := by
    rw [show (27220567752501014821/27230000000000000000 : ℝ)+2*(787891039/425468750000 : ℝ)*(561/4000 : ℝ)=(10001730434239127/10000000000000000 : ℝ) by norm_num, show 1+2*(35051506814692099/100000000000000000000 : ℝ)=(50035051506814692099/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27220567752501014821/27230000000000000000 : ℝ)*(X 1 0+X 2 0)+(787891039/425468750000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (27220567752501014821/27230000000000000000 : ℝ)) (alpha := (787891039/425468750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27220567752501014821/27230000000000000000 : ℝ)*(X 0 1+X 2 1)+(787891039/425468750000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (27220567752501014821/27230000000000000000 : ℝ)) (alpha := (787891039/425468750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27220567752501014821/27230000000000000000 : ℝ)*(X 0 2+X 1 2)+(787891039/425468750000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8295/2048 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (27220567752501014821/27230000000000000000 : ℝ)) (alpha := (787891039/425468750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1028742259/5000000000 : ℝ)*X 0 0+(5376859181/10000000000 : ℝ)*X 0 1+(1344214717/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((82743771/156250000 : ℝ)*X 1 0+(-2167583853/10000000000 : ℝ)*X 1 1+(1075371819/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323900383/2500000000 : ℝ)*X 2 0+(5376858981/10000000000 : ℝ)*X 2 1+(-1083791877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1119542419/2500000000 : ℝ)*X 0 0+(2159174843/5000000000 : ℝ)*X 0 1+(539793541/1250000000 : ℝ)*X 0 2+(1119542419/2500000000 : ℝ)*X 1 0+(2159174843/5000000000 : ℝ)*X 1 1+(539793541/1250000000 : ℝ)*X 1 2+(1119542419/2500000000 : ℝ)*X 2 0+(2159174843/5000000000 : ℝ)*X 2 1+(539793541/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-289408261/1250000000 : ℝ)*X 0 0+(330038789/625000000 : ℝ)*X 0 1+(165019403/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072730651/2000000000 : ℝ)*X 1 0+(-441064599/2000000000 : ℝ)*X 1 1+(528062101/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363653989/10000000000 : ℝ)*X 2 0+(2640310383/5000000000 : ℝ)*X 2 1+(-1102661169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2130942023/5000000000 : ℝ)*X 0 0+(2213235639/5000000000 : ℝ)*X 0 1+(442647007/1000000000 : ℝ)*X 0 2+(2130942023/5000000000 : ℝ)*X 1 0+(2213235639/5000000000 : ℝ)*X 1 1+(442647007/1000000000 : ℝ)*X 1 2+(2130942023/5000000000 : ℝ)*X 2 0+(2213235639/5000000000 : ℝ)*X 2 1+(442647007/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-113070303/500000000 : ℝ)*X 0 0+(260762263/500000000 : ℝ)*X 0 1+(53864643/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288805607/10000000000 : ℝ)*X 1 0+(-2163747709/10000000000 : ℝ)*X 1 1+(1346616027/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((528880577/1000000000 : ℝ)*X 2 0+(2693232173/5000000000 : ℝ)*X 2 1+(-216374717/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((449948333/1000000000 : ℝ)*X 0 0+(269221969/625000000 : ℝ)*X 0 1+(861510357/2000000000 : ℝ)*X 0 2+(449948333/1000000000 : ℝ)*X 1 0+(269221969/625000000 : ℝ)*X 1 1+(861510357/2000000000 : ℝ)*X 1 2+(449948333/1000000000 : ℝ)*X 2 0+(269221969/625000000 : ℝ)*X 2 1+(861510357/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1055844259/5000000000 : ℝ)*X 0 0+(2720463851/5000000000 : ℝ)*X 0 1+(1054520123/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369322391/10000000000 : ℝ)*X 1 0+(-1104204997/5000000000 : ℝ)*X 1 1+(5272600637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369321971/10000000000 : ℝ)*X 2 0+(5272600941/10000000000 : ℝ)*X 2 1+(-2208410151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4243628017/10000000000 : ℝ)*X 0 0+(69304327/156250000 : ℝ)*X 0 1+(887095287/2000000000 : ℝ)*X 0 2+(4243628017/10000000000 : ℝ)*X 1 0+(69304327/156250000 : ℝ)*X 1 1+(887095287/2000000000 : ℝ)*X 1 2+(4243628017/10000000000 : ℝ)*X 2 0+(69304327/156250000 : ℝ)*X 2 1+(887095287/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1103_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62227/100000 : ℝ) ≤ (-847188838090479575335142619/1361500000000000000000000000 : ℝ) := by norm_num
    linear_combination (10331027/25000000000000 : ℝ)*(lower0) + (21768737/4000000000000 : ℝ)*(lower2) + (18305721/100000000000000 : ℝ)*(lower4) + (13845291/100000000000000 : ℝ)*(lower5) + (1943872163805129/50000000000000 : ℝ)*(major0) + (1943872163805129/50000000000000 : ℝ)*(major1) + (1943872163805129/50000000000000 : ℝ)*(major2) + (3960612149/50000000000000 : ℝ)*(sp1) + (129549088437789/2500000000000 : ℝ)*(sp4) + (5181968399972431/100000000000000 : ℝ)*(sp5) + (647726827885981/12500000000000 : ℝ)*(sp6) + (2614253889614193/100000000000000 : ℝ)*(sp7) + (12783685169/100000000000000 : ℝ)*(sp8) + (80849054441/50000000000000 : ℝ)*(sp14) + (2614253889614193/100000000000000 : ℝ)*(f.failure) + (5181976321196729/100000000000000 : ℝ)*(f.sum) + (7610533347901/1361500000000000000000000000 : ℝ)*base65 + (7061603492577816909/1361500000000000000000000000000000 : ℝ)*base67 + (664932065786183091/1361500000000000000000000000000000 : ℝ)*base70 + (13764917072726316909/1361500000000000000000000000000000 : ℝ)*base71 + (12846408766291/2723000000000000000000000000 : ℝ)*base73 + (6056664255126183091/1361500000000000000000000000000000 : ℝ)*base76 + (4727548727990816909/1361500000000000000000000000000000 : ℝ)*base77 + (3845028752147183091/1361500000000000000000000000000000 : ℝ)*base80 + (1302984404493/340375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (34168497/5000000000000000000000 : ℝ)*base90 + (34168497/5000000000000000000000 : ℝ)*base92 + (34168497/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59269/100000 : ℝ) ≤ (40348783575065987024086052427147/68075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6206683/12500000000000 : ℝ)*(upper3) + (306788497/100000000000000 : ℝ)*(upper4) + (187538041/50000000000000 : ℝ)*(lower5) + (395129209998469/10000000000000 : ℝ)*(major0) + (395129209998469/10000000000000 : ℝ)*(major1) + (395129209998469/10000000000000 : ℝ)*(major2) + (2612918056247899/50000000000000 : ℝ)*(sp0) + (5225834940501053/100000000000000 : ℝ)*(sp1) + (209032171846143/4000000000000 : ℝ)*(sp2) + (33212048426429/1250000000000 : ℝ)*(sp3) + (6622879919/100000000000000 : ℝ)*(sp5) + (37267227397/100000000000000 : ℝ)*(sp6) + (1358614507/6250000000000 : ℝ)*(sp7) + (2725442587/50000000000000 : ℝ)*(sp8) + (41515400186663/1562500000000 : ℝ)*(f.failure) + (1306460390845243/25000000000000 : ℝ)*(f.sum) + (1534818042129/680750000000000000000000000 : ℝ)*base65 + (3210338055667890951/272300000000000000000000000000000 : ℝ)*base68 + (281421937473109049/272300000000000000000000000000000 : ℝ)*base69 + (1210884824462390951/272300000000000000000000000000000 : ℝ)*base72 + (15963606162943/1361500000000000000000000000 : ℝ)*base74 + (1738853550827190951/272300000000000000000000000000000 : ℝ)*base76 + (951576790081190951/272300000000000000000000000000000 : ℝ)*base78 + (631204084345590951/272300000000000000000000000000000 : ℝ)*base80 + (50136510737/170187500000000000000000000 : ℝ)*base82 + (216373/78125000000000000000 : ℝ)*base89 + (216373/78125000000000000000 : ℝ)*base91 + (216373/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (9961/12500 : ℝ) ≤ (77498918964906765002533310794209/97250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104404631/100000000000000 : ℝ)*(upper0) + (39851857/100000000000000 : ℝ)*(lower1) + (18988323/12500000000000 : ℝ)*(lower3) + (276084439/100000000000000 : ℝ)*(upper4) + (2209700125551667/50000000000000 : ℝ)*(major0) + (2209700125551667/50000000000000 : ℝ)*(major1) + (2209700125551667/50000000000000 : ℝ)*(major2) + (17171457/20000000000000 : ℝ)*(sp0) + (26617269229/10000000000000 : ℝ)*(sp2) + (157164801647/100000000000000 : ℝ)*(sp3) + (5840479208111607/100000000000000 : ℝ)*(sp8) + (1460119823492223/25000000000000 : ℝ)*(sp9) + (2920106560638301/50000000000000 : ℝ)*(sp10) + (742900143766919/25000000000000 : ℝ)*(sp11) + (1485878869934661/50000000000000 : ℝ)*(f.failure) + (1460119823492223/25000000000000 : ℝ)*(f.sum) + (126073746737/194500000000000000000000000 : ℝ)*base66 + (3103707417926606199/194500000000000000000000000000000 : ℝ)*base68 + (12352016588199106199/194500000000000000000000000000000 : ℝ)*base70 + (1839134731729106199/194500000000000000000000000000000 : ℝ)*base72 + (45376419499/194500000000000000000000000 : ℝ)*base74 + (1045876462691106199/194500000000000000000000000000000 : ℝ)*base76 + (2348531082861106199/194500000000000000000000000000000 : ℝ)*base78 + (1945901895253106199/194500000000000000000000000000000 : ℝ)*base80 + (1147533925443/19450000000000000000000000 : ℝ)*base82 + (29473531/2500000000000000000000 : ℝ)*base89 + (29473531/2500000000000000000000 : ℝ)*base91 + (29473531/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-83037/100000 : ℝ) ≤ (-2208027317991291898617340563969/2659179687500000000000000000000 : ℝ) := by norm_num
    linear_combination (92216359/25000000000000 : ℝ)*(upper3) + (56277329/100000000000000 : ℝ)*(lower4) + (11354749/50000000000000 : ℝ)*(upper5) + (139191795130929/3125000000000 : ℝ)*(major0) + (139191795130929/3125000000000 : ℝ)*(major1) + (139191795130929/3125000000000 : ℝ)*(major2) + (714995069/10000000000000 : ℝ)*(sp4) + (56345580559/12500000000000 : ℝ)*(sp5) + (109927650681/100000000000000 : ℝ)*(sp6) + (127085797261/50000000000000 : ℝ)*(sp7) + (5940829558083153/100000000000000 : ℝ)*(sp12) + (5940385943389371/100000000000000 : ℝ)*(sp13) + (2970363390191581/50000000000000 : ℝ)*(sp14) + (46794719681207/1562500000000 : ℝ)*(sp15) + (299511623119177/10000000000000 : ℝ)*(f.failure) + (5940836708033843/100000000000000 : ℝ)*(f.sum) + (447560154767/1361500000000000000000000000 : ℝ)*base65 + (867879000742311209/85093750000000000000000000000000 : ℝ)*base67 + (1212381342977717459/85093750000000000000000000000000 : ℝ)*base69 + (68994417841404959/85093750000000000000000000000000 : ℝ)*base71 + (8633891243759/1361500000000000000000000000 : ℝ)*base73 + (300979406484032541/85093750000000000000000000000000 : ℝ)*base76 + (3726967842342459/85093750000000000000000000000000 : ℝ)*base77 + (475583017673373709/85093750000000000000000000000000 : ℝ)*base79 + (1401366937809/680750000000000000000000000 : ℝ)*base81 + (2020233/500000000000000000000 : ℝ)*base90 + (2020233/500000000000000000000 : ℝ)*base92 + (2020233/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1103_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59269/100000 : ℝ) else (9961/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83037/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1103_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1103_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59269/100000 : ℝ) else (9961/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83037/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1103_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8295/2048 : ℝ) ≤ p) (hpb : p ≤ (1037/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74356671/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59269/100000 : ℝ) else (9961/12500 : ℝ) ≤ X j i ∧ X j i ≤ (83037/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1103_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

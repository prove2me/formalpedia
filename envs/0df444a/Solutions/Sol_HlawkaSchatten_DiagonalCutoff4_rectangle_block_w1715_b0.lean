-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1715_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:47.11315+00:00
-- url     : https://prove2.me/submissions/5d385192-9810-445b-ace9-d9f7767f44d4

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
theorem support_rectangle_w1715_s0_0 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-26439999/200000000 : ℝ)*x 0 + (1421990281/2500000000 : ℝ)*x 1 + (4965420257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26439999/200000000 : ℝ)^5343 ≤ (1636486810743/20000000000000 : ℝ)^4319 := by
    have hnat : (26439999 : ℕ)^5343*20000000000000^4319 ≤ 1636486810743^4319*200000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26439999 200000000 1636486810743 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1421990281/2500000000 : ℝ)^5343 ≤ (1243938251301/2500000000000 : ℝ)^4319 := by
    have hnat : (1421990281 : ℕ)^5343*2500000000000^4319 ≤ 1243938251301^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421990281 2500000000 1243938251301 2500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4965420257/10000000000 : ℝ)^5343 ≤ (8412007176759/20000000000000 : ℝ)^4319 := by
    have hnat : (4965420257 : ℕ)^5343*20000000000000^4319 ≤ 8412007176759^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4965420257 10000000000 8412007176759 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26439999/200000000 : ℝ), (1421990281/2500000000 : ℝ), (4965420257/10000000000 : ℝ)] ![(1636486810743/20000000000000 : ℝ), (1243938251301/2500000000000 : ℝ), (8412007176759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26439999/200000000 : ℝ)|^5343 ≤ (1636486810743/20000000000000 : ℝ)^4319
        have hw : |(-26439999/200000000 : ℝ)|=(26439999/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1421990281/2500000000 : ℝ)|^5343 ≤ (1243938251301/2500000000000 : ℝ)^4319
        have hw : |(1421990281/2500000000 : ℝ)|=(1421990281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4965420257/10000000000 : ℝ)|^5343 ≤ (8412007176759/20000000000000 : ℝ)^4319
        have hw : |(4965420257/10000000000 : ℝ)|=(4965420257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s0_1 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400803659/10000000000 : ℝ)*x 0 + (-1712624429/10000000000 : ℝ)*x 1 + (4965420199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400803659/10000000000 : ℝ)^5343 ≤ (46668778638999/100000000000000 : ℝ)^4319 := by
    have hnat : (5400803659 : ℕ)^5343*100000000000000^4319 ≤ 46668778638999^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400803659 10000000000 46668778638999 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1712624429/10000000000 : ℝ)^5343 ≤ (11271186062447/100000000000000 : ℝ)^4319 := by
    have hnat : (1712624429 : ℕ)^5343*100000000000000^4319 ≤ 11271186062447^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712624429 10000000000 11271186062447 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4965420199/10000000000 : ℝ)^5343 ≤ (42060035276019/100000000000000 : ℝ)^4319 := by
    have hnat : (4965420199 : ℕ)^5343*100000000000000^4319 ≤ 42060035276019^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4965420199 10000000000 42060035276019 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400803659/10000000000 : ℝ), (-1712624429/10000000000 : ℝ), (4965420199/10000000000 : ℝ)] ![(46668778638999/100000000000000 : ℝ), (11271186062447/100000000000000 : ℝ), (42060035276019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400803659/10000000000 : ℝ)|^5343 ≤ (46668778638999/100000000000000 : ℝ)^4319
        have hw : |(5400803659/10000000000 : ℝ)|=(5400803659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1712624429/10000000000 : ℝ)|^5343 ≤ (11271186062447/100000000000000 : ℝ)^4319
        have hw : |(-1712624429/10000000000 : ℝ)|=(1712624429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4965420199/10000000000 : ℝ)|^5343 ≤ (42060035276019/100000000000000 : ℝ)^4319
        have hw : |(4965420199/10000000000 : ℝ)|=(4965420199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s0_2 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400803831/10000000000 : ℝ)*x 0 + (2482710181/5000000000 : ℝ)*x 1 + (-342524799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400803831/10000000000 : ℝ)^5343 ≤ (23334390238823/50000000000000 : ℝ)^4319 := by
    have hnat : (5400803831 : ℕ)^5343*50000000000000^4319 ≤ 23334390238823^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400803831 10000000000 23334390238823 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2482710181/5000000000 : ℝ)^5343 ≤ (42060036984079/100000000000000 : ℝ)^4319 := by
    have hnat : (2482710181 : ℕ)^5343*100000000000000^4319 ≤ 42060036984079^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482710181 5000000000 42060036984079 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342524799/2000000000 : ℝ)^5343 ≤ (2254236505799/20000000000000 : ℝ)^4319 := by
    have hnat : (342524799 : ℕ)^5343*20000000000000^4319 ≤ 2254236505799^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342524799 2000000000 2254236505799 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400803831/10000000000 : ℝ), (2482710181/5000000000 : ℝ), (-342524799/2000000000 : ℝ)] ![(23334390238823/50000000000000 : ℝ), (42060036984079/100000000000000 : ℝ), (2254236505799/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400803831/10000000000 : ℝ)|^5343 ≤ (23334390238823/50000000000000 : ℝ)^4319
        have hw : |(5400803831/10000000000 : ℝ)|=(5400803831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2482710181/5000000000 : ℝ)|^5343 ≤ (42060036984079/100000000000000 : ℝ)^4319
        have hw : |(2482710181/5000000000 : ℝ)|=(2482710181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-342524799/2000000000 : ℝ)|^5343 ≤ (2254236505799/20000000000000 : ℝ)^4319
        have hw : |(-342524799/2000000000 : ℝ)|=(342524799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s0_3 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (403539433/1000000000 : ℝ)*x 0 + (765527127/2500000000 : ℝ)*x 1 + (5180830893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403539433/1000000000 : ℝ)^5343 ≤ (4067754581093/12500000000000 : ℝ)^4319 := by
    have hnat : (403539433 : ℕ)^5343*12500000000000^4319 ≤ 4067754581093^4319*1000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403539433 1000000000 4067754581093 12500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (765527127/2500000000 : ℝ)^5343 ≤ (23129178511439/100000000000000 : ℝ)^4319 := by
    have hnat : (765527127 : ℕ)^5343*100000000000000^4319 ≤ 23129178511439^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765527127 2500000000 23129178511439 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180830893/10000000000 : ℝ)^5343 ≤ (2216439241443/5000000000000 : ℝ)^4319 := by
    have hnat : (5180830893 : ℕ)^5343*5000000000000^4319 ≤ 2216439241443^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180830893 10000000000 2216439241443 5000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(403539433/1000000000 : ℝ), (765527127/2500000000 : ℝ), (5180830893/10000000000 : ℝ)] ![(4067754581093/12500000000000 : ℝ), (23129178511439/100000000000000 : ℝ), (2216439241443/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(403539433/1000000000 : ℝ)|^5343 ≤ (4067754581093/12500000000000 : ℝ)^4319
        have hw : |(403539433/1000000000 : ℝ)|=(403539433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(765527127/2500000000 : ℝ)|^5343 ≤ (23129178511439/100000000000000 : ℝ)^4319
        have hw : |(765527127/2500000000 : ℝ)|=(765527127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180830893/10000000000 : ℝ)|^5343 ≤ (2216439241443/5000000000000 : ℝ)^4319
        have hw : |(5180830893/10000000000 : ℝ)|=(5180830893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s0_4 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1323594411/10000000000 : ℝ)*x 0 + (4983078569/10000000000 : ℝ)*x 1 + (2834860039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323594411/10000000000 : ℝ)^5343 ≤ (1638928885829/20000000000000 : ℝ)^4319 := by
    have hnat : (1323594411 : ℕ)^5343*20000000000000^4319 ≤ 1638928885829^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323594411 10000000000 1638928885829 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4983078569/10000000000 : ℝ)^5343 ≤ (2112257673299/5000000000000 : ℝ)^4319 := by
    have hnat : (4983078569 : ℕ)^5343*5000000000000^4319 ≤ 2112257673299^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4983078569 10000000000 2112257673299 5000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2834860039/5000000000 : ℝ)^5343 ≤ (12390050522519/25000000000000 : ℝ)^4319 := by
    have hnat : (2834860039 : ℕ)^5343*25000000000000^4319 ≤ 12390050522519^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2834860039 5000000000 12390050522519 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1323594411/10000000000 : ℝ), (4983078569/10000000000 : ℝ), (2834860039/5000000000 : ℝ)] ![(1638928885829/20000000000000 : ℝ), (2112257673299/5000000000000 : ℝ), (12390050522519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1323594411/10000000000 : ℝ)|^5343 ≤ (1638928885829/20000000000000 : ℝ)^4319
        have hw : |(-1323594411/10000000000 : ℝ)|=(1323594411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4983078569/10000000000 : ℝ)|^5343 ≤ (2112257673299/5000000000000 : ℝ)^4319
        have hw : |(4983078569/10000000000 : ℝ)|=(4983078569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2834860039/5000000000 : ℝ)|^5343 ≤ (12390050522519/25000000000000 : ℝ)^4319
        have hw : |(2834860039/5000000000 : ℝ)|=(2834860039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s0_5 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5205214573/10000000000 : ℝ)*x 0 + (-1008324141/10000000000 : ℝ)*x 1 + (2834859791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5205214573/10000000000 : ℝ)^5343 ≤ (44587028438091/100000000000000 : ℝ)^4319 := by
    have hnat : (5205214573 : ℕ)^5343*100000000000000^4319 ≤ 44587028438091^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205214573 10000000000 44587028438091 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008324141/10000000000 : ℝ)^5343 ≤ (5852774824307/100000000000000 : ℝ)^4319 := by
    have hnat : (1008324141 : ℕ)^5343*100000000000000^4319 ≤ 5852774824307^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008324141 10000000000 5852774824307 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2834859791/5000000000 : ℝ)^5343 ≤ (49560196726491/100000000000000 : ℝ)^4319 := by
    have hnat : (2834859791 : ℕ)^5343*100000000000000^4319 ≤ 49560196726491^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2834859791 5000000000 49560196726491 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5205214573/10000000000 : ℝ), (-1008324141/10000000000 : ℝ), (2834859791/5000000000 : ℝ)] ![(44587028438091/100000000000000 : ℝ), (5852774824307/100000000000000 : ℝ), (49560196726491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5205214573/10000000000 : ℝ)|^5343 ≤ (44587028438091/100000000000000 : ℝ)^4319
        have hw : |(5205214573/10000000000 : ℝ)|=(5205214573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1008324141/10000000000 : ℝ)|^5343 ≤ (5852774824307/100000000000000 : ℝ)^4319
        have hw : |(-1008324141/10000000000 : ℝ)|=(1008324141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2834859791/5000000000 : ℝ)|^5343 ≤ (49560196726491/100000000000000 : ℝ)^4319
        have hw : |(2834859791/5000000000 : ℝ)|=(2834859791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s0_6 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5205214219/10000000000 : ℝ)*x 0 + (1133943987/2000000000 : ℝ)*x 1 + (-1008324131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5205214219/10000000000 : ℝ)^5343 ≤ (44587024686849/100000000000000 : ℝ)^4319 := by
    have hnat : (5205214219 : ℕ)^5343*100000000000000^4319 ≤ 44587024686849^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205214219 10000000000 44587024686849 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133943987/2000000000 : ℝ)^5343 ≤ (1239005013593/2500000000000 : ℝ)^4319 := by
    have hnat : (1133943987 : ℕ)^5343*2500000000000^4319 ≤ 1239005013593^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133943987 2000000000 1239005013593 2500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008324131/10000000000 : ℝ)^5343 ≤ (5852774752501/100000000000000 : ℝ)^4319 := by
    have hnat : (1008324131 : ℕ)^5343*100000000000000^4319 ≤ 5852774752501^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008324131 10000000000 5852774752501 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5205214219/10000000000 : ℝ), (1133943987/2000000000 : ℝ), (-1008324131/10000000000 : ℝ)] ![(44587024686849/100000000000000 : ℝ), (1239005013593/2500000000000 : ℝ), (5852774752501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5205214219/10000000000 : ℝ)|^5343 ≤ (44587024686849/100000000000000 : ℝ)^4319
        have hw : |(5205214219/10000000000 : ℝ)|=(5205214219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133943987/2000000000 : ℝ)|^5343 ≤ (1239005013593/2500000000000 : ℝ)^4319
        have hw : |(1133943987/2000000000 : ℝ)|=(1133943987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008324131/10000000000 : ℝ)|^5343 ≤ (5852774752501/100000000000000 : ℝ)^4319
        have hw : |(-1008324131/10000000000 : ℝ)|=(1008324131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s0_7 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (505008391/1250000000 : ℝ)*x 0 + (2564525083/5000000000 : ℝ)*x 1 + (389449427/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505008391/1250000000 : ℝ)^5343 ≤ (32588659338169/100000000000000 : ℝ)^4319 := by
    have hnat : (505008391 : ℕ)^5343*100000000000000^4319 ≤ 32588659338169^4319*1250000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505008391 1250000000 32588659338169 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564525083/5000000000 : ℝ)^5343 ≤ (43781340024281/100000000000000 : ℝ)^4319 := by
    have hnat : (2564525083 : ℕ)^5343*100000000000000^4319 ≤ 43781340024281^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564525083 5000000000 43781340024281 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389449427/1250000000 : ℝ)^5343 ≤ (5907500155827/25000000000000 : ℝ)^4319 := by
    have hnat : (389449427 : ℕ)^5343*25000000000000^4319 ≤ 5907500155827^4319*1250000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389449427 1250000000 5907500155827 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(505008391/1250000000 : ℝ), (2564525083/5000000000 : ℝ), (389449427/1250000000 : ℝ)] ![(32588659338169/100000000000000 : ℝ), (43781340024281/100000000000000 : ℝ), (5907500155827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(505008391/1250000000 : ℝ)|^5343 ≤ (32588659338169/100000000000000 : ℝ)^4319
        have hw : |(505008391/1250000000 : ℝ)|=(505008391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564525083/5000000000 : ℝ)|^5343 ≤ (43781340024281/100000000000000 : ℝ)^4319
        have hw : |(2564525083/5000000000 : ℝ)|=(2564525083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(389449427/1250000000 : ℝ)|^5343 ≤ (5907500155827/25000000000000 : ℝ)^4319
        have hw : |(389449427/1250000000 : ℝ)|=(389449427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1715_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3097/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4347/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5335/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5335 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5335*1^1024 ≤ 0^1024*1^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5335/1024 : ℝ) ≤ (52799294151117599/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5335 ≤ (52799294151117599/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5335*6250000000000000000^1024 ≤ 52799294151117599^1024*5^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 52799294151117599 6250000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (52799294151117599/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5335 := by
      have hnat : (1 : ℕ)^1024*1^5335 ≤ 1^5335*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6302799294151117599/6250000000000000000 : ℝ) ≤ (10016159811526711/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (6302799294151117599/6250000000000000000 : ℝ)^1024 ≤ (10016159811526711/10000000000000000 : ℝ)^5335 := by
      have hnat : (6302799294151117599 : ℕ)^1024*10000000000000000^5335 ≤ 10016159811526711^5335*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6302799294151117599 6250000000000000000 10016159811526711 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016159811526711/10000000000000000 : ℝ)) (X := (6302799294151117599/6250000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3177799294151117599/3125000000000000000 : ℝ) ≤ (5016159811526711/5000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (3177799294151117599/3125000000000000000 : ℝ)^1024 ≤ (5016159811526711/5000000000000000 : ℝ)^5335 := by
      have hnat : (3177799294151117599 : ℕ)^1024*5000000000000000^5335 ≤ 5016159811526711^5335*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3177799294151117599 3125000000000000000 5016159811526711 5000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5016159811526711/5000000000000000 : ℝ)) (X := (3177799294151117599/3125000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(16159811526711/4000000000000000 : ℝ)*(0 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16159811526711/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(52799294151117599/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(16159811526711/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5335/1024 : ℝ) := by
    rw [show (1 : ℝ)+(16159811526711/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10016159811526711/10000000000000000 : ℝ) by norm_num, show 1+(52799294151117599/6250000000000000000 : ℝ)+(0 : ℝ)=(6302799294151117599/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(52799294151117599/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(16159811526711/4000000000000000 : ℝ)*(2/5 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(16159811526711/4000000000000000 : ℝ)*(2/5 : ℝ)=(5016159811526711/5000000000000000 : ℝ) by norm_num, show 1+2*(52799294151117599/6250000000000000000 : ℝ)=(3177799294151117599/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(16159811526711/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16159811526711/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(16159811526711/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16159811526711/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(16159811526711/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (16159811526711/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-26439999/200000000 : ℝ)*X 0 0+(1421990281/2500000000 : ℝ)*X 0 1+(4965420257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5400803659/10000000000 : ℝ)*X 1 0+(-1712624429/10000000000 : ℝ)*X 1 1+(4965420199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5400803831/10000000000 : ℝ)*X 2 0+(2482710181/5000000000 : ℝ)*X 2 1+(-342524799/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((403539433/1000000000 : ℝ)*X 0 0+(765527127/2500000000 : ℝ)*X 0 1+(5180830893/10000000000 : ℝ)*X 0 2+(403539433/1000000000 : ℝ)*X 1 0+(765527127/2500000000 : ℝ)*X 1 1+(5180830893/10000000000 : ℝ)*X 1 2+(403539433/1000000000 : ℝ)*X 2 0+(765527127/2500000000 : ℝ)*X 2 1+(5180830893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1323594411/10000000000 : ℝ)*X 0 0+(4983078569/10000000000 : ℝ)*X 0 1+(2834860039/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5205214573/10000000000 : ℝ)*X 1 0+(-1008324141/10000000000 : ℝ)*X 1 1+(2834859791/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5205214219/10000000000 : ℝ)*X 2 0+(1133943987/2000000000 : ℝ)*X 2 1+(-1008324131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((505008391/1250000000 : ℝ)*X 0 0+(2564525083/5000000000 : ℝ)*X 0 1+(389449427/1250000000 : ℝ)*X 0 2+(505008391/1250000000 : ℝ)*X 1 0+(2564525083/5000000000 : ℝ)*X 1 1+(389449427/1250000000 : ℝ)*X 1 2+(505008391/1250000000 : ℝ)*X 2 0+(2564525083/5000000000 : ℝ)*X 2 1+(389449427/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (638751241086761191845423/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41623509/100000000000000 : ℝ)*(base1) + (548387611/50000000000000 : ℝ)*(base19) + (570426039/50000000000000 : ℝ)*(base23) + (1371173/2000000000000 : ℝ)*(upper3) + (255833987/100000000000000 : ℝ)*(upper5) + (464000414556131/50000000000000 : ℝ)*(major0) + (464000414556131/50000000000000 : ℝ)*(major1) + (464000414556131/50000000000000 : ℝ)*(major2) + (1384008926867113/100000000000000 : ℝ)*(sp0) + (1384014247741323/100000000000000 : ℝ)*(sp1) + (1384014203664467/100000000000000 : ℝ)*(sp2) + (471984550916031/100000000000000 : ℝ)*(sp3) + (6459272941/100000000000000 : ℝ)*(sp4) + (301650271/20000000000000 : ℝ)*(sp7) + (94397220158179/20000000000000 : ℝ)*(f.failure) + (276803068903309/20000000000000 : ℝ)*(f.sum) + (145533958415141/100000000000000000000000000000 : ℝ)*base65 + (462605891515141/200000000000000000000000000000 : ℝ)*base67 + (1546727845084859/200000000000000000000000000000 : ℝ)*base70 + (680670190084859/200000000000000000000000000000 : ℝ)*base72 + (587343804215141/100000000000000000000000000000 : ℝ)*base73 + (1155541012684859/200000000000000000000000000000 : ℝ)*base76 + (254324634084859/200000000000000000000000000000 : ℝ)*base78 + (1133566231084859/200000000000000000000000000000 : ℝ)*base80 + (107242354484859/100000000000000000000000000000 : ℝ)*base82 + (723633/400000000000000000000 : ℝ)*base89 + (723633/400000000000000000000 : ℝ)*base91 + (723633/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (727470544967085130374867/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (751565137/50000000000000 : ℝ)*(base19) + (1659972997/100000000000000 : ℝ)*(base23) + (122678941/100000000000000 : ℝ)*(upper2) + (28259287/12500000000000 : ℝ)*(upper3) + (122864129/50000000000000 : ℝ)*(upper5) + (976510924134999/100000000000000 : ℝ)*(major0) + (976510924134999/100000000000000 : ℝ)*(major1) + (976510924134999/100000000000000 : ℝ)*(major2) + (5006218381/100000000000000 : ℝ)*(sp1) + (5543874519/100000000000000 : ℝ)*(sp2) + (14563631368563/1000000000000 : ℝ)*(sp4) + (291271325501529/20000000000000 : ℝ)*(sp5) + (91022245813049/6250000000000 : ℝ)*(sp6) + (124164647542151/25000000000000 : ℝ)*(sp7) + (124164647542151/25000000000000 : ℝ)*(f.failure) + (14563631368563/1000000000000 : ℝ)*(f.sum) + (873894743941711/200000000000000000000000000000 : ℝ)*base66 + (416958072858289/400000000000000000000000000000 : ℝ)*base67 + (287562992858289/400000000000000000000000000000 : ℝ)*base69 + (1056160868058289/400000000000000000000000000000 : ℝ)*base71 + (1030152915541711/200000000000000000000000000000 : ℝ)*base74 + (918406669258289/400000000000000000000000000000 : ℝ)*base75 + (2322405260341711/400000000000000000000000000000 : ℝ)*base78 + (2165825985658289/400000000000000000000000000000 : ℝ)*base79 + (520086572541711/200000000000000000000000000000 : ℝ)*base82 + (841277/500000000000000000000 : ℝ)*base89 + (841277/500000000000000000000 : ℝ)*base91 + (841277/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1715_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3097/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4347/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1715_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1715_s1_0 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1390962569/10000000000 : ℝ)*x 0 + (2740103389/5000000000 : ℝ)*x 1 + (1281928861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1390962569/10000000000 : ℝ)^5343 ≤ (8713697062303/100000000000000 : ℝ)^4319 := by
    have hnat : (1390962569 : ℕ)^5343*100000000000000^4319 ≤ 8713697062303^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390962569 10000000000 8713697062303 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2740103389/5000000000 : ℝ)^5343 ≤ (2969941051023/6250000000000 : ℝ)^4319 := by
    have hnat : (2740103389 : ℕ)^5343*6250000000000^4319 ≤ 2969941051023^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740103389 5000000000 2969941051023 6250000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1281928861/2500000000 : ℝ)^5343 ≤ (4376724611429/10000000000000 : ℝ)^4319 := by
    have hnat : (1281928861 : ℕ)^5343*10000000000000^4319 ≤ 4376724611429^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281928861 2500000000 4376724611429 10000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1390962569/10000000000 : ℝ), (2740103389/5000000000 : ℝ), (1281928861/2500000000 : ℝ)] ![(8713697062303/100000000000000 : ℝ), (2969941051023/6250000000000 : ℝ), (4376724611429/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1390962569/10000000000 : ℝ)|^5343 ≤ (8713697062303/100000000000000 : ℝ)^4319
        have hw : |(-1390962569/10000000000 : ℝ)|=(1390962569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2740103389/5000000000 : ℝ)|^5343 ≤ (2969941051023/6250000000000 : ℝ)^4319
        have hw : |(2740103389/5000000000 : ℝ)|=(2740103389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1281928861/2500000000 : ℝ)|^5343 ≤ (4376724611429/10000000000000 : ℝ)^4319
        have hw : |(1281928861/2500000000 : ℝ)|=(1281928861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s1_1 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345467129/10000000000 : ℝ)*x 0 + (-1574147807/10000000000 : ℝ)*x 1 + (5127714427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345467129/10000000000 : ℝ)^5343 ≤ (11519490494879/25000000000000 : ℝ)^4319 := by
    have hnat : (5345467129 : ℕ)^5343*25000000000000^4319 ≤ 11519490494879^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345467129 10000000000 11519490494879 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1574147807/10000000000 : ℝ)^5343 ≤ (10154802636949/100000000000000 : ℝ)^4319 := by
    have hnat : (1574147807 : ℕ)^5343*100000000000000^4319 ≤ 10154802636949^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574147807 10000000000 10154802636949 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127714427/10000000000 : ℝ)^5343 ≤ (10941808843919/25000000000000 : ℝ)^4319 := by
    have hnat : (5127714427 : ℕ)^5343*25000000000000^4319 ≤ 10941808843919^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127714427 10000000000 10941808843919 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345467129/10000000000 : ℝ), (-1574147807/10000000000 : ℝ), (5127714427/10000000000 : ℝ)] ![(11519490494879/25000000000000 : ℝ), (10154802636949/100000000000000 : ℝ), (10941808843919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345467129/10000000000 : ℝ)|^5343 ≤ (11519490494879/25000000000000 : ℝ)^4319
        have hw : |(5345467129/10000000000 : ℝ)|=(5345467129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1574147807/10000000000 : ℝ)|^5343 ≤ (10154802636949/100000000000000 : ℝ)^4319
        have hw : |(-1574147807/10000000000 : ℝ)|=(1574147807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127714427/10000000000 : ℝ)|^5343 ≤ (10941808843919/25000000000000 : ℝ)^4319
        have hw : |(5127714427/10000000000 : ℝ)|=(5127714427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s1_2 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672732907/5000000000 : ℝ)*x 0 + (5127715503/10000000000 : ℝ)*x 1 + (-78707407/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672732907/5000000000 : ℝ)^5343 ≤ (23038973978349/50000000000000 : ℝ)^4319 := by
    have hnat : (2672732907 : ℕ)^5343*50000000000000^4319 ≤ 23038973978349^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672732907 5000000000 23038973978349 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127715503/10000000000 : ℝ)^5343 ≤ (43767246737277/100000000000000 : ℝ)^4319 := by
    have hnat : (5127715503 : ℕ)^5343*100000000000000^4319 ≤ 43767246737277^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127715503 10000000000 43767246737277 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78707407/500000000 : ℝ)^5343 ≤ (5077402647221/50000000000000 : ℝ)^4319 := by
    have hnat : (78707407 : ℕ)^5343*50000000000000^4319 ≤ 5077402647221^4319*500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78707407 500000000 5077402647221 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672732907/5000000000 : ℝ), (5127715503/10000000000 : ℝ), (-78707407/500000000 : ℝ)] ![(23038973978349/50000000000000 : ℝ), (43767246737277/100000000000000 : ℝ), (5077402647221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672732907/5000000000 : ℝ)|^5343 ≤ (23038973978349/50000000000000 : ℝ)^4319
        have hw : |(2672732907/5000000000 : ℝ)|=(2672732907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127715503/10000000000 : ℝ)|^5343 ≤ (43767246737277/100000000000000 : ℝ)^4319
        have hw : |(5127715503/10000000000 : ℝ)|=(5127715503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78707407/500000000 : ℝ)|^5343 ≤ (5077402647221/50000000000000 : ℝ)^4319
        have hw : |(-78707407/500000000 : ℝ)|=(78707407/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s1_3 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4095825059/10000000000 : ℝ)*x 0 + (224960231/625000000 : ℝ)*x 1 + (289561209/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4095825059/10000000000 : ℝ)^5343 ≤ (16572982861831/50000000000000 : ℝ)^4319 := by
    have hnat : (4095825059 : ℕ)^5343*50000000000000^4319 ≤ 16572982861831^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4095825059 10000000000 16572982861831 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224960231/625000000 : ℝ)^5343 ≤ (225995830091/800000000000 : ℝ)^4319 := by
    have hnat : (224960231 : ℕ)^5343*800000000000^4319 ≤ 225995830091^4319*625000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224960231 625000000 225995830091 800000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289561209/625000000 : ℝ)^5343 ≤ (38604555497469/100000000000000 : ℝ)^4319 := by
    have hnat : (289561209 : ℕ)^5343*100000000000000^4319 ≤ 38604555497469^4319*625000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289561209 625000000 38604555497469 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4095825059/10000000000 : ℝ), (224960231/625000000 : ℝ), (289561209/625000000 : ℝ)] ![(16572982861831/50000000000000 : ℝ), (225995830091/800000000000 : ℝ), (38604555497469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4095825059/10000000000 : ℝ)|^5343 ≤ (16572982861831/50000000000000 : ℝ)^4319
        have hw : |(4095825059/10000000000 : ℝ)|=(4095825059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224960231/625000000 : ℝ)|^5343 ≤ (225995830091/800000000000 : ℝ)^4319
        have hw : |(224960231/625000000 : ℝ)|=(224960231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(289561209/625000000 : ℝ)|^5343 ≤ (38604555497469/100000000000000 : ℝ)^4319
        have hw : |(289561209/625000000 : ℝ)|=(289561209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s1_4 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-10868341/78125000 : ℝ)*x 0 + (641490753/1250000000 : ℝ)*x 1 + (1368981883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10868341/78125000 : ℝ)^5343 ≤ (2178782851293/25000000000000 : ℝ)^4319 := by
    have hnat : (10868341 : ℕ)^5343*25000000000000^4319 ≤ 2178782851293^4319*78125000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10868341 78125000 2178782851293 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641490753/1250000000 : ℝ)^5343 ≤ (43811710414599/100000000000000 : ℝ)^4319 := by
    have hnat : (641490753 : ℕ)^5343*100000000000000^4319 ≤ 43811710414599^4319*1250000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641490753 1250000000 43811710414599 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368981883/2500000000 : ℝ)^5343 ≤ (9494631633977/20000000000000 : ℝ)^4319 := by
    have hnat : (1368981883 : ℕ)^5343*20000000000000^4319 ≤ 9494631633977^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368981883 2500000000 9494631633977 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10868341/78125000 : ℝ), (641490753/1250000000 : ℝ), (1368981883/2500000000 : ℝ)] ![(2178782851293/25000000000000 : ℝ), (43811710414599/100000000000000 : ℝ), (9494631633977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10868341/78125000 : ℝ)|^5343 ≤ (2178782851293/25000000000000 : ℝ)^4319
        have hw : |(-10868341/78125000 : ℝ)|=(10868341/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641490753/1250000000 : ℝ)|^5343 ≤ (43811710414599/100000000000000 : ℝ)^4319
        have hw : |(641490753/1250000000 : ℝ)|=(641490753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368981883/2500000000 : ℝ)|^5343 ≤ (9494631633977/20000000000000 : ℝ)^4319
        have hw : |(1368981883/2500000000 : ℝ)|=(1368981883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s1_5 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251075693/10000000000 : ℝ)*x 0 + (-612967611/5000000000 : ℝ)*x 1 + (5475927141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251075693/10000000000 : ℝ)^5343 ≤ (9014702557927/20000000000000 : ℝ)^4319 := by
    have hnat : (5251075693 : ℕ)^5343*20000000000000^4319 ≤ 9014702557927^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251075693 10000000000 9014702557927 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (612967611/5000000000 : ℝ)^5343 ≤ (7453333224987/100000000000000 : ℝ)^4319 := by
    have hnat : (612967611 : ℕ)^5343*100000000000000^4319 ≤ 7453333224987^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612967611 5000000000 7453333224987 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475927141/10000000000 : ℝ)^5343 ≤ (47473153976457/100000000000000 : ℝ)^4319 := by
    have hnat : (5475927141 : ℕ)^5343*100000000000000^4319 ≤ 47473153976457^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475927141 10000000000 47473153976457 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251075693/10000000000 : ℝ), (-612967611/5000000000 : ℝ), (5475927141/10000000000 : ℝ)] ![(9014702557927/20000000000000 : ℝ), (7453333224987/100000000000000 : ℝ), (47473153976457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251075693/10000000000 : ℝ)|^5343 ≤ (9014702557927/20000000000000 : ℝ)^4319
        have hw : |(5251075693/10000000000 : ℝ)|=(5251075693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-612967611/5000000000 : ℝ)|^5343 ≤ (7453333224987/100000000000000 : ℝ)^4319
        have hw : |(-612967611/5000000000 : ℝ)|=(612967611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475927141/10000000000 : ℝ)|^5343 ≤ (47473153976457/100000000000000 : ℝ)^4319
        have hw : |(5475927141/10000000000 : ℝ)|=(5475927141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s1_6 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625537999/5000000000 : ℝ)*x 0 + (273796339/500000000 : ℝ)*x 1 + (-612967653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625537999/5000000000 : ℝ)^5343 ≤ (45073516028367/100000000000000 : ℝ)^4319 := by
    have hnat : (2625537999 : ℕ)^5343*100000000000000^4319 ≤ 45073516028367^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625537999 5000000000 45073516028367 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273796339/500000000 : ℝ)^5343 ≤ (5934143763097/12500000000000 : ℝ)^4319 := by
    have hnat : (273796339 : ℕ)^5343*12500000000000^4319 ≤ 5934143763097^4319*500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273796339 500000000 5934143763097 12500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (612967653/5000000000 : ℝ)^5343 ≤ (1863333464191/25000000000000 : ℝ)^4319 := by
    have hnat : (612967653 : ℕ)^5343*25000000000000^4319 ≤ 1863333464191^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612967653 5000000000 1863333464191 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625537999/5000000000 : ℝ), (273796339/500000000 : ℝ), (-612967653/5000000000 : ℝ)] ![(45073516028367/100000000000000 : ℝ), (5934143763097/12500000000000 : ℝ), (1863333464191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625537999/5000000000 : ℝ)|^5343 ≤ (45073516028367/100000000000000 : ℝ)^4319
        have hw : |(2625537999/5000000000 : ℝ)|=(2625537999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273796339/500000000 : ℝ)|^5343 ≤ (5934143763097/12500000000000 : ℝ)^4319
        have hw : |(273796339/500000000 : ℝ)|=(273796339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-612967653/5000000000 : ℝ)|^5343 ≤ (1863333464191/25000000000000 : ℝ)^4319
        have hw : |(-612967653/5000000000 : ℝ)|=(612967653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s1_7 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4096363447/10000000000 : ℝ)*x 0 + (92412627/200000000 : ℝ)*x 1 + (3611908841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4096363447/10000000000 : ℝ)^5343 ≤ (16575677890511/50000000000000 : ℝ)^4319 := by
    have hnat : (4096363447 : ℕ)^5343*50000000000000^4319 ≤ 16575677890511^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4096363447 10000000000 16575677890511 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92412627/200000000 : ℝ)^5343 ≤ (19238655466337/50000000000000 : ℝ)^4319 := by
    have hnat : (92412627 : ℕ)^5343*50000000000000^4319 ≤ 19238655466337^4319*200000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92412627 200000000 19238655466337 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3611908841/10000000000 : ℝ)^5343 ≤ (5674266654263/20000000000000 : ℝ)^4319 := by
    have hnat : (3611908841 : ℕ)^5343*20000000000000^4319 ≤ 5674266654263^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3611908841 10000000000 5674266654263 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4096363447/10000000000 : ℝ), (92412627/200000000 : ℝ), (3611908841/10000000000 : ℝ)] ![(16575677890511/50000000000000 : ℝ), (19238655466337/50000000000000 : ℝ), (5674266654263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4096363447/10000000000 : ℝ)|^5343 ≤ (16575677890511/50000000000000 : ℝ)^4319
        have hw : |(4096363447/10000000000 : ℝ)|=(4096363447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(92412627/200000000 : ℝ)|^5343 ≤ (19238655466337/50000000000000 : ℝ)^4319
        have hw : |(92412627/200000000 : ℝ)|=(92412627/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3611908841/10000000000 : ℝ)|^5343 ≤ (5674266654263/20000000000000 : ℝ)^4319
        have hw : |(3611908841/10000000000 : ℝ)|=(3611908841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1715_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4347/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3097/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4903/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8669/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4347/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3097/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4347/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3097/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4347/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3097/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4347/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3097/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4347/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3097/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4347/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3097/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3097/50000 : ℝ) ^ (5335/1024 : ℝ) ≤ (50841358429309/100000000000000000000 : ℝ) := by
    have hpowers : (3097/50000 : ℝ)^5335 ≤ (50841358429309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^5335*100000000000000000000^1024 ≤ 50841358429309^1024*50000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 50000 50841358429309 100000000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/50000 : ℝ)) (X := (50841358429309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4347/20000 : ℝ) ^ (5335/1024 : ℝ) ≤ (35206888120636399/100000000000000000000 : ℝ) := by
    have hpowers : (4347/20000 : ℝ)^5335 ≤ (35206888120636399/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4347 : ℕ)^5335*100000000000000000000^1024 ≤ 35206888120636399^1024*20000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4347 20000 35206888120636399 100000000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4347/20000 : ℝ)) (X := (35206888120636399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000050841358429309/50000000000000000000 : ℝ) ≤ (10000001951697457/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (50000050841358429309/50000000000000000000 : ℝ)^1024 ≤ (10000001951697457/10000000000000000 : ℝ)^5335 := by
      have hnat : (50000050841358429309 : ℕ)^1024*10000000000000000^5335 ≤ 10000001951697457^5335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000050841358429309 50000000000000000000 10000001951697457 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001951697457/10000000000000000 : ℝ)) (X := (50000050841358429309/50000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008814432369766427/25000000000000000000 : ℝ) ≤ (2000135328108759/2000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (25008814432369766427/25000000000000000000 : ℝ)^1024 ≤ (2000135328108759/2000000000000000 : ℝ)^5335 := by
      have hnat : (25008814432369766427 : ℕ)^1024*2000000000000000^5335 ≤ 2000135328108759^5335*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008814432369766427 25000000000000000000 2000135328108759 2000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000135328108759/2000000000000000 : ℝ)) (X := (25008814432369766427/25000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035206888120636399/50000000000000000000 : ℝ) ≤ (10001351329390133/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (50035206888120636399/50000000000000000000 : ℝ)^1024 ≤ (10001351329390133/10000000000000000 : ℝ)^5335 := by
      have hnat : (50035206888120636399 : ℕ)^1024*10000000000000000^5335 ≤ 10001351329390133^5335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035206888120636399 50000000000000000000 10001351329390133 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001351329390133/10000000000000000 : ℝ)) (X := (50035206888120636399/50000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(50841358429309/100000000000000000000 : ℝ) ≤ ((155401672285901744093/155410000000000000000 : ℝ)+2*(337344423169/777050000000000 : ℝ)*(3097/50000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (155401672285901744093/155410000000000000000 : ℝ)+2*(337344423169/777050000000000 : ℝ)*(3097/50000 : ℝ)=(10000001951697457/10000000000000000 : ℝ) by norm_num, show 1+2*(50841358429309/100000000000000000000 : ℝ)=(50000050841358429309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35206888120636399/100000000000000000000 : ℝ)+(50841358429309/100000000000000000000 : ℝ) ≤ ((155401672285901744093/155410000000000000000 : ℝ)+(337344423169/777050000000000 : ℝ)*((4347/20000 : ℝ)+(3097/50000 : ℝ)))^(5335/1024 : ℝ) := by
    rw [show (155401672285901744093/155410000000000000000 : ℝ)+(337344423169/777050000000000 : ℝ)*((4347/20000 : ℝ)+(3097/50000 : ℝ))=(2000135328108759/2000000000000000 : ℝ) by norm_num, show 1+(35206888120636399/100000000000000000000 : ℝ)+(50841358429309/100000000000000000000 : ℝ)=(25008814432369766427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35206888120636399/100000000000000000000 : ℝ) ≤ ((155401672285901744093/155410000000000000000 : ℝ)+2*(337344423169/777050000000000 : ℝ)*(4347/20000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (155401672285901744093/155410000000000000000 : ℝ)+2*(337344423169/777050000000000 : ℝ)*(4347/20000 : ℝ)=(10001351329390133/10000000000000000 : ℝ) by norm_num, show 1+2*(35206888120636399/100000000000000000000 : ℝ)=(50035206888120636399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (155401672285901744093/155410000000000000000 : ℝ)*(X 1 0+X 2 0)+(337344423169/777050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (3097/50000 : ℝ)) (hi := (4347/20000 : ℝ)) (c := (155401672285901744093/155410000000000000000 : ℝ)) (alpha := (337344423169/777050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (155401672285901744093/155410000000000000000 : ℝ)*(X 0 1+X 2 1)+(337344423169/777050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (3097/50000 : ℝ)) (hi := (4347/20000 : ℝ)) (c := (155401672285901744093/155410000000000000000 : ℝ)) (alpha := (337344423169/777050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (155401672285901744093/155410000000000000000 : ℝ)*(X 0 2+X 1 2)+(337344423169/777050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (3097/50000 : ℝ)) (hi := (4347/20000 : ℝ)) (c := (155401672285901744093/155410000000000000000 : ℝ)) (alpha := (337344423169/777050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1390962569/10000000000 : ℝ)*X 0 0+(2740103389/5000000000 : ℝ)*X 0 1+(1281928861/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345467129/10000000000 : ℝ)*X 1 0+(-1574147807/10000000000 : ℝ)*X 1 1+(5127714427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672732907/5000000000 : ℝ)*X 2 0+(5127715503/10000000000 : ℝ)*X 2 1+(-78707407/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4095825059/10000000000 : ℝ)*X 0 0+(224960231/625000000 : ℝ)*X 0 1+(289561209/625000000 : ℝ)*X 0 2+(4095825059/10000000000 : ℝ)*X 1 0+(224960231/625000000 : ℝ)*X 1 1+(289561209/625000000 : ℝ)*X 1 2+(4095825059/10000000000 : ℝ)*X 2 0+(224960231/625000000 : ℝ)*X 2 1+(289561209/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-10868341/78125000 : ℝ)*X 0 0+(641490753/1250000000 : ℝ)*X 0 1+(1368981883/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251075693/10000000000 : ℝ)*X 1 0+(-612967611/5000000000 : ℝ)*X 1 1+(5475927141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625537999/5000000000 : ℝ)*X 2 0+(273796339/500000000 : ℝ)*X 2 1+(-612967653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4096363447/10000000000 : ℝ)*X 0 0+(92412627/200000000 : ℝ)*X 0 1+(3611908841/10000000000 : ℝ)*X 0 2+(4096363447/10000000000 : ℝ)*X 1 0+(92412627/200000000 : ℝ)*X 1 1+(3611908841/10000000000 : ℝ)*X 1 2+(4096363447/10000000000 : ℝ)*X 2 0+(92412627/200000000 : ℝ)*X 2 1+(3611908841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34406085830400255735208525629/3885250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (883950689/100000000000000 : ℝ)*(base19) + (1116283/25000000000000 : ℝ)*(base23) + (161528001/100000000000000 : ℝ)*(lower2) + (19792801/50000000000000 : ℝ)*(upper3) + (108087317/100000000000000 : ℝ)*(lower4) + (1902217706021349/100000000000000 : ℝ)*(major0) + (1902217706021349/100000000000000 : ℝ)*(major1) + (1902217706021349/100000000000000 : ℝ)*(major2) + (354619280552321/12500000000000 : ℝ)*(sp0) + (141847815321369/5000000000000 : ℝ)*(sp1) + (2836952564062631/100000000000000 : ℝ)*(sp2) + (9674779264791/1000000000000 : ℝ)*(sp3) + (2945959501/100000000000000 : ℝ)*(sp4) + (4621850307/100000000000000 : ℝ)*(sp6) + (9674779264791/1000000000000 : ℝ)*(f.failure) + (283695719037807/10000000000000 : ℝ)*(f.sum) + (301222361748831/38852500000000000000000000000 : ℝ)*base65 + (126783434167340841457/15541000000000000000000000000000000 : ℝ)*base67 + (43723089550904841457/15541000000000000000000000000000000 : ℝ)*base69 + (169278785098268841457/15541000000000000000000000000000000 : ℝ)*base71 + (16094393228869/38852500000000000000000000000 : ℝ)*base74 + (80447008155928841457/15541000000000000000000000000000000 : ℝ)*base75 + (150840383222268841457/15541000000000000000000000000000000 : ℝ)*base77 + (13700708529084158543/15541000000000000000000000000000000 : ℝ)*base80 + (2342040693557/19426250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (199443/20000000000000000000 : ℝ)*base90 + (199443/20000000000000000000 : ℝ)*base92 + (199443/20000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6268323017406599090511302829/971312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50894971/3125000000000 : ℝ)*(base19) + (1060612011/50000000000000 : ℝ)*(base23) + (41104701/25000000000000 : ℝ)*(upper2) + (42330179/20000000000000 : ℝ)*(upper3) + (154995193/50000000000000 : ℝ)*(upper5) + (487289542305451/25000000000000 : ℝ)*(major0) + (487289542305451/25000000000000 : ℝ)*(major1) + (487289542305451/25000000000000 : ℝ)*(major2) + (5908672731/50000000000000 : ℝ)*(sp1) + (620430087/5000000000000 : ℝ)*(sp2) + (581392806093793/20000000000000 : ℝ)*(sp4) + (290695058448443/10000000000000 : ℝ)*(sp5) + (2906949500643203/100000000000000 : ℝ)*(sp6) + (991352092859421/100000000000000 : ℝ)*(sp7) + (991352092859421/100000000000000 : ℝ)*(f.failure) + (581392806093793/20000000000000 : ℝ)*(f.sum) + (179299971288517/77705000000000000000000000000 : ℝ)*base65 + (438174456842749057/3885250000000000000000000000000000 : ℝ)*base68 + (10451597931760499057/3885250000000000000000000000000000 : ℝ)*base70 + (11765501418683999057/3885250000000000000000000000000000 : ℝ)*base72 + (42791475867159/9713125000000000000000000000 : ℝ)*base73 + (6044200219868500943/3885250000000000000000000000000000 : ℝ)*base75 + (411943700435499057/3885250000000000000000000000000000 : ℝ)*base78 + (19381124222442749057/3885250000000000000000000000000000 : ℝ)*base80 + (92233350159063/77705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (11071567/2000000000000000000000 : ℝ)*base89 + (11071567/2000000000000000000000 : ℝ)*base91 + (11071567/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1715_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4347/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3097/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4903/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8669/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1715_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1715_s2_0 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1394099947/10000000000 : ℝ)*x 0 + (1366823723/2500000000 : ℝ)*x 1 + (321157677/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1394099947/10000000000 : ℝ)^5343 ≤ (4369008763621/50000000000000 : ℝ)^4319 := by
    have hnat : (1394099947 : ℕ)^5343*50000000000000^4319 ≤ 4369008763621^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394099947 10000000000 4369008763621 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366823723/2500000000 : ℝ)^5343 ≤ (9476118291921/20000000000000 : ℝ)^4319 := by
    have hnat : (1366823723 : ℕ)^5343*20000000000000^4319 ≤ 9476118291921^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366823723 2500000000 9476118291921 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321157677/625000000 : ℝ)^5343 ≤ (21940695499809/50000000000000 : ℝ)^4319 := by
    have hnat : (321157677 : ℕ)^5343*50000000000000^4319 ≤ 21940695499809^4319*625000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321157677 625000000 21940695499809 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1394099947/10000000000 : ℝ), (1366823723/2500000000 : ℝ), (321157677/625000000 : ℝ)] ![(4369008763621/50000000000000 : ℝ), (9476118291921/20000000000000 : ℝ), (21940695499809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1394099947/10000000000 : ℝ)|^5343 ≤ (4369008763621/50000000000000 : ℝ)^4319
        have hw : |(-1394099947/10000000000 : ℝ)|=(1394099947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366823723/2500000000 : ℝ)|^5343 ≤ (9476118291921/20000000000000 : ℝ)^4319
        have hw : |(1366823723/2500000000 : ℝ)|=(1366823723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321157677/625000000 : ℝ)|^5343 ≤ (21940695499809/50000000000000 : ℝ)^4319
        have hw : |(321157677/625000000 : ℝ)|=(321157677/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s2_1 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670980187/5000000000 : ℝ)*x 0 + (-782260943/5000000000 : ℝ)*x 1 + (5138522841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670980187/5000000000 : ℝ)^5343 ≤ (5755071220349/12500000000000 : ℝ)^4319 := by
    have hnat : (2670980187 : ℕ)^5343*12500000000000^4319 ≤ 5755071220349^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670980187 5000000000 5755071220349 12500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782260943/5000000000 : ℝ)^5343 ≤ (10078039129127/100000000000000 : ℝ)^4319 := by
    have hnat : (782260943 : ℕ)^5343*100000000000000^4319 ≤ 10078039129127^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782260943 5000000000 10078039129127 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138522841/10000000000 : ℝ)^5343 ≤ (21940695547349/50000000000000 : ℝ)^4319 := by
    have hnat : (5138522841 : ℕ)^5343*50000000000000^4319 ≤ 21940695547349^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138522841 10000000000 21940695547349 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670980187/5000000000 : ℝ), (-782260943/5000000000 : ℝ), (5138522841/10000000000 : ℝ)] ![(5755071220349/12500000000000 : ℝ), (10078039129127/100000000000000 : ℝ), (21940695547349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670980187/5000000000 : ℝ)|^5343 ≤ (5755071220349/12500000000000 : ℝ)^4319
        have hw : |(2670980187/5000000000 : ℝ)|=(2670980187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-782260943/5000000000 : ℝ)|^5343 ≤ (10078039129127/100000000000000 : ℝ)^4319
        have hw : |(-782260943/5000000000 : ℝ)|=(782260943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138522841/10000000000 : ℝ)|^5343 ≤ (21940695547349/50000000000000 : ℝ)^4319
        have hw : |(5138522841/10000000000 : ℝ)|=(5138522841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s2_2 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133549009/250000000 : ℝ)*x 0 + (5138522841/10000000000 : ℝ)*x 1 + (-312904381/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133549009/250000000 : ℝ)^5343 ≤ (46040569613523/100000000000000 : ℝ)^4319 := by
    have hnat : (133549009 : ℕ)^5343*100000000000000^4319 ≤ 46040569613523^4319*250000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133549009 250000000 46040569613523 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138522841/10000000000 : ℝ)^5343 ≤ (21940695547349/50000000000000 : ℝ)^4319 := by
    have hnat : (5138522841 : ℕ)^5343*50000000000000^4319 ≤ 21940695547349^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138522841 10000000000 21940695547349 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312904381/2000000000 : ℝ)^5343 ≤ (1259754910067/12500000000000 : ℝ)^4319 := by
    have hnat : (312904381 : ℕ)^5343*12500000000000^4319 ≤ 1259754910067^4319*2000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312904381 2000000000 1259754910067 12500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133549009/250000000 : ℝ), (5138522841/10000000000 : ℝ), (-312904381/2000000000 : ℝ)] ![(46040569613523/100000000000000 : ℝ), (21940695547349/50000000000000 : ℝ), (1259754910067/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133549009/250000000 : ℝ)|^5343 ≤ (46040569613523/100000000000000 : ℝ)^4319
        have hw : |(133549009/250000000 : ℝ)|=(133549009/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138522841/10000000000 : ℝ)|^5343 ≤ (21940695547349/50000000000000 : ℝ)^4319
        have hw : |(5138522841/10000000000 : ℝ)|=(5138522841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-312904381/2000000000 : ℝ)|^5343 ≤ (1259754910067/12500000000000 : ℝ)^4319
        have hw : |(-312904381/2000000000 : ℝ)|=(312904381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s2_3 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1024564913/2500000000 : ℝ)*x 0 + (1816963067/5000000000 : ℝ)*x 1 + (4597991849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024564913/2500000000 : ℝ)^5343 ≤ (16585170462567/50000000000000 : ℝ)^4319 := by
    have hnat : (1024564913 : ℕ)^5343*50000000000000^4319 ≤ 16585170462567^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024564913 2500000000 16585170462567 50000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1816963067/5000000000 : ℝ)^5343 ≤ (1786589746573/6250000000000 : ℝ)^4319 := by
    have hnat : (1816963067 : ℕ)^5343*6250000000000^4319 ≤ 1786589746573^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816963067 5000000000 1786589746573 6250000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4597991849/10000000000 : ℝ)^5343 ≤ (9561055779347/25000000000000 : ℝ)^4319 := by
    have hnat : (4597991849 : ℕ)^5343*25000000000000^4319 ≤ 9561055779347^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4597991849 10000000000 9561055779347 25000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1024564913/2500000000 : ℝ), (1816963067/5000000000 : ℝ), (4597991849/10000000000 : ℝ)] ![(16585170462567/50000000000000 : ℝ), (1786589746573/6250000000000 : ℝ), (9561055779347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1024564913/2500000000 : ℝ)|^5343 ≤ (16585170462567/50000000000000 : ℝ)^4319
        have hw : |(1024564913/2500000000 : ℝ)|=(1024564913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1816963067/5000000000 : ℝ)|^5343 ≤ (1786589746573/6250000000000 : ℝ)^4319
        have hw : |(1816963067/5000000000 : ℝ)|=(1816963067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4597991849/10000000000 : ℝ)|^5343 ≤ (9561055779347/25000000000000 : ℝ)^4319
        have hw : |(4597991849/10000000000 : ℝ)|=(4597991849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s2_4 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-139424881/1000000000 : ℝ)*x 0 + (80346699/156250000 : ℝ)*x 1 + (341473389/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139424881/1000000000 : ℝ)^5343 ≤ (8739171812729/100000000000000 : ℝ)^4319 := by
    have hnat : (139424881 : ℕ)^5343*100000000000000^4319 ≤ 8739171812729^4319*1000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139424881 1000000000 8739171812729 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80346699/156250000 : ℝ)^5343 ≤ (8784024456361/20000000000000 : ℝ)^4319 := by
    have hnat : (80346699 : ℕ)^5343*20000000000000^4319 ≤ 8784024456361^4319*156250000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80346699 156250000 8784024456361 20000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341473389/625000000 : ℝ)^5343 ≤ (47340705887677/100000000000000 : ℝ)^4319 := by
    have hnat : (341473389 : ℕ)^5343*100000000000000^4319 ≤ 47340705887677^4319*625000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341473389 625000000 47340705887677 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-139424881/1000000000 : ℝ), (80346699/156250000 : ℝ), (341473389/625000000 : ℝ)] ![(8739171812729/100000000000000 : ℝ), (8784024456361/20000000000000 : ℝ), (47340705887677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-139424881/1000000000 : ℝ)|^5343 ≤ (8739171812729/100000000000000 : ℝ)^4319
        have hw : |(-139424881/1000000000 : ℝ)|=(139424881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80346699/156250000 : ℝ)|^5343 ≤ (8784024456361/20000000000000 : ℝ)^4319
        have hw : |(80346699/156250000 : ℝ)|=(80346699/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(341473389/625000000 : ℝ)|^5343 ≤ (47340705887677/100000000000000 : ℝ)^4319
        have hw : |(341473389/625000000 : ℝ)|=(341473389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s2_5 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525394909/1000000000 : ℝ)*x 0 + (-123947053/1000000000 : ℝ)*x 1 + (2731787111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525394909/1000000000 : ℝ)^5343 ≤ (5638003346569/12500000000000 : ℝ)^4319 := by
    have hnat : (525394909 : ℕ)^5343*12500000000000^4319 ≤ 5638003346569^4319*1000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525394909 1000000000 5638003346569 12500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123947053/1000000000 : ℝ)^5343 ≤ (7555267348613/100000000000000 : ℝ)^4319 := by
    have hnat : (123947053 : ℕ)^5343*100000000000000^4319 ≤ 7555267348613^4319*1000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123947053 1000000000 7555267348613 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731787111/5000000000 : ℝ)^5343 ≤ (47340705866239/100000000000000 : ℝ)^4319 := by
    have hnat : (2731787111 : ℕ)^5343*100000000000000^4319 ≤ 47340705866239^4319*5000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731787111 5000000000 47340705866239 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525394909/1000000000 : ℝ), (-123947053/1000000000 : ℝ), (2731787111/5000000000 : ℝ)] ![(5638003346569/12500000000000 : ℝ), (7555267348613/100000000000000 : ℝ), (47340705866239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525394909/1000000000 : ℝ)|^5343 ≤ (5638003346569/12500000000000 : ℝ)^4319
        have hw : |(525394909/1000000000 : ℝ)|=(525394909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123947053/1000000000 : ℝ)|^5343 ≤ (7555267348613/100000000000000 : ℝ)^4319
        have hw : |(-123947053/1000000000 : ℝ)|=(123947053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731787111/5000000000 : ℝ)|^5343 ≤ (47340705866239/100000000000000 : ℝ)^4319
        have hw : |(2731787111/5000000000 : ℝ)|=(2731787111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s2_6 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253949087/10000000000 : ℝ)*x 0 + (218542969/400000000 : ℝ)*x 1 + (-1239470529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253949087/10000000000 : ℝ)^5343 ≤ (45104026740691/100000000000000 : ℝ)^4319 := by
    have hnat : (5253949087 : ℕ)^5343*100000000000000^4319 ≤ 45104026740691^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253949087 10000000000 45104026740691 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218542969/400000000 : ℝ)^5343 ≤ (47340705898397/100000000000000 : ℝ)^4319 := by
    have hnat : (218542969 : ℕ)^5343*100000000000000^4319 ≤ 47340705898397^4319*400000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218542969 400000000 47340705898397 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1239470529/10000000000 : ℝ)^5343 ≤ (472204208817/6250000000000 : ℝ)^4319 := by
    have hnat : (1239470529 : ℕ)^5343*6250000000000^4319 ≤ 472204208817^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239470529 10000000000 472204208817 6250000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253949087/10000000000 : ℝ), (218542969/400000000 : ℝ), (-1239470529/10000000000 : ℝ)] ![(45104026740691/100000000000000 : ℝ), (47340705898397/100000000000000 : ℝ), (472204208817/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253949087/10000000000 : ℝ)|^5343 ≤ (45104026740691/100000000000000 : ℝ)^4319
        have hw : |(5253949087/10000000000 : ℝ)|=(5253949087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218542969/400000000 : ℝ)|^5343 ≤ (47340705898397/100000000000000 : ℝ)^4319
        have hw : |(218542969/400000000 : ℝ)|=(218542969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1239470529/10000000000 : ℝ)|^5343 ≤ (472204208817/6250000000000 : ℝ)^4319
        have hw : |(-1239470529/10000000000 : ℝ)|=(1239470529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1715_s2_7 (p : ℝ) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (163947847/400000000 : ℝ)*x 0 + (1146810563/2500000000 : ℝ)*x 1 + (3644836301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163947847/400000000 : ℝ)^5343 ≤ (4146838970819/12500000000000 : ℝ)^4319 := by
    have hnat : (163947847 : ℕ)^5343*12500000000000^4319 ≤ 4146838970819^4319*400000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163947847 400000000 4146838970819 12500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146810563/2500000000 : ℝ)^5343 ≤ (4766705556393/12500000000000 : ℝ)^4319 := by
    have hnat : (1146810563 : ℕ)^5343*12500000000000^4319 ≤ 4766705556393^4319*2500000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146810563 2500000000 4766705556393 12500000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3644836301/10000000000 : ℝ)^5343 ≤ (28691643770903/100000000000000 : ℝ)^4319 := by
    have hnat : (3644836301 : ℕ)^5343*100000000000000^4319 ≤ 28691643770903^4319*10000000000^5343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3644836301 10000000000 28691643770903 100000000000000 5343 4319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5343/1024 : ℝ)) 5343 4319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163947847/400000000 : ℝ), (1146810563/2500000000 : ℝ), (3644836301/10000000000 : ℝ)] ![(4146838970819/12500000000000 : ℝ), (4766705556393/12500000000000 : ℝ), (28691643770903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163947847/400000000 : ℝ)|^5343 ≤ (4146838970819/12500000000000 : ℝ)^4319
        have hw : |(163947847/400000000 : ℝ)|=(163947847/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1146810563/2500000000 : ℝ)|^5343 ≤ (4766705556393/12500000000000 : ℝ)^4319
        have hw : |(1146810563/2500000000 : ℝ)|=(1146810563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3644836301/10000000000 : ℝ)|^5343 ≤ (28691643770903/100000000000000 : ℝ)^4319
        have hw : |(3644836301/10000000000 : ℝ)|=(3644836301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1715_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8669/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4903/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10041/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8533/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8669/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4903/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8669/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4903/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8669/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4903/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8669/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4903/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8669/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4903/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8669/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4903/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4903/50000 : ℝ) ^ (5335/1024 : ℝ) ≤ (556816551208097/100000000000000000000 : ℝ) := by
    have hpowers : (4903/50000 : ℝ)^5335 ≤ (556816551208097/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4903 : ℕ)^5335*100000000000000000000^1024 ≤ 556816551208097^1024*50000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4903 50000 556816551208097 100000000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4903/50000 : ℝ)) (X := (556816551208097/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8669/50000 : ℝ) ^ (5335/1024 : ℝ) ≤ (677789016297581/6250000000000000000 : ℝ) := by
    have hpowers : (8669/50000 : ℝ)^5335 ≤ (677789016297581/6250000000000000000 : ℝ)^1024 := by
      have hnat : (8669 : ℕ)^5335*6250000000000000000^1024 ≤ 677789016297581^1024*50000^5335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8669 50000 677789016297581 6250000000000000000 5335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8669/50000 : ℝ)) (X := (677789016297581/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000556816551208097/50000000000000000000 : ℝ) ≤ (10000021374979681/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (50000556816551208097/50000000000000000000 : ℝ)^1024 ≤ (10000021374979681/10000000000000000 : ℝ)^5335 := by
      have hnat : (50000556816551208097 : ℕ)^1024*10000000000000000^5335 ≤ 10000021374979681^5335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000556816551208097 50000000000000000000 10000021374979681 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000021374979681/10000000000000000 : ℝ)) (X := (50000556816551208097/50000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011401440811969393/100000000000000000000 : ℝ) ≤ (80001750633569/80000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (100011401440811969393/100000000000000000000 : ℝ)^1024 ≤ (80001750633569/80000000000000 : ℝ)^5335 := by
      have hnat : (100011401440811969393 : ℕ)^1024*80000000000000^5335 ≤ 80001750633569^5335*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011401440811969393 100000000000000000000 80001750633569 80000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80001750633569/80000000000000 : ℝ)) (X := (100011401440811969393/100000000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3125677789016297581/3125000000000000000 : ℝ) ≤ (10000416283412569/10000000000000000 : ℝ) ^ (5335/1024 : ℝ) := by
    have hpowers : (3125677789016297581/3125000000000000000 : ℝ)^1024 ≤ (10000416283412569/10000000000000000 : ℝ)^5335 := by
      have hnat : (3125677789016297581 : ℕ)^1024*10000000000000000^5335 ≤ 10000416283412569^5335*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125677789016297581 3125000000000000000 10000416283412569 10000000000000000 1024 5335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000416283412569/10000000000000000 : ℝ)) (X := (3125677789016297581/3125000000000000000 : ℝ)) (by norm_num) 5335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(556816551208097/100000000000000000000 : ℝ) ≤ ((18829072131063514391/18830000000000000000 : ℝ)+2*(49363554111/188300000000000 : ℝ)*(4903/50000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (18829072131063514391/18830000000000000000 : ℝ)+2*(49363554111/188300000000000 : ℝ)*(4903/50000 : ℝ)=(10000021374979681/10000000000000000 : ℝ) by norm_num, show 1+2*(556816551208097/100000000000000000000 : ℝ)=(50000556816551208097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(677789016297581/6250000000000000000 : ℝ)+(556816551208097/100000000000000000000 : ℝ) ≤ ((18829072131063514391/18830000000000000000 : ℝ)+(49363554111/188300000000000 : ℝ)*((8669/50000 : ℝ)+(4903/50000 : ℝ)))^(5335/1024 : ℝ) := by
    rw [show (18829072131063514391/18830000000000000000 : ℝ)+(49363554111/188300000000000 : ℝ)*((8669/50000 : ℝ)+(4903/50000 : ℝ))=(80001750633569/80000000000000 : ℝ) by norm_num, show 1+(677789016297581/6250000000000000000 : ℝ)+(556816551208097/100000000000000000000 : ℝ)=(100011401440811969393/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(677789016297581/6250000000000000000 : ℝ) ≤ ((18829072131063514391/18830000000000000000 : ℝ)+2*(49363554111/188300000000000 : ℝ)*(8669/50000 : ℝ))^(5335/1024 : ℝ) := by
    rw [show (18829072131063514391/18830000000000000000 : ℝ)+2*(49363554111/188300000000000 : ℝ)*(8669/50000 : ℝ)=(10000416283412569/10000000000000000 : ℝ) by norm_num, show 1+2*(677789016297581/6250000000000000000 : ℝ)=(3125677789016297581/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18829072131063514391/18830000000000000000 : ℝ)*(X 1 0+X 2 0)+(49363554111/188300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (4903/50000 : ℝ)) (hi := (8669/50000 : ℝ)) (c := (18829072131063514391/18830000000000000000 : ℝ)) (alpha := (49363554111/188300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18829072131063514391/18830000000000000000 : ℝ)*(X 0 1+X 2 1)+(49363554111/188300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (4903/50000 : ℝ)) (hi := (8669/50000 : ℝ)) (c := (18829072131063514391/18830000000000000000 : ℝ)) (alpha := (49363554111/188300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18829072131063514391/18830000000000000000 : ℝ)*(X 0 2+X 1 2)+(49363554111/188300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5335/1024 : ℝ)) (lo := (4903/50000 : ℝ)) (hi := (8669/50000 : ℝ)) (c := (18829072131063514391/18830000000000000000 : ℝ)) (alpha := (49363554111/188300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1394099947/10000000000 : ℝ)*X 0 0+(1366823723/2500000000 : ℝ)*X 0 1+(321157677/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2670980187/5000000000 : ℝ)*X 1 0+(-782260943/5000000000 : ℝ)*X 1 1+(5138522841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133549009/250000000 : ℝ)*X 2 0+(5138522841/10000000000 : ℝ)*X 2 1+(-312904381/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1024564913/2500000000 : ℝ)*X 0 0+(1816963067/5000000000 : ℝ)*X 0 1+(4597991849/10000000000 : ℝ)*X 0 2+(1024564913/2500000000 : ℝ)*X 1 0+(1816963067/5000000000 : ℝ)*X 1 1+(4597991849/10000000000 : ℝ)*X 1 2+(1024564913/2500000000 : ℝ)*X 2 0+(1816963067/5000000000 : ℝ)*X 2 1+(4597991849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-139424881/1000000000 : ℝ)*X 0 0+(80346699/156250000 : ℝ)*X 0 1+(341473389/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((525394909/1000000000 : ℝ)*X 1 0+(-123947053/1000000000 : ℝ)*X 1 1+(2731787111/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253949087/10000000000 : ℝ)*X 2 0+(218542969/400000000 : ℝ)*X 2 1+(-1239470529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((163947847/400000000 : ℝ)*X 0 0+(1146810563/2500000000 : ℝ)*X 0 1+(3644836301/10000000000 : ℝ)*X 0 2+(163947847/400000000 : ℝ)*X 1 0+(1146810563/2500000000 : ℝ)*X 1 1+(3644836301/10000000000 : ℝ)*X 1 2+(163947847/400000000 : ℝ)*X 2 0+(1146810563/2500000000 : ℝ)*X 2 1+(3644836301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1715_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3673919296426173125013/294218750000000000000000000 : ℝ) := by norm_num
    linear_combination (461561173/25000000000000 : ℝ)*(base19) + (21621719/1250000000000 : ℝ)*(base23) + (57979351/100000000000000 : ℝ)*(lower2) + (77067969/25000000000000 : ℝ)*(upper3) + (108793949/50000000000000 : ℝ)*(upper5) + (509868108051503/25000000000000 : ℝ)*(major0) + (509868108051503/25000000000000 : ℝ)*(major1) + (509868108051503/25000000000000 : ℝ)*(major2) + (3041639833411007/100000000000000 : ℝ)*(sp0) + (304165620007883/10000000000000 : ℝ)*(sp1) + (1520828158293001/50000000000000 : ℝ)*(sp2) + (207455924627243/20000000000000 : ℝ)*(sp3) + (4553228129/25000000000000 : ℝ)*(sp4) + (6778717841/100000000000000 : ℝ)*(sp7) + (207457280370811/20000000000000 : ℝ)*(f.failure) + (1520829023161761/50000000000000 : ℝ)*(f.sum) + (8840231488279/4707500000000000000000000000 : ℝ)*base66 + (54601775202645761/67250000000000000000000000000000 : ℝ)*base68 + (382230346857145761/67250000000000000000000000000000 : ℝ)*base70 + (72374226673104239/67250000000000000000000000000000 : ℝ)*base71 + (6689554001051/4707500000000000000000000000 : ℝ)*base73 + (178543420313354239/67250000000000000000000000000000 : ℝ)*base75 + (228488490998104239/67250000000000000000000000000000 : ℝ)*base77 + (13012738472145761/67250000000000000000000000000000 : ℝ)*base80 + (1139002041529/4707500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2872903/400000000000000000000 : ℝ)*base90 + (2872903/400000000000000000000 : ℝ)*base92 + (2872903/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1403049845217485567197448607/470750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40870739/10000000000000 : ℝ)*(base19) + (219773341/50000000000000 : ℝ)*(base23) + (31730969/50000000000000 : ℝ)*(upper3) + (7347373/50000000000000 : ℝ)*(lower4) + (31477871/50000000000000 : ℝ)*(upper5) + (1043160467018141/50000000000000 : ℝ)*(major0) + (1043160467018141/50000000000000 : ℝ)*(major1) + (1043160467018141/50000000000000 : ℝ)*(major2) + (3732420097/100000000000000 : ℝ)*(sp1) + (1002457609/25000000000000 : ℝ)*(sp2) + (1555763986263007/50000000000000 : ℝ)*(sp4) + (1555761915699263/50000000000000 : ℝ)*(sp5) + (97235110098403/3125000000000 : ℝ)*(sp6) + (1061113796197999/100000000000000 : ℝ)*(sp7) + (1061113796197999/100000000000000 : ℝ)*(f.failure) + (1555763986263007/50000000000000 : ℝ)*(f.sum) + (55457329539027/9415000000000000000000000000 : ℝ)*base65 + (366808937197333267/134500000000000000000000000000000 : ℝ)*base68 + (194997666510833267/134500000000000000000000000000000 : ℝ)*base70 + (1257924244713166733/134500000000000000000000000000000 : ℝ)*base71 + (344085929343/588437500000000000000000000 : ℝ)*base74 + (982621224340666733/134500000000000000000000000000000 : ℝ)*base75 + (109630858670166733/134500000000000000000000000000000 : ℝ)*base77 + (132452914568666733/134500000000000000000000000000000 : ℝ)*base79 + (18929345359277/9415000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (11622773/2000000000000000000000 : ℝ)*base89 + (11622773/2000000000000000000000 : ℝ)*base91 + (11622773/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1715_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8669/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4903/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8533/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1715_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1715_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8533/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1715_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1715_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1715_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5335/1024 : ℝ) ≤ p) (hpb : p ≤ (5343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39323227/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8533/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1715_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1565_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:25:52.874097+00:00
-- url     : https://prove2.me/submissions/a540d01b-e853-49b9-87b6-eddd0dbd7bf8

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
theorem support_rectangle_w1565_box_0 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1587854763/10000000000 : ℝ)*x 0 + (2698564479/5000000000 : ℝ)*x 1 + (5397128131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1587854763/10000000000 : ℝ)^4627 ≤ (1882370537319/20000000000000 : ℝ)^3603 := by
    have hnat : (1587854763 : ℕ)^4627*20000000000000^3603 ≤ 1882370537319^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587854763 10000000000 1882370537319 20000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698564479/5000000000 : ℝ)^4627 ≤ (45294078107789/100000000000000 : ℝ)^3603 := by
    have hnat : (2698564479 : ℕ)^4627*100000000000000^3603 ≤ 45294078107789^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698564479 5000000000 45294078107789 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397128131/10000000000 : ℝ)^4627 ≤ (22647034597441/50000000000000 : ℝ)^3603 := by
    have hnat : (5397128131 : ℕ)^4627*50000000000000^3603 ≤ 22647034597441^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397128131 10000000000 22647034597441 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1587854763/10000000000 : ℝ), (2698564479/5000000000 : ℝ), (5397128131/10000000000 : ℝ)] ![(1882370537319/20000000000000 : ℝ), (45294078107789/100000000000000 : ℝ), (22647034597441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1587854763/10000000000 : ℝ)|^4627 ≤ (1882370537319/20000000000000 : ℝ)^3603
        have hw : |(-1587854763/10000000000 : ℝ)|=(1587854763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698564479/5000000000 : ℝ)|^4627 ≤ (45294078107789/100000000000000 : ℝ)^3603
        have hw : |(2698564479/5000000000 : ℝ)|=(2698564479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397128131/10000000000 : ℝ)|^4627 ≤ (22647034597441/50000000000000 : ℝ)^3603
        have hw : |(5397128131/10000000000 : ℝ)|=(5397128131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_1 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271139663/10000000000 : ℝ)*x 0 + (-220370557/1250000000 : ℝ)*x 1 + (5397128667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271139663/10000000000 : ℝ)^4627 ≤ (43940771110257/100000000000000 : ℝ)^3603 := by
    have hnat : (5271139663 : ℕ)^4627*100000000000000^3603 ≤ 43940771110257^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271139663 10000000000 43940771110257 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220370557/1250000000 : ℝ)^4627 ≤ (10765153899983/100000000000000 : ℝ)^3603 := by
    have hnat : (220370557 : ℕ)^4627*100000000000000^3603 ≤ 10765153899983^3603*1250000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220370557 1250000000 10765153899983 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397128667/10000000000 : ℝ)^4627 ≤ (22647037485783/50000000000000 : ℝ)^3603 := by
    have hnat : (5397128667 : ℕ)^4627*50000000000000^3603 ≤ 22647037485783^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397128667 10000000000 22647037485783 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271139663/10000000000 : ℝ), (-220370557/1250000000 : ℝ), (5397128667/10000000000 : ℝ)] ![(43940771110257/100000000000000 : ℝ), (10765153899983/100000000000000 : ℝ), (22647037485783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271139663/10000000000 : ℝ)|^4627 ≤ (43940771110257/100000000000000 : ℝ)^3603
        have hw : |(5271139663/10000000000 : ℝ)|=(5271139663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220370557/1250000000 : ℝ)|^4627 ≤ (10765153899983/100000000000000 : ℝ)^3603
        have hw : |(-220370557/1250000000 : ℝ)|=(220370557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397128667/10000000000 : ℝ)|^4627 ≤ (22647037485783/50000000000000 : ℝ)^3603
        have hw : |(5397128667/10000000000 : ℝ)|=(5397128667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_2 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635570139/5000000000 : ℝ)*x 0 + (33732053/62500000 : ℝ)*x 1 + (-1762963873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635570139/5000000000 : ℝ)^4627 ≤ (4394077769401/10000000000000 : ℝ)^3603 := by
    have hnat : (2635570139 : ℕ)^4627*10000000000000^3603 ≤ 4394077769401^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635570139 5000000000 4394077769401 10000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33732053/62500000 : ℝ)^4627 ≤ (45294072956193/100000000000000 : ℝ)^3603 := by
    have hnat : (33732053 : ℕ)^4627*100000000000000^3603 ≤ 45294072956193^3603*62500000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33732053 62500000 45294072956193 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1762963873/10000000000 : ℝ)^4627 ≤ (2153029865651/20000000000000 : ℝ)^3603 := by
    have hnat : (1762963873 : ℕ)^4627*20000000000000^3603 ≤ 2153029865651^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762963873 10000000000 2153029865651 20000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635570139/5000000000 : ℝ), (33732053/62500000 : ℝ), (-1762963873/10000000000 : ℝ)] ![(4394077769401/10000000000000 : ℝ), (45294072956193/100000000000000 : ℝ), (2153029865651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635570139/5000000000 : ℝ)|^4627 ≤ (4394077769401/10000000000000 : ℝ)^3603
        have hw : |(2635570139/5000000000 : ℝ)|=(2635570139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33732053/62500000 : ℝ)|^4627 ≤ (45294072956193/100000000000000 : ℝ)^3603
        have hw : |(33732053/62500000 : ℝ)|=(33732053/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1762963873/10000000000 : ℝ)|^4627 ≤ (2153029865651/20000000000000 : ℝ)^3603
        have hw : |(-1762963873/10000000000 : ℝ)|=(1762963873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_3 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2223294269/5000000000 : ℝ)*x 0 + (2075968707/5000000000 : ℝ)*x 1 + (830387719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2223294269/5000000000 : ℝ)^4627 ≤ (35317790415967/100000000000000 : ℝ)^3603 := by
    have hnat : (2223294269 : ℕ)^4627*100000000000000^3603 ≤ 35317790415967^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223294269 5000000000 35317790415967 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075968707/5000000000 : ℝ)^4627 ≤ (16170549437979/50000000000000 : ℝ)^3603 := by
    have hnat : (2075968707 : ℕ)^4627*50000000000000^3603 ≤ 16170549437979^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075968707 5000000000 16170549437979 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830387719/2000000000 : ℝ)^4627 ≤ (2021319418109/6250000000000 : ℝ)^3603 := by
    have hnat : (830387719 : ℕ)^4627*6250000000000^3603 ≤ 2021319418109^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830387719 2000000000 2021319418109 6250000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2223294269/5000000000 : ℝ), (2075968707/5000000000 : ℝ), (830387719/2000000000 : ℝ)] ![(35317790415967/100000000000000 : ℝ), (16170549437979/50000000000000 : ℝ), (2021319418109/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2223294269/5000000000 : ℝ)|^4627 ≤ (35317790415967/100000000000000 : ℝ)^3603
        have hw : |(2223294269/5000000000 : ℝ)|=(2223294269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075968707/5000000000 : ℝ)|^4627 ≤ (16170549437979/50000000000000 : ℝ)^3603
        have hw : |(2075968707/5000000000 : ℝ)|=(2075968707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830387719/2000000000 : ℝ)|^4627 ≤ (2021319418109/6250000000000 : ℝ)^3603
        have hw : |(830387719/2000000000 : ℝ)|=(830387719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_4 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2002477289/10000000000 : ℝ)*x 0 + (104899277/200000000 : ℝ)*x 1 + (2622482079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2002477289/10000000000 : ℝ)^4627 ≤ (12678497797811/100000000000000 : ℝ)^3603 := by
    have hnat : (2002477289 : ℕ)^4627*100000000000000^3603 ≤ 12678497797811^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002477289 10000000000 12678497797811 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104899277/200000000 : ℝ)^4627 ≤ (21830374724829/50000000000000 : ℝ)^3603 := by
    have hnat : (104899277 : ℕ)^4627*50000000000000^3603 ≤ 21830374724829^3603*200000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104899277 200000000 21830374724829 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622482079/5000000000 : ℝ)^4627 ≤ (21830376371113/50000000000000 : ℝ)^3603 := by
    have hnat : (2622482079 : ℕ)^4627*50000000000000^3603 ≤ 21830376371113^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622482079 5000000000 21830376371113 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2002477289/10000000000 : ℝ), (104899277/200000000 : ℝ), (2622482079/5000000000 : ℝ)] ![(12678497797811/100000000000000 : ℝ), (21830374724829/50000000000000 : ℝ), (21830376371113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2002477289/10000000000 : ℝ)|^4627 ≤ (12678497797811/100000000000000 : ℝ)^3603
        have hw : |(-2002477289/10000000000 : ℝ)|=(2002477289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104899277/200000000 : ℝ)|^4627 ≤ (21830374724829/50000000000000 : ℝ)^3603
        have hw : |(104899277/200000000 : ℝ)|=(104899277/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622482079/5000000000 : ℝ)|^4627 ≤ (21830376371113/50000000000000 : ℝ)^3603
        have hw : |(2622482079/5000000000 : ℝ)|=(2622482079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_5 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688328021/5000000000 : ℝ)*x 0 + (-1826472593/10000000000 : ℝ)*x 1 + (1048992821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688328021/5000000000 : ℝ)^4627 ≤ (5634194052007/12500000000000 : ℝ)^3603 := by
    have hnat : (2688328021 : ℕ)^4627*12500000000000^3603 ≤ 5634194052007^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688328021 5000000000 5634194052007 12500000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1826472593/10000000000 : ℝ)^4627 ≤ (11265695397503/100000000000000 : ℝ)^3603 := by
    have hnat : (1826472593 : ℕ)^4627*100000000000000^3603 ≤ 11265695397503^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826472593 10000000000 11265695397503 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048992821/2000000000 : ℝ)^4627 ≤ (1364398505489/3125000000000 : ℝ)^3603 := by
    have hnat : (1048992821 : ℕ)^4627*3125000000000^3603 ≤ 1364398505489^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048992821 2000000000 1364398505489 3125000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688328021/5000000000 : ℝ), (-1826472593/10000000000 : ℝ), (1048992821/2000000000 : ℝ)] ![(5634194052007/12500000000000 : ℝ), (11265695397503/100000000000000 : ℝ), (1364398505489/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688328021/5000000000 : ℝ)|^4627 ≤ (5634194052007/12500000000000 : ℝ)^3603
        have hw : |(2688328021/5000000000 : ℝ)|=(2688328021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1826472593/10000000000 : ℝ)|^4627 ≤ (11265695397503/100000000000000 : ℝ)^3603
        have hw : |(-1826472593/10000000000 : ℝ)|=(1826472593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048992821/2000000000 : ℝ)|^4627 ≤ (1364398505489/3125000000000 : ℝ)^3603
        have hw : |(1048992821/2000000000 : ℝ)|=(1048992821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_6 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376655691/10000000000 : ℝ)*x 0 + (5244964519/10000000000 : ℝ)*x 1 + (-1826472511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376655691/10000000000 : ℝ)^4627 ≤ (45073548637273/100000000000000 : ℝ)^3603 := by
    have hnat : (5376655691 : ℕ)^4627*100000000000000^3603 ≤ 45073548637273^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376655691 10000000000 45073548637273 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244964519/10000000000 : ℝ)^4627 ≤ (43660756601371/100000000000000 : ℝ)^3603 := by
    have hnat : (5244964519 : ℕ)^4627*100000000000000^3603 ≤ 43660756601371^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244964519 10000000000 43660756601371 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1826472511/10000000000 : ℝ)^4627 ≤ (563284737399/5000000000000 : ℝ)^3603 := by
    have hnat : (1826472511 : ℕ)^4627*5000000000000^3603 ≤ 563284737399^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826472511 10000000000 563284737399 5000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376655691/10000000000 : ℝ), (5244964519/10000000000 : ℝ), (-1826472511/10000000000 : ℝ)] ![(45073548637273/100000000000000 : ℝ), (43660756601371/100000000000000 : ℝ), (563284737399/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376655691/10000000000 : ℝ)|^4627 ≤ (45073548637273/100000000000000 : ℝ)^3603
        have hw : |(5376655691/10000000000 : ℝ)|=(5376655691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244964519/10000000000 : ℝ)|^4627 ≤ (43660756601371/100000000000000 : ℝ)^3603
        have hw : |(5244964519/10000000000 : ℝ)|=(5244964519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1826472511/10000000000 : ℝ)|^4627 ≤ (563284737399/5000000000000 : ℝ)^3603
        have hw : |(-1826472511/10000000000 : ℝ)|=(1826472511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_7 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (808434043/2000000000 : ℝ)*x 0 + (4354019647/10000000000 : ℝ)*x 1 + (2177009367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808434043/2000000000 : ℝ)^4627 ≤ (31247226441819/100000000000000 : ℝ)^3603 := by
    have hnat : (808434043 : ℕ)^4627*100000000000000^3603 ≤ 31247226441819^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808434043 2000000000 31247226441819 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4354019647/10000000000 : ℝ)^4627 ≤ (34376391403587/100000000000000 : ℝ)^3603 := by
    have hnat : (4354019647 : ℕ)^4627*100000000000000^3603 ≤ 34376391403587^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354019647 10000000000 34376391403587 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177009367/5000000000 : ℝ)^4627 ≤ (34376382146467/100000000000000 : ℝ)^3603 := by
    have hnat : (2177009367 : ℕ)^4627*100000000000000^3603 ≤ 34376382146467^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177009367 5000000000 34376382146467 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(808434043/2000000000 : ℝ), (4354019647/10000000000 : ℝ), (2177009367/5000000000 : ℝ)] ![(31247226441819/100000000000000 : ℝ), (34376391403587/100000000000000 : ℝ), (34376382146467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(808434043/2000000000 : ℝ)|^4627 ≤ (31247226441819/100000000000000 : ℝ)^3603
        have hw : |(808434043/2000000000 : ℝ)|=(808434043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4354019647/10000000000 : ℝ)|^4627 ≤ (34376391403587/100000000000000 : ℝ)^3603
        have hw : |(4354019647/10000000000 : ℝ)|=(4354019647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2177009367/5000000000 : ℝ)|^4627 ≤ (34376382146467/100000000000000 : ℝ)^3603
        have hw : |(2177009367/5000000000 : ℝ)|=(2177009367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_8 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-382922381/2000000000 : ℝ)*x 0 + (5137809403/10000000000 : ℝ)*x 1 + (2708707501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382922381/2000000000 : ℝ)^4627 ≤ (11968580522017/100000000000000 : ℝ)^3603 := by
    have hnat : (382922381 : ℕ)^4627*100000000000000^3603 ≤ 11968580522017^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382922381 2000000000 11968580522017 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137809403/10000000000 : ℝ)^4627 ≤ (21259296971467/50000000000000 : ℝ)^3603 := by
    have hnat : (5137809403 : ℕ)^4627*50000000000000^3603 ≤ 21259296971467^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137809403 10000000000 21259296971467 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708707501/5000000000 : ℝ)^4627 ≤ (45512825521337/100000000000000 : ℝ)^3603 := by
    have hnat : (2708707501 : ℕ)^4627*100000000000000^3603 ≤ 45512825521337^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708707501 5000000000 45512825521337 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382922381/2000000000 : ℝ), (5137809403/10000000000 : ℝ), (2708707501/5000000000 : ℝ)] ![(11968580522017/100000000000000 : ℝ), (21259296971467/50000000000000 : ℝ), (45512825521337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382922381/2000000000 : ℝ)|^4627 ≤ (11968580522017/100000000000000 : ℝ)^3603
        have hw : |(-382922381/2000000000 : ℝ)|=(382922381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137809403/10000000000 : ℝ)|^4627 ≤ (21259296971467/50000000000000 : ℝ)^3603
        have hw : |(5137809403/10000000000 : ℝ)|=(5137809403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708707501/5000000000 : ℝ)|^4627 ≤ (45512825521337/100000000000000 : ℝ)^3603
        have hw : |(2708707501/5000000000 : ℝ)|=(2708707501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_9 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314267079/2500000000 : ℝ)*x 0 + (-1754264071/10000000000 : ℝ)*x 1 + (5417415769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314267079/2500000000 : ℝ)^4627 ≤ (43790190457233/100000000000000 : ℝ)^3603 := by
    have hnat : (1314267079 : ℕ)^4627*100000000000000^3603 ≤ 43790190457233^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314267079 2500000000 43790190457233 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1754264071/10000000000 : ℝ)^4627 ≤ (5348487863421/50000000000000 : ℝ)^3603 := by
    have hnat : (1754264071 : ℕ)^4627*50000000000000^3603 ≤ 5348487863421^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754264071 10000000000 5348487863421 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417415769/10000000000 : ℝ)^4627 ≤ (22756416898209/50000000000000 : ℝ)^3603 := by
    have hnat : (5417415769 : ℕ)^4627*50000000000000^3603 ≤ 22756416898209^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417415769 10000000000 22756416898209 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314267079/2500000000 : ℝ), (-1754264071/10000000000 : ℝ), (5417415769/10000000000 : ℝ)] ![(43790190457233/100000000000000 : ℝ), (5348487863421/50000000000000 : ℝ), (22756416898209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314267079/2500000000 : ℝ)|^4627 ≤ (43790190457233/100000000000000 : ℝ)^3603
        have hw : |(1314267079/2500000000 : ℝ)|=(1314267079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1754264071/10000000000 : ℝ)|^4627 ≤ (5348487863421/50000000000000 : ℝ)^3603
        have hw : |(-1754264071/10000000000 : ℝ)|=(1754264071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417415769/10000000000 : ℝ)|^4627 ≤ (22756416898209/50000000000000 : ℝ)^3603
        have hw : |(5417415769/10000000000 : ℝ)|=(5417415769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_10 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657133513/1250000000 : ℝ)*x 0 + (2708708103/5000000000 : ℝ)*x 1 + (-1754263759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657133513/1250000000 : ℝ)^4627 ≤ (10947547047359/25000000000000 : ℝ)^3603 := by
    have hnat : (657133513 : ℕ)^4627*25000000000000^3603 ≤ 10947547047359^3603*1250000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657133513 1250000000 10947547047359 25000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708708103/5000000000 : ℝ)^4627 ≤ (9102567702233/20000000000000 : ℝ)^3603 := by
    have hnat : (2708708103 : ℕ)^4627*20000000000000^3603 ≤ 9102567702233^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708708103 5000000000 9102567702233 20000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1754263759/10000000000 : ℝ)^4627 ≤ (534848664183/5000000000000 : ℝ)^3603 := by
    have hnat : (1754263759 : ℕ)^4627*5000000000000^3603 ≤ 534848664183^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754263759 10000000000 534848664183 5000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657133513/1250000000 : ℝ), (2708708103/5000000000 : ℝ), (-1754263759/10000000000 : ℝ)] ![(10947547047359/25000000000000 : ℝ), (9102567702233/20000000000000 : ℝ), (534848664183/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657133513/1250000000 : ℝ)|^4627 ≤ (10947547047359/25000000000000 : ℝ)^3603
        have hw : |(657133513/1250000000 : ℝ)|=(657133513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708708103/5000000000 : ℝ)|^4627 ≤ (9102567702233/20000000000000 : ℝ)^3603
        have hw : |(2708708103/5000000000 : ℝ)|=(2708708103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1754263759/10000000000 : ℝ)|^4627 ≤ (534848664183/5000000000000 : ℝ)^3603
        have hw : |(-1754263759/10000000000 : ℝ)|=(1754263759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_11 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2249681037/5000000000 : ℝ)*x 0 + (1031240453/2500000000 : ℝ)*x 1 + (82499237/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2249681037/5000000000 : ℝ)^4627 ≤ (7171397562747/20000000000000 : ℝ)^3603 := by
    have hnat : (2249681037 : ℕ)^4627*20000000000000^3603 ≤ 7171397562747^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249681037 5000000000 7171397562747 20000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031240453/2500000000 : ℝ)^4627 ≤ (25657204717/80000000000 : ℝ)^3603 := by
    have hnat : (1031240453 : ℕ)^4627*80000000000^3603 ≤ 25657204717^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031240453 2500000000 25657204717 80000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82499237/200000000 : ℝ)^4627 ≤ (32071506275669/100000000000000 : ℝ)^3603 := by
    have hnat : (82499237 : ℕ)^4627*100000000000000^3603 ≤ 32071506275669^3603*200000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82499237 200000000 32071506275669 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2249681037/5000000000 : ℝ), (1031240453/2500000000 : ℝ), (82499237/200000000 : ℝ)] ![(7171397562747/20000000000000 : ℝ), (25657204717/80000000000 : ℝ), (32071506275669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2249681037/5000000000 : ℝ)|^4627 ≤ (7171397562747/20000000000000 : ℝ)^3603
        have hw : |(2249681037/5000000000 : ℝ)|=(2249681037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031240453/2500000000 : ℝ)|^4627 ≤ (25657204717/80000000000 : ℝ)^3603
        have hw : |(1031240453/2500000000 : ℝ)|=(1031240453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82499237/200000000 : ℝ)|^4627 ≤ (32071506275669/100000000000000 : ℝ)^3603
        have hw : |(82499237/200000000 : ℝ)|=(82499237/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_12 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418851183/2500000000 : ℝ)*x 0 + (1100200823/2000000000 : ℝ)*x 1 + (163434817/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418851183/2500000000 : ℝ)^4627 ≤ (504171940051/5000000000000 : ℝ)^3603 := by
    have hnat : (418851183 : ℕ)^4627*5000000000000^3603 ≤ 504171940051^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418851183 2500000000 504171940051 5000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100200823/2000000000 : ℝ)^4627 ≤ (725259839923/1562500000000 : ℝ)^3603 := by
    have hnat : (1100200823 : ℕ)^4627*1562500000000^3603 ≤ 725259839923^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100200823 2000000000 725259839923 1562500000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163434817/312500000 : ℝ)^4627 ≤ (21749965716761/50000000000000 : ℝ)^3603 := by
    have hnat : (163434817 : ℕ)^4627*50000000000000^3603 ≤ 21749965716761^3603*312500000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163434817 312500000 21749965716761 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418851183/2500000000 : ℝ), (1100200823/2000000000 : ℝ), (163434817/312500000 : ℝ)] ![(504171940051/5000000000000 : ℝ), (725259839923/1562500000000 : ℝ), (21749965716761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418851183/2500000000 : ℝ)|^4627 ≤ (504171940051/5000000000000 : ℝ)^3603
        have hw : |(-418851183/2500000000 : ℝ)|=(418851183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100200823/2000000000 : ℝ)|^4627 ≤ (725259839923/1562500000000 : ℝ)^3603
        have hw : |(1100200823/2000000000 : ℝ)|=(1100200823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163434817/312500000 : ℝ)|^4627 ≤ (21749965716761/50000000000000 : ℝ)^3603
        have hw : |(163434817/312500000 : ℝ)|=(163434817/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_13 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346773181/2500000000 : ℝ)*x 0 + (-366516733/2000000000 : ℝ)*x 1 + (2614957171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346773181/2500000000 : ℝ)^4627 ≤ (11296485557039/25000000000000 : ℝ)^3603 := by
    have hnat : (1346773181 : ℕ)^4627*25000000000000^3603 ≤ 11296485557039^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346773181 2500000000 11296485557039 25000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366516733/2000000000 : ℝ)^4627 ≤ (11314124202953/100000000000000 : ℝ)^3603 := by
    have hnat : (366516733 : ℕ)^4627*100000000000000^3603 ≤ 11314124202953^3603*2000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366516733 2000000000 11314124202953 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614957171/5000000000 : ℝ)^4627 ≤ (10874983387111/25000000000000 : ℝ)^3603 := by
    have hnat : (2614957171 : ℕ)^4627*25000000000000^3603 ≤ 10874983387111^3603*5000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614957171 5000000000 10874983387111 25000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346773181/2500000000 : ℝ), (-366516733/2000000000 : ℝ), (2614957171/5000000000 : ℝ)] ![(11296485557039/25000000000000 : ℝ), (11314124202953/100000000000000 : ℝ), (10874983387111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346773181/2500000000 : ℝ)|^4627 ≤ (11296485557039/25000000000000 : ℝ)^3603
        have hw : |(1346773181/2500000000 : ℝ)|=(1346773181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366516733/2000000000 : ℝ)|^4627 ≤ (11314124202953/100000000000000 : ℝ)^3603
        have hw : |(-366516733/2000000000 : ℝ)|=(366516733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614957171/5000000000 : ℝ)|^4627 ≤ (10874983387111/25000000000000 : ℝ)^3603
        have hw : |(2614957171/5000000000 : ℝ)|=(2614957171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_14 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387093673/10000000000 : ℝ)*x 0 + (522991361/1000000000 : ℝ)*x 1 + (-1832583363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387093673/10000000000 : ℝ)^4627 ≤ (706030507039/1562500000000 : ℝ)^3603 := by
    have hnat : (5387093673 : ℕ)^4627*1562500000000^3603 ≤ 706030507039^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387093673 10000000000 706030507039 1562500000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522991361/1000000000 : ℝ)^4627 ≤ (1087498143241/2500000000000 : ℝ)^3603 := by
    have hnat : (522991361 : ℕ)^4627*2500000000000^3603 ≤ 1087498143241^3603*1000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522991361 1000000000 1087498143241 2500000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1832583363/10000000000 : ℝ)^4627 ≤ (5657060904269/50000000000000 : ℝ)^3603 := by
    have hnat : (1832583363 : ℕ)^4627*50000000000000^3603 ≤ 5657060904269^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1832583363 10000000000 5657060904269 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387093673/10000000000 : ℝ), (522991361/1000000000 : ℝ), (-1832583363/10000000000 : ℝ)] ![(706030507039/1562500000000 : ℝ), (1087498143241/2500000000000 : ℝ), (5657060904269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387093673/10000000000 : ℝ)|^4627 ≤ (706030507039/1562500000000 : ℝ)^3603
        have hw : |(5387093673/10000000000 : ℝ)|=(5387093673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522991361/1000000000 : ℝ)|^4627 ≤ (1087498143241/2500000000000 : ℝ)^3603
        have hw : |(522991361/1000000000 : ℝ)|=(522991361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1832583363/10000000000 : ℝ)|^4627 ≤ (5657060904269/50000000000000 : ℝ)^3603
        have hw : |(-1832583363/10000000000 : ℝ)|=(1832583363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1565_box_15 (p : ℝ) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4001309787/10000000000 : ℝ)*x 0 + (1093495361/2500000000 : ℝ)*x 1 + (1093494947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4001309787/10000000000 : ℝ)^4627 ≤ (30842175900767/100000000000000 : ℝ)^3603 := by
    have hnat : (4001309787 : ℕ)^4627*100000000000000^3603 ≤ 30842175900767^3603*10000000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001309787 10000000000 30842175900767 100000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093495361/2500000000 : ℝ)^4627 ≤ (3457892044893/10000000000000 : ℝ)^3603 := by
    have hnat : (1093495361 : ℕ)^4627*10000000000000^3603 ≤ 3457892044893^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093495361 2500000000 3457892044893 10000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093494947/2500000000 : ℝ)^4627 ≤ (17289451818259/50000000000000 : ℝ)^3603 := by
    have hnat : (1093494947 : ℕ)^4627*50000000000000^3603 ≤ 17289451818259^3603*2500000000^4627 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093494947 2500000000 17289451818259 50000000000000 4627 3603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4627/1024 : ℝ)) 4627 3603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4001309787/10000000000 : ℝ), (1093495361/2500000000 : ℝ), (1093494947/2500000000 : ℝ)] ![(30842175900767/100000000000000 : ℝ), (3457892044893/10000000000000 : ℝ), (17289451818259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4001309787/10000000000 : ℝ)|^4627 ≤ (30842175900767/100000000000000 : ℝ)^3603
        have hw : |(4001309787/10000000000 : ℝ)|=(4001309787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093495361/2500000000 : ℝ)|^4627 ≤ (3457892044893/10000000000000 : ℝ)^3603
        have hw : |(1093495361/2500000000 : ℝ)|=(1093495361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093494947/2500000000 : ℝ)|^4627 ≤ (17289451818259/50000000000000 : ℝ)^3603
        have hw : |(1093494947/2500000000 : ℝ)|=(1093494947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1565_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3191/5000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58879/100000 : ℝ) ∧ (8087/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2698/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2221/20000 : ℝ) ^ (4625/1024 : ℝ) ≤ (977276926969307/20000000000000000000 : ℝ) := by
    have hpowers : (2221/20000 : ℝ)^4625 ≤ (977276926969307/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2221 : ℕ)^4625*20000000000000000000^1024 ≤ 977276926969307^1024*20000^4625 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2221 20000 977276926969307 20000000000000000000 4625 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2221/20000 : ℝ)) (X := (977276926969307/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4625/1024 : ℝ) ≤ (10967855202558879/50000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4625 ≤ (10967855202558879/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4625*50000000000000000000^1024 ≤ 10967855202558879^1024*20000^4625 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 10967855202558879 50000000000000000000 4625 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (10967855202558879/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000977276926969307/10000000000000000000 : ℝ) ≤ (2000043273232539/2000000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (10000977276926969307/10000000000000000000 : ℝ)^1024 ≤ (2000043273232539/2000000000000000 : ℝ)^4625 := by
      have hnat : (10000977276926969307 : ℕ)^1024*2000000000000000^4625 ≤ 2000043273232539^4625*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000977276926969307 10000000000000000000 2000043273232539 2000000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000043273232539/2000000000000000 : ℝ)) (X := (10000977276926969307/10000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026822095039964293/100000000000000000000 : ℝ) ≤ (2000118758736687/2000000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (100026822095039964293/100000000000000000000 : ℝ)^1024 ≤ (2000118758736687/2000000000000000 : ℝ)^4625 := by
      have hnat : (100026822095039964293 : ℕ)^1024*2000000000000000^4625 ≤ 2000118758736687^4625*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026822095039964293 100000000000000000000 2000118758736687 2000000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000118758736687/2000000000000000 : ℝ)) (X := (100026822095039964293/100000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010967855202558879/25000000000000000000 : ℝ) ≤ (400038848848167/400000000000000 : ℝ) ^ (4625/1024 : ℝ) := by
    have hpowers : (25010967855202558879/25000000000000000000 : ℝ)^1024 ≤ (400038848848167/400000000000000 : ℝ)^4625 := by
      have hnat : (25010967855202558879 : ℕ)^1024*400000000000000^4625 ≤ 400038848848167^4625*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010967855202558879 25000000000000000000 400038848848167 400000000000000 1024 4625 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400038848848167/400000000000000 : ℝ)) (X := (25010967855202558879/25000000000000000000 : ℝ)) (by norm_num) 4625 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(977276926969307/20000000000000000000 : ℝ) ≤ ((145975216728523229/146000000000000000 : ℝ)+2*(6290458679/7300000000000 : ℝ)*(2221/20000 : ℝ))^(4625/1024 : ℝ) := by
    rw [show (145975216728523229/146000000000000000 : ℝ)+2*(6290458679/7300000000000 : ℝ)*(2221/20000 : ℝ)=(2000043273232539/2000000000000000 : ℝ) by norm_num, show 1+2*(977276926969307/20000000000000000000 : ℝ)=(10000977276926969307/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10967855202558879/50000000000000000000 : ℝ)+(977276926969307/20000000000000000000 : ℝ) ≤ ((145975216728523229/146000000000000000 : ℝ)+(6290458679/7300000000000 : ℝ)*((3097/20000 : ℝ)+(2221/20000 : ℝ)))^(4625/1024 : ℝ) := by
    rw [show (145975216728523229/146000000000000000 : ℝ)+(6290458679/7300000000000 : ℝ)*((3097/20000 : ℝ)+(2221/20000 : ℝ))=(2000118758736687/2000000000000000 : ℝ) by norm_num, show 1+(10967855202558879/50000000000000000000 : ℝ)+(977276926969307/20000000000000000000 : ℝ)=(100026822095039964293/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10967855202558879/50000000000000000000 : ℝ) ≤ ((145975216728523229/146000000000000000 : ℝ)+2*(6290458679/7300000000000 : ℝ)*(3097/20000 : ℝ))^(4625/1024 : ℝ) := by
    rw [show (145975216728523229/146000000000000000 : ℝ)+2*(6290458679/7300000000000 : ℝ)*(3097/20000 : ℝ)=(400038848848167/400000000000000 : ℝ) by norm_num, show 1+2*(10967855202558879/50000000000000000000 : ℝ)=(25010967855202558879/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (145975216728523229/146000000000000000 : ℝ)*(X 1 0+X 2 0)+(6290458679/7300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (145975216728523229/146000000000000000 : ℝ)) (alpha := (6290458679/7300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (145975216728523229/146000000000000000 : ℝ)*(X 0 1+X 2 1)+(6290458679/7300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (145975216728523229/146000000000000000 : ℝ)) (alpha := (6290458679/7300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (145975216728523229/146000000000000000 : ℝ)*(X 0 2+X 1 2)+(6290458679/7300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4625/1024 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (145975216728523229/146000000000000000 : ℝ)) (alpha := (6290458679/7300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1587854763/10000000000 : ℝ)*X 0 0+(2698564479/5000000000 : ℝ)*X 0 1+(5397128131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271139663/10000000000 : ℝ)*X 1 0+(-220370557/1250000000 : ℝ)*X 1 1+(5397128667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635570139/5000000000 : ℝ)*X 2 0+(33732053/62500000 : ℝ)*X 2 1+(-1762963873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2223294269/5000000000 : ℝ)*X 0 0+(2075968707/5000000000 : ℝ)*X 0 1+(830387719/2000000000 : ℝ)*X 0 2+(2223294269/5000000000 : ℝ)*X 1 0+(2075968707/5000000000 : ℝ)*X 1 1+(830387719/2000000000 : ℝ)*X 1 2+(2223294269/5000000000 : ℝ)*X 2 0+(2075968707/5000000000 : ℝ)*X 2 1+(830387719/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2002477289/10000000000 : ℝ)*X 0 0+(104899277/200000000 : ℝ)*X 0 1+(2622482079/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2688328021/5000000000 : ℝ)*X 1 0+(-1826472593/10000000000 : ℝ)*X 1 1+(1048992821/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5376655691/10000000000 : ℝ)*X 2 0+(5244964519/10000000000 : ℝ)*X 2 1+(-1826472511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((808434043/2000000000 : ℝ)*X 0 0+(4354019647/10000000000 : ℝ)*X 0 1+(2177009367/5000000000 : ℝ)*X 0 2+(808434043/2000000000 : ℝ)*X 1 0+(4354019647/10000000000 : ℝ)*X 1 1+(2177009367/5000000000 : ℝ)*X 1 2+(808434043/2000000000 : ℝ)*X 2 0+(4354019647/10000000000 : ℝ)*X 2 1+(2177009367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-382922381/2000000000 : ℝ)*X 0 0+(5137809403/10000000000 : ℝ)*X 0 1+(2708707501/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314267079/2500000000 : ℝ)*X 1 0+(-1754264071/10000000000 : ℝ)*X 1 1+(5417415769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((657133513/1250000000 : ℝ)*X 2 0+(2708708103/5000000000 : ℝ)*X 2 1+(-1754263759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2249681037/5000000000 : ℝ)*X 0 0+(1031240453/2500000000 : ℝ)*X 0 1+(82499237/200000000 : ℝ)*X 0 2+(2249681037/5000000000 : ℝ)*X 1 0+(1031240453/2500000000 : ℝ)*X 1 1+(82499237/200000000 : ℝ)*X 1 2+(2249681037/5000000000 : ℝ)*X 2 0+(1031240453/2500000000 : ℝ)*X 2 1+(82499237/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-418851183/2500000000 : ℝ)*X 0 0+(1100200823/2000000000 : ℝ)*X 0 1+(163434817/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1346773181/2500000000 : ℝ)*X 1 0+(-366516733/2000000000 : ℝ)*X 1 1+(2614957171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5387093673/10000000000 : ℝ)*X 2 0+(522991361/1000000000 : ℝ)*X 2 1+(-1832583363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4001309787/10000000000 : ℝ)*X 0 0+(1093495361/2500000000 : ℝ)*X 0 1+(1093494947/2500000000 : ℝ)*X 0 2+(4001309787/10000000000 : ℝ)*X 1 0+(1093495361/2500000000 : ℝ)*X 1 1+(1093494947/2500000000 : ℝ)*X 1 2+(4001309787/10000000000 : ℝ)*X 2 0+(1093495361/2500000000 : ℝ)*X 2 1+(1093494947/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1565_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3191/5000 : ℝ) ≤ (-232933725128080581810561837/365000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71067483/50000000000000 : ℝ)*(lower0) + (360853/12500000000000 : ℝ)*(upper3) + (1108749/3125000000000 : ℝ)*(lower4) + (2300558740928027/100000000000000 : ℝ)*(major0) + (2300558740928027/100000000000000 : ℝ)*(major1) + (2300558740928027/100000000000000 : ℝ)*(major2) + (20485159/1000000000000 : ℝ)*(sp1) + (162497765559381/5000000000000 : ℝ)*(sp4) + (324995390398851/10000000000000 : ℝ)*(sp5) + (812475341262197/25000000000000 : ℝ)*(sp6) + (274484451605517/20000000000000 : ℝ)*(sp7) + (641316791/100000000000000 : ℝ)*(sp8) + (54587455623/100000000000000 : ℝ)*(sp14) + (4592827/39062500000 : ℝ)*(sp15) + (274486803132941/20000000000000 : ℝ)*(f.failure) + (324995595250441/10000000000000 : ℝ)*(f.sum) + (1991542455633/365000000000000000000000000 : ℝ)*base65 + (57775800987500817/14600000000000000000000000000000 : ℝ)*base68 + (65715922569900817/14600000000000000000000000000000 : ℝ)*base70 + (39074659922299183/14600000000000000000000000000000 : ℝ)*base71 + (24400186897/5703125000000000000000000 : ℝ)*base73 + (50112939333299183/14600000000000000000000000000000 : ℝ)*base75 + (39155157415900817/14600000000000000000000000000000 : ℝ)*base78 + (70798234269099183/14600000000000000000000000000000 : ℝ)*base79 + (92924870697/91250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (869369/1000000000000000000000 : ℝ)*base90 + (869369/1000000000000000000000 : ℝ)*base92 + (869369/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58879/100000 : ℝ) ≤ (429832108432401308871673688991/730000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15094329/100000000000000 : ℝ)*(upper0) + (58658977/20000000000000 : ℝ)*(lower1) + (4529461/1562500000000 : ℝ)*(upper4) + (476089902036393/20000000000000 : ℝ)*(major0) + (476089902036393/20000000000000 : ℝ)*(major1) + (476089902036393/20000000000000 : ℝ)*(major2) + (830293114815369/25000000000000 : ℝ)*(sp0) + (3321115635164689/100000000000000 : ℝ)*(sp1) + (830294122895993/25000000000000 : ℝ)*(sp2) + (1420088828445847/100000000000000 : ℝ)*(sp3) + (1316329221/25000000000000 : ℝ)*(sp7) + (543042499/10000000000000 : ℝ)*(sp8) + (62254521777/100000000000000 : ℝ)*(sp9) + (1398102493/100000000000000 : ℝ)*(sp10) + (142009409376273/10000000000000 : ℝ)*(f.failure) + (1660588944843233/50000000000000 : ℝ)*(f.sum) + (13393374537/73000000000000000000000000 : ℝ)*base66 + (15102127544467003/2920000000000000000000000000000 : ℝ)*base68 + (28418812577627003/2920000000000000000000000000000 : ℝ)*base70 + (20224819327387003/2920000000000000000000000000000 : ℝ)*base72 + (23113062601/2281250000000000000000000 : ℝ)*base73 + (30976323018427003/2920000000000000000000000000000 : ℝ)*base76 + (1472375362467003/2920000000000000000000000000000 : ℝ)*base78 + (85642774726732997/2920000000000000000000000000000 : ℝ)*base79 + (299347475847/73000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2810157/500000000000000000000 : ℝ)*base90 + (2810157/500000000000000000000 : ℝ)*base92 + (2810157/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (8087/10000 : ℝ) ≤ (147592210812710736343546371/182500000000000000000000000 : ℝ) := by norm_num
    linear_combination (20975869/100000000000000 : ℝ)*(upper0) + (666177/5000000000000 : ℝ)*(lower1) + (58637929/100000000000000 : ℝ)*(upper4) + (641896827308789/25000000000000 : ℝ)*(major0) + (641896827308789/25000000000000 : ℝ)*(major1) + (641896827308789/25000000000000 : ℝ)*(major2) + (4169169097/25000000000000 : ℝ)*(sp0) + (145326065419/100000000000000 : ℝ)*(sp1) + (240867345713/100000000000000 : ℝ)*(sp2) + (3713859481/4000000000000 : ℝ)*(sp3) + (357646640868093/10000000000000 : ℝ)*(sp8) + (1788168879645949/50000000000000 : ℝ)*(sp9) + (894060554502901/25000000000000 : ℝ)*(sp10) + (76582060259949/5000000000000 : ℝ)*(sp11) + (382933512921501/25000000000000 : ℝ)*(f.failure) + (1788241542678659/50000000000000 : ℝ)*(f.sum) + (75060752727/45625000000000000000000000 : ℝ)*base66 + (5069303717620319/3650000000000000000000000000000 : ℝ)*base68 + (16250684367970319/3650000000000000000000000000000 : ℝ)*base70 + (21174970334229681/3650000000000000000000000000000 : ℝ)*base71 + (279888187201/91250000000000000000000000 : ℝ)*base73 + (15760460415479681/3650000000000000000000000000000 : ℝ)*base75 + (17377913786979681/3650000000000000000000000000000 : ℝ)*base77 + (35705331138120319/3650000000000000000000000000000 : ℝ)*base80 + (29734341213/182500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10830409/1250000000000000000000 : ℝ)*base90 + (10830409/1250000000000000000000 : ℝ)*base92 + (10830409/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-2698/3125 : ℝ) ≤ (-3151157417806669456602867892377/3650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (352761501/100000000000000 : ℝ)*(lower2) + (49349547/20000000000000 : ℝ)*(upper3) + (98912939/100000000000000 : ℝ)*(upper5) + (1303958168848043/50000000000000 : ℝ)*(major0) + (1303958168848043/50000000000000 : ℝ)*(major1) + (1303958168848043/50000000000000 : ℝ)*(major2) + (614503979/6250000000000 : ℝ)*(sp0) + (4493293429/2000000000000 : ℝ)*(sp5) + (111028474859/50000000000000 : ℝ)*(sp6) + (4805815331/50000000000000 : ℝ)*(sp7) + (3688807577224471/100000000000000 : ℝ)*(sp12) + (1844296372308343/50000000000000 : ℝ)*(sp13) + (1844297676169209/50000000000000 : ℝ)*(sp14) + (97236459236667/6250000000000 : ℝ)*(sp15) + (777896479708667/50000000000000 : ℝ)*(f.failure) + (737763481857627/20000000000000 : ℝ)*(f.sum) + (204574028011/91250000000000000000000000 : ℝ)*base65 + (15050098200069153/7300000000000000000000000000000 : ℝ)*base68 + (30901656138969153/7300000000000000000000000000000 : ℝ)*base70 + (42024136932769153/7300000000000000000000000000000 : ℝ)*base72 + (126608387121/22812500000000000000000000 : ℝ)*base74 + (4395816433169153/7300000000000000000000000000000 : ℝ)*base76 + (40864757415169153/7300000000000000000000000000000 : ℝ)*base78 + (35325441918569153/7300000000000000000000000000000 : ℝ)*base80 + (727756004507/182500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10759697/2500000000000000000000 : ℝ)*base89 + (10759697/2500000000000000000000 : ℝ)*base91 + (10759697/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1565_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3191/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(58879/100000 : ℝ) else (8087/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2698/3125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1565_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1565_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3191/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(58879/100000 : ℝ) else (8087/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2698/3125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1565_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4625/1024 : ℝ) ≤ p) (hpb : p ≤ (4627/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83813091/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3191/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(58879/100000 : ℝ) else (8087/10000 : ℝ) ≤ X j i ∧ X j i ≤ (2698/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1565_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

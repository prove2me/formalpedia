-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1588_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:36:18.36064+00:00
-- url     : https://prove2.me/submissions/92229d7f-539f-4d3f-a9c2-abc19701689b

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
theorem support_rectangle_w1588_box_0 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-780175519/5000000000 : ℝ)*x 0 + (5394668159/10000000000 : ℝ)*x 1 + (5394668381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (780175519/5000000000 : ℝ)^4673 ≤ (9264467546227/100000000000000 : ℝ)^3649 := by
    have hnat : (780175519 : ℕ)^4673*100000000000000^3649 ≤ 9264467546227^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780175519 5000000000 9264467546227 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394668159/10000000000 : ℝ)^4673 ≤ (4536776502253/10000000000000 : ℝ)^3649 := by
    have hnat : (5394668159 : ℕ)^4673*10000000000000^3649 ≤ 4536776502253^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394668159 10000000000 4536776502253 10000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394668381/10000000000 : ℝ)^4673 ≤ (45367767413409/100000000000000 : ℝ)^3649 := by
    have hnat : (5394668381 : ℕ)^4673*100000000000000^3649 ≤ 45367767413409^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394668381 10000000000 45367767413409 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-780175519/5000000000 : ℝ), (5394668159/10000000000 : ℝ), (5394668381/10000000000 : ℝ)] ![(9264467546227/100000000000000 : ℝ), (4536776502253/10000000000000 : ℝ), (45367767413409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-780175519/5000000000 : ℝ)|^4673 ≤ (9264467546227/100000000000000 : ℝ)^3649
        have hw : |(-780175519/5000000000 : ℝ)|=(780175519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394668159/10000000000 : ℝ)|^4673 ≤ (4536776502253/10000000000000 : ℝ)^3649
        have hw : |(5394668159/10000000000 : ℝ)|=(5394668159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394668381/10000000000 : ℝ)|^4673 ≤ (45367767413409/100000000000000 : ℝ)^3649
        have hw : |(5394668381/10000000000 : ℝ)|=(5394668381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_1 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054223143/2000000000 : ℝ)*x 0 + (-433049103/2500000000 : ℝ)*x 1 + (5394668189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054223143/2000000000 : ℝ)^4673 ≤ (22020719523309/50000000000000 : ℝ)^3649 := by
    have hnat : (1054223143 : ℕ)^4673*50000000000000^3649 ≤ 22020719523309^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054223143 2000000000 22020719523309 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433049103/2500000000 : ℝ)^4673 ≤ (10590795592401/100000000000000 : ℝ)^3649 := by
    have hnat : (433049103 : ℕ)^4673*100000000000000^3649 ≤ 10590795592401^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433049103 2500000000 10590795592401 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394668189/10000000000 : ℝ)^4673 ≤ (22683882672811/50000000000000 : ℝ)^3649 := by
    have hnat : (5394668189 : ℕ)^4673*50000000000000^3649 ≤ 22683882672811^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394668189 10000000000 22683882672811 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054223143/2000000000 : ℝ), (-433049103/2500000000 : ℝ), (5394668189/10000000000 : ℝ)] ![(22020719523309/50000000000000 : ℝ), (10590795592401/100000000000000 : ℝ), (22683882672811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054223143/2000000000 : ℝ)|^4673 ≤ (22020719523309/50000000000000 : ℝ)^3649
        have hw : |(1054223143/2000000000 : ℝ)|=(1054223143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433049103/2500000000 : ℝ)|^4673 ≤ (10590795592401/100000000000000 : ℝ)^3649
        have hw : |(-433049103/2500000000 : ℝ)|=(433049103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394668189/10000000000 : ℝ)|^4673 ≤ (22683882672811/50000000000000 : ℝ)^3649
        have hw : |(5394668189/10000000000 : ℝ)|=(5394668189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_2 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271115389/10000000000 : ℝ)*x 0 + (5394668463/10000000000 : ℝ)*x 1 + (-1732196481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271115389/10000000000 : ℝ)^4673 ≤ (22020717779221/50000000000000 : ℝ)^3649 := by
    have hnat : (5271115389 : ℕ)^4673*50000000000000^3649 ≤ 22020717779221^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271115389 10000000000 22020717779221 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394668463/10000000000 : ℝ)^4673 ≤ (22683884148263/50000000000000 : ℝ)^3649 := by
    have hnat : (5394668463 : ℕ)^4673*50000000000000^3649 ≤ 22683884148263^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394668463 10000000000 22683884148263 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732196481/10000000000 : ℝ)^4673 ≤ (10590796132661/100000000000000 : ℝ)^3649 := by
    have hnat : (1732196481 : ℕ)^4673*100000000000000^3649 ≤ 10590796132661^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732196481 10000000000 10590796132661 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271115389/10000000000 : ℝ), (5394668463/10000000000 : ℝ), (-1732196481/10000000000 : ℝ)] ![(22020717779221/50000000000000 : ℝ), (22683884148263/50000000000000 : ℝ), (10590796132661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271115389/10000000000 : ℝ)|^4673 ≤ (22020717779221/50000000000000 : ℝ)^3649
        have hw : |(5271115389/10000000000 : ℝ)|=(5271115389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394668463/10000000000 : ℝ)|^4673 ≤ (22683884148263/50000000000000 : ℝ)^3649
        have hw : |(5394668463/10000000000 : ℝ)|=(5394668463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1732196481/10000000000 : ℝ)|^4673 ≤ (10590796132661/100000000000000 : ℝ)^3649
        have hw : |(-1732196481/10000000000 : ℝ)|=(1732196481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_3 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4435690089/10000000000 : ℝ)*x 0 + (1035540543/2500000000 : ℝ)*x 1 + (828432407/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4435690089/10000000000 : ℝ)^4673 ≤ (17654675753287/50000000000000 : ℝ)^3649 := by
    have hnat : (4435690089 : ℕ)^4673*50000000000000^3649 ≤ 17654675753287^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435690089 10000000000 17654675753287 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035540543/2500000000 : ℝ)^4673 ≤ (32345324922801/100000000000000 : ℝ)^3649 := by
    have hnat : (1035540543 : ℕ)^4673*100000000000000^3649 ≤ 32345324922801^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035540543 2500000000 32345324922801 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828432407/2000000000 : ℝ)^4673 ≤ (32345323552781/100000000000000 : ℝ)^3649 := by
    have hnat : (828432407 : ℕ)^4673*100000000000000^3649 ≤ 32345323552781^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828432407 2000000000 32345323552781 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4435690089/10000000000 : ℝ), (1035540543/2500000000 : ℝ), (828432407/2000000000 : ℝ)] ![(17654675753287/50000000000000 : ℝ), (32345324922801/100000000000000 : ℝ), (32345323552781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4435690089/10000000000 : ℝ)|^4673 ≤ (17654675753287/50000000000000 : ℝ)^3649
        have hw : |(4435690089/10000000000 : ℝ)|=(4435690089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035540543/2500000000 : ℝ)|^4673 ≤ (32345324922801/100000000000000 : ℝ)^3649
        have hw : |(1035540543/2500000000 : ℝ)|=(1035540543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828432407/2000000000 : ℝ)|^4673 ≤ (32345323552781/100000000000000 : ℝ)^3649
        have hw : |(828432407/2000000000 : ℝ)|=(828432407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_4 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393531141/2000000000 : ℝ)*x 0 + (8392533/16000000 : ℝ)*x 1 + (1049066647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393531141/2000000000 : ℝ)^4673 ≤ (2493697066631/20000000000000 : ℝ)^3649 := by
    have hnat : (393531141 : ℕ)^4673*20000000000000^3649 ≤ 2493697066631^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393531141 2000000000 2493697066631 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8392533/16000000 : ℝ)^4673 ≤ (1750630269507/4000000000000 : ℝ)^3649 := by
    have hnat : (8392533 : ℕ)^4673*4000000000000^3649 ≤ 1750630269507^3649*16000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8392533 16000000 1750630269507 4000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049066647/2000000000 : ℝ)^4673 ≤ (43765757913049/100000000000000 : ℝ)^3649 := by
    have hnat : (1049066647 : ℕ)^4673*100000000000000^3649 ≤ 43765757913049^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049066647 2000000000 43765757913049 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393531141/2000000000 : ℝ), (8392533/16000000 : ℝ), (1049066647/2000000000 : ℝ)] ![(2493697066631/20000000000000 : ℝ), (1750630269507/4000000000000 : ℝ), (43765757913049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393531141/2000000000 : ℝ)|^4673 ≤ (2493697066631/20000000000000 : ℝ)^3649
        have hw : |(-393531141/2000000000 : ℝ)|=(393531141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8392533/16000000 : ℝ)|^4673 ≤ (1750630269507/4000000000000 : ℝ)^3649
        have hw : |(8392533/16000000 : ℝ)|=(8392533/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049066647/2000000000 : ℝ)|^4673 ≤ (43765757913049/100000000000000 : ℝ)^3649
        have hw : |(1049066647/2000000000 : ℝ)|=(1049066647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_5 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537449451/1000000000 : ℝ)*x 0 + (-1794824347/10000000000 : ℝ)*x 1 + (2622666539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537449451/1000000000 : ℝ)^4673 ≤ (45150614496231/100000000000000 : ℝ)^3649 := by
    have hnat : (537449451 : ℕ)^4673*100000000000000^3649 ≤ 45150614496231^3649*1000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537449451 1000000000 45150614496231 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1794824347/10000000000 : ℝ)^4673 ≤ (173181707091/1562500000000 : ℝ)^3649 := by
    have hnat : (1794824347 : ℕ)^4673*1562500000000^3649 ≤ 173181707091^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794824347 10000000000 173181707091 1562500000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622666539/5000000000 : ℝ)^4673 ≤ (4376575623547/10000000000000 : ℝ)^3649 := by
    have hnat : (2622666539 : ℕ)^4673*10000000000000^3649 ≤ 4376575623547^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622666539 5000000000 4376575623547 10000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537449451/1000000000 : ℝ), (-1794824347/10000000000 : ℝ), (2622666539/5000000000 : ℝ)] ![(45150614496231/100000000000000 : ℝ), (173181707091/1562500000000 : ℝ), (4376575623547/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537449451/1000000000 : ℝ)|^4673 ≤ (45150614496231/100000000000000 : ℝ)^3649
        have hw : |(537449451/1000000000 : ℝ)|=(537449451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1794824347/10000000000 : ℝ)|^4673 ≤ (173181707091/1562500000000 : ℝ)^3649
        have hw : |(-1794824347/10000000000 : ℝ)|=(1794824347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622666539/5000000000 : ℝ)|^4673 ≤ (4376575623547/10000000000000 : ℝ)^3649
        have hw : |(2622666539/5000000000 : ℝ)|=(2622666539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_6 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074899013/2000000000 : ℝ)*x 0 + (524533281/1000000000 : ℝ)*x 1 + (-358964791/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074899013/2000000000 : ℝ)^4673 ≤ (45150620467147/100000000000000 : ℝ)^3649 := by
    have hnat : (1074899013 : ℕ)^4673*100000000000000^3649 ≤ 45150620467147^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074899013 2000000000 45150620467147 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524533281/1000000000 : ℝ)^4673 ≤ (5470719171479/12500000000000 : ℝ)^3649 := by
    have hnat : (524533281 : ℕ)^4673*12500000000000^3649 ≤ 5470719171479^3649*1000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524533281 1000000000 5470719171479 12500000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (358964791/2000000000 : ℝ)^4673 ≤ (11083626153779/100000000000000 : ℝ)^3649 := by
    have hnat : (358964791 : ℕ)^4673*100000000000000^3649 ≤ 11083626153779^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358964791 2000000000 11083626153779 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074899013/2000000000 : ℝ), (524533281/1000000000 : ℝ), (-358964791/2000000000 : ℝ)] ![(45150620467147/100000000000000 : ℝ), (5470719171479/12500000000000 : ℝ), (11083626153779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074899013/2000000000 : ℝ)|^4673 ≤ (45150620467147/100000000000000 : ℝ)^3649
        have hw : |(1074899013/2000000000 : ℝ)|=(1074899013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524533281/1000000000 : ℝ)|^4673 ≤ (5470719171479/12500000000000 : ℝ)^3649
        have hw : |(524533281/1000000000 : ℝ)|=(524533281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-358964791/2000000000 : ℝ)|^4673 ≤ (11083626153779/100000000000000 : ℝ)^3649
        have hw : |(-358964791/2000000000 : ℝ)|=(358964791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_7 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (100820827/250000000 : ℝ)*x 0 + (217173213/500000000 : ℝ)*x 1 + (4343465871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100820827/250000000 : ℝ)^4673 ≤ (15628046480449/50000000000000 : ℝ)^3649 := by
    have hnat : (100820827 : ℕ)^4673*50000000000000^3649 ≤ 15628046480449^3649*250000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100820827 250000000 15628046480449 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217173213/500000000 : ℝ)^4673 ≤ (6874389070179/20000000000000 : ℝ)^3649 := by
    have hnat : (217173213 : ℕ)^4673*20000000000000^3649 ≤ 6874389070179^3649*500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217173213 500000000 6874389070179 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4343465871/10000000000 : ℝ)^4673 ≤ (34371961677103/100000000000000 : ℝ)^3649 := by
    have hnat : (4343465871 : ℕ)^4673*100000000000000^3649 ≤ 34371961677103^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343465871 10000000000 34371961677103 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100820827/250000000 : ℝ), (217173213/500000000 : ℝ), (4343465871/10000000000 : ℝ)] ![(15628046480449/50000000000000 : ℝ), (6874389070179/20000000000000 : ℝ), (34371961677103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100820827/250000000 : ℝ)|^4673 ≤ (15628046480449/50000000000000 : ℝ)^3649
        have hw : |(100820827/250000000 : ℝ)|=(100820827/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217173213/500000000 : ℝ)|^4673 ≤ (6874389070179/20000000000000 : ℝ)^3649
        have hw : |(217173213/500000000 : ℝ)|=(217173213/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4343465871/10000000000 : ℝ)|^4673 ≤ (34371961677103/100000000000000 : ℝ)^3649
        have hw : |(4343465871/10000000000 : ℝ)|=(4343465871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_8 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-940624959/5000000000 : ℝ)*x 0 + (5139938623/10000000000 : ℝ)*x 1 + (54148789/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940624959/5000000000 : ℝ)^4673 ≤ (1177167235319/10000000000000 : ℝ)^3649 := by
    have hnat : (940624959 : ℕ)^4673*10000000000000^3649 ≤ 1177167235319^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940624959 5000000000 1177167235319 10000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139938623/10000000000 : ℝ)^4673 ≤ (42642784193051/100000000000000 : ℝ)^3649 := by
    have hnat : (5139938623 : ℕ)^4673*100000000000000^3649 ≤ 42642784193051^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139938623 10000000000 42642784193051 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54148789/100000000 : ℝ)^4673 ≤ (9117108687757/20000000000000 : ℝ)^3649 := by
    have hnat : (54148789 : ℕ)^4673*20000000000000^3649 ≤ 9117108687757^3649*100000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54148789 100000000 9117108687757 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-940624959/5000000000 : ℝ), (5139938623/10000000000 : ℝ), (54148789/100000000 : ℝ)] ![(1177167235319/10000000000000 : ℝ), (42642784193051/100000000000000 : ℝ), (9117108687757/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-940624959/5000000000 : ℝ)|^4673 ≤ (1177167235319/10000000000000 : ℝ)^3649
        have hw : |(-940624959/5000000000 : ℝ)|=(940624959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139938623/10000000000 : ℝ)|^4673 ≤ (42642784193051/100000000000000 : ℝ)^3649
        have hw : |(5139938623/10000000000 : ℝ)|=(5139938623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54148789/100000000 : ℝ)|^4673 ≤ (9117108687757/20000000000000 : ℝ)^3649
        have hw : |(54148789/100000000 : ℝ)|=(54148789/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_9 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257121833/10000000000 : ℝ)*x 0 + (-861746387/5000000000 : ℝ)*x 1 + (5414878871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257121833/10000000000 : ℝ)^4673 ≤ (43891761324243/100000000000000 : ℝ)^3649 := by
    have hnat : (5257121833 : ℕ)^4673*100000000000000^3649 ≤ 43891761324243^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257121833 10000000000 43891761324243 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861746387/5000000000 : ℝ)^4673 ≤ (526134776377/5000000000000 : ℝ)^3649 := by
    have hnat : (861746387 : ℕ)^4673*5000000000000^3649 ≤ 526134776377^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861746387 5000000000 526134776377 5000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414878871/10000000000 : ℝ)^4673 ≤ (9117108625227/20000000000000 : ℝ)^3649 := by
    have hnat : (5414878871 : ℕ)^4673*20000000000000^3649 ≤ 9117108625227^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414878871 10000000000 9117108625227 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257121833/10000000000 : ℝ), (-861746387/5000000000 : ℝ), (5414878871/10000000000 : ℝ)] ![(43891761324243/100000000000000 : ℝ), (526134776377/5000000000000 : ℝ), (9117108625227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257121833/10000000000 : ℝ)|^4673 ≤ (43891761324243/100000000000000 : ℝ)^3649
        have hw : |(5257121833/10000000000 : ℝ)|=(5257121833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-861746387/5000000000 : ℝ)|^4673 ≤ (526134776377/5000000000000 : ℝ)^3649
        have hw : |(-861746387/5000000000 : ℝ)|=(861746387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414878871/10000000000 : ℝ)|^4673 ≤ (9117108625227/20000000000000 : ℝ)^3649
        have hw : |(5414878871/10000000000 : ℝ)|=(5414878871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_10 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257121731/10000000000 : ℝ)*x 0 + (5414878981/10000000000 : ℝ)*x 1 + (-861746381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257121731/10000000000 : ℝ)^4673 ≤ (685808753651/1562500000000 : ℝ)^3649 := by
    have hnat : (5257121731 : ℕ)^4673*1562500000000^3649 ≤ 685808753651^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257121731 10000000000 685808753651 1562500000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414878981/10000000000 : ℝ)^4673 ≤ (45585544312049/100000000000000 : ℝ)^3649 := by
    have hnat : (5414878981 : ℕ)^4673*100000000000000^3649 ≤ 45585544312049^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414878981 10000000000 45585544312049 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861746381/5000000000 : ℝ)^4673 ≤ (2104539086743/20000000000000 : ℝ)^3649 := by
    have hnat : (861746381 : ℕ)^4673*20000000000000^3649 ≤ 2104539086743^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861746381 5000000000 2104539086743 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257121731/10000000000 : ℝ), (5414878981/10000000000 : ℝ), (-861746381/5000000000 : ℝ)] ![(685808753651/1562500000000 : ℝ), (45585544312049/100000000000000 : ℝ), (2104539086743/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257121731/10000000000 : ℝ)|^4673 ≤ (685808753651/1562500000000 : ℝ)^3649
        have hw : |(5257121731/10000000000 : ℝ)|=(5257121731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414878981/10000000000 : ℝ)|^4673 ≤ (45585544312049/100000000000000 : ℝ)^3649
        have hw : |(5414878981/10000000000 : ℝ)|=(5414878981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-861746381/5000000000 : ℝ)|^4673 ≤ (2104539086743/20000000000000 : ℝ)^3649
        have hw : |(-861746381/5000000000 : ℝ)|=(861746381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_11 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4489068999/10000000000 : ℝ)*x 0 + (4114883911/10000000000 : ℝ)*x 1 + (411488379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489068999/10000000000 : ℝ)^4673 ≤ (35854419595513/100000000000000 : ℝ)^3649 := by
    have hnat : (4489068999 : ℕ)^4673*100000000000000^3649 ≤ 35854419595513^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489068999 10000000000 35854419595513 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4114883911/10000000000 : ℝ)^4673 ≤ (8018197698501/25000000000000 : ℝ)^3649 := by
    have hnat : (4114883911 : ℕ)^4673*25000000000000^3649 ≤ 8018197698501^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114883911 10000000000 8018197698501 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411488379/1000000000 : ℝ)^4673 ≤ (32072789586227/100000000000000 : ℝ)^3649 := by
    have hnat : (411488379 : ℕ)^4673*100000000000000^3649 ≤ 32072789586227^3649*1000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411488379 1000000000 32072789586227 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489068999/10000000000 : ℝ), (4114883911/10000000000 : ℝ), (411488379/1000000000 : ℝ)] ![(35854419595513/100000000000000 : ℝ), (8018197698501/25000000000000 : ℝ), (32072789586227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489068999/10000000000 : ℝ)|^4673 ≤ (35854419595513/100000000000000 : ℝ)^3649
        have hw : |(4489068999/10000000000 : ℝ)|=(4489068999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4114883911/10000000000 : ℝ)|^4673 ≤ (8018197698501/25000000000000 : ℝ)^3649
        have hw : |(4114883911/10000000000 : ℝ)|=(4114883911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(411488379/1000000000 : ℝ)|^4673 ≤ (32072789586227/100000000000000 : ℝ)^3649
        have hw : |(411488379/1000000000 : ℝ)|=(411488379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_12 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1646338721/10000000000 : ℝ)*x 0 + (5496901027/10000000000 : ℝ)*x 1 + (653785587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1646338721/10000000000 : ℝ)^4673 ≤ (198465499249/2000000000000 : ℝ)^3649 := by
    have hnat : (1646338721 : ℕ)^4673*2000000000000^3649 ≤ 198465499249^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646338721 10000000000 198465499249 2000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496901027/10000000000 : ℝ)^4673 ≤ (23235849608931/50000000000000 : ℝ)^3649 := by
    have hnat : (5496901027 : ℕ)^4673*50000000000000^3649 ≤ 23235849608931^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496901027 10000000000 23235849608931 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653785587/1250000000 : ℝ)^4673 ≤ (1362657056349/3125000000000 : ℝ)^3649 := by
    have hnat : (653785587 : ℕ)^4673*3125000000000^3649 ≤ 1362657056349^3649*1250000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653785587 1250000000 1362657056349 3125000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1646338721/10000000000 : ℝ), (5496901027/10000000000 : ℝ), (653785587/1250000000 : ℝ)] ![(198465499249/2000000000000 : ℝ), (23235849608931/50000000000000 : ℝ), (1362657056349/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1646338721/10000000000 : ℝ)|^4673 ≤ (198465499249/2000000000000 : ℝ)^3649
        have hw : |(-1646338721/10000000000 : ℝ)|=(1646338721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496901027/10000000000 : ℝ)|^4673 ≤ (23235849608931/50000000000000 : ℝ)^3649
        have hw : |(5496901027/10000000000 : ℝ)|=(5496901027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653785587/1250000000 : ℝ)|^4673 ≤ (1362657056349/3125000000000 : ℝ)^3649
        have hw : |(653785587/1250000000 : ℝ)|=(653785587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_13 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692456367/5000000000 : ℝ)*x 0 + (-1800967817/10000000000 : ℝ)*x 1 + (653785691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692456367/5000000000 : ℝ)^4673 ≤ (22631364229449/50000000000000 : ℝ)^3649 := by
    have hnat : (2692456367 : ℕ)^4673*50000000000000^3649 ≤ 22631364229449^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692456367 5000000000 22631364229449 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1800967817/10000000000 : ℝ)^4673 ≤ (2226447368037/20000000000000 : ℝ)^3649 := by
    have hnat : (1800967817 : ℕ)^4673*20000000000000^3649 ≤ 2226447368037^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800967817 10000000000 2226447368037 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653785691/1250000000 : ℝ)^4673 ≤ (43605034686103/100000000000000 : ℝ)^3649 := by
    have hnat : (653785691 : ℕ)^4673*100000000000000^3649 ≤ 43605034686103^3649*1250000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653785691 1250000000 43605034686103 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692456367/5000000000 : ℝ), (-1800967817/10000000000 : ℝ), (653785691/1250000000 : ℝ)] ![(22631364229449/50000000000000 : ℝ), (2226447368037/20000000000000 : ℝ), (43605034686103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692456367/5000000000 : ℝ)|^4673 ≤ (22631364229449/50000000000000 : ℝ)^3649
        have hw : |(2692456367/5000000000 : ℝ)|=(2692456367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1800967817/10000000000 : ℝ)|^4673 ≤ (2226447368037/20000000000000 : ℝ)^3649
        have hw : |(-1800967817/10000000000 : ℝ)|=(1800967817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653785691/1250000000 : ℝ)|^4673 ≤ (43605034686103/100000000000000 : ℝ)^3649
        have hw : |(653785691/1250000000 : ℝ)|=(653785691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_14 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346228451/2500000000 : ℝ)*x 0 + (5230284281/10000000000 : ℝ)*x 1 + (-450242011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346228451/2500000000 : ℝ)^4673 ≤ (45262739976651/100000000000000 : ℝ)^3649 := by
    have hnat : (1346228451 : ℕ)^4673*100000000000000^3649 ≤ 45262739976651^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346228451 2500000000 45262739976651 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230284281/10000000000 : ℝ)^4673 ≤ (21802510686189/50000000000000 : ℝ)^3649 := by
    have hnat : (5230284281 : ℕ)^4673*50000000000000^3649 ≤ 21802510686189^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230284281 10000000000 21802510686189 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450242011/2500000000 : ℝ)^4673 ≤ (5566119318543/50000000000000 : ℝ)^3649 := by
    have hnat : (450242011 : ℕ)^4673*50000000000000^3649 ≤ 5566119318543^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450242011 2500000000 5566119318543 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346228451/2500000000 : ℝ), (5230284281/10000000000 : ℝ), (-450242011/2500000000 : ℝ)] ![(45262739976651/100000000000000 : ℝ), (21802510686189/50000000000000 : ℝ), (5566119318543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346228451/2500000000 : ℝ)|^4673 ≤ (45262739976651/100000000000000 : ℝ)^3649
        have hw : |(1346228451/2500000000 : ℝ)|=(1346228451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230284281/10000000000 : ℝ)|^4673 ≤ (21802510686189/50000000000000 : ℝ)^3649
        have hw : |(5230284281/10000000000 : ℝ)|=(5230284281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-450242011/2500000000 : ℝ)|^4673 ≤ (5566119318543/50000000000000 : ℝ)^3649
        have hw : |(-450242011/2500000000 : ℝ)|=(450242011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_box_15 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1995687001/5000000000 : ℝ)*x 0 + (872745057/2000000000 : ℝ)*x 1 + (436372433/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995687001/5000000000 : ℝ)^4673 ≤ (1927824477353/6250000000000 : ℝ)^3649 := by
    have hnat : (1995687001 : ℕ)^4673*6250000000000^3649 ≤ 1927824477353^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995687001 5000000000 1927824477353 6250000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872745057/2000000000 : ℝ)^4673 ≤ (3457740901731/10000000000000 : ℝ)^3649 := by
    have hnat : (872745057 : ℕ)^4673*10000000000000^3649 ≤ 3457740901731^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872745057 2000000000 3457740901731 10000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436372433/1000000000 : ℝ)^4673 ≤ (6915479865299/20000000000000 : ℝ)^3649 := by
    have hnat : (436372433 : ℕ)^4673*20000000000000^3649 ≤ 6915479865299^3649*1000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436372433 1000000000 6915479865299 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1995687001/5000000000 : ℝ), (872745057/2000000000 : ℝ), (436372433/1000000000 : ℝ)] ![(1927824477353/6250000000000 : ℝ), (3457740901731/10000000000000 : ℝ), (6915479865299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1995687001/5000000000 : ℝ)|^4673 ≤ (1927824477353/6250000000000 : ℝ)^3649
        have hw : |(1995687001/5000000000 : ℝ)|=(1995687001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(872745057/2000000000 : ℝ)|^4673 ≤ (3457740901731/10000000000000 : ℝ)^3649
        have hw : |(872745057/2000000000 : ℝ)|=(872745057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(436372433/1000000000 : ℝ)|^4673 ≤ (6915479865299/20000000000000 : ℝ)^3649
        have hw : |(436372433/1000000000 : ℝ)|=(436372433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1588_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63861/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58989/100000 : ℝ) ∧ (40549/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21619/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5589/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5589/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5589/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5589/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5589/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5589/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5589/50000 : ℝ) ^ (4671/1024 : ℝ) ≤ (912264044053313/20000000000000000000 : ℝ) := by
    have hpowers : (5589/50000 : ℝ)^4671 ≤ (912264044053313/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5589 : ℕ)^4671*20000000000000000000^1024 ≤ 912264044053313^1024*50000^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5589 50000 912264044053313 20000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5589/50000 : ℝ)) (X := (912264044053313/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4671/1024 : ℝ) ≤ (10080338547751309/50000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4671 ≤ (10080338547751309/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4671*50000000000000000000^1024 ≤ 10080338547751309^1024*100000^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 10080338547751309 50000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (10080338547751309/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000912264044053313/10000000000000000000 : ℝ) ≤ (5000099991983957/5000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (10000912264044053313/10000000000000000000 : ℝ)^1024 ≤ (5000099991983957/5000000000000000 : ℝ)^4671 := by
      have hnat : (10000912264044053313 : ℕ)^1024*5000000000000000^4671 ≤ 5000099991983957^4671*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000912264044053313 10000000000000000000 5000099991983957 5000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000099991983957/5000000000000000 : ℝ)) (X := (10000912264044053313/10000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024721997315769183/100000000000000000000 : ℝ) ≤ (1000054191570087/1000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (100024721997315769183/100000000000000000000 : ℝ)^1024 ≤ (1000054191570087/1000000000000000 : ℝ)^4671 := by
      have hnat : (100024721997315769183 : ℕ)^1024*1000000000000000^4671 ≤ 1000054191570087^4671*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024721997315769183 100000000000000000000 1000054191570087 1000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000054191570087/1000000000000000 : ℝ)) (X := (100024721997315769183/100000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010080338547751309/25000000000000000000 : ℝ) ≤ (5000441923716913/5000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (25010080338547751309/25000000000000000000 : ℝ)^1024 ≤ (5000441923716913/5000000000000000 : ℝ)^4671 := by
      have hnat : (25010080338547751309 : ℕ)^1024*5000000000000000^4671 ≤ 5000441923716913^4671*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010080338547751309 25000000000000000000 5000441923716913 5000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000441923716913/5000000000000000 : ℝ)) (X := (25010080338547751309/25000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(912264044053313/20000000000000000000 : ℝ) ≤ ((7173869450859984239/7175000000000000000 : ℝ)+2*(85482933239/107625000000000 : ℝ)*(5589/50000 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (7173869450859984239/7175000000000000000 : ℝ)+2*(85482933239/107625000000000 : ℝ)*(5589/50000 : ℝ)=(5000099991983957/5000000000000000 : ℝ) by norm_num, show 1+2*(912264044053313/20000000000000000000 : ℝ)=(10000912264044053313/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10080338547751309/50000000000000000000 : ℝ)+(912264044053313/20000000000000000000 : ℝ) ≤ ((7173869450859984239/7175000000000000000 : ℝ)+(85482933239/107625000000000 : ℝ)*((15483/100000 : ℝ)+(5589/50000 : ℝ)))^(4671/1024 : ℝ) := by
    rw [show (7173869450859984239/7175000000000000000 : ℝ)+(85482933239/107625000000000 : ℝ)*((15483/100000 : ℝ)+(5589/50000 : ℝ))=(1000054191570087/1000000000000000 : ℝ) by norm_num, show 1+(10080338547751309/50000000000000000000 : ℝ)+(912264044053313/20000000000000000000 : ℝ)=(100024721997315769183/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10080338547751309/50000000000000000000 : ℝ) ≤ ((7173869450859984239/7175000000000000000 : ℝ)+2*(85482933239/107625000000000 : ℝ)*(15483/100000 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (7173869450859984239/7175000000000000000 : ℝ)+2*(85482933239/107625000000000 : ℝ)*(15483/100000 : ℝ)=(5000441923716913/5000000000000000 : ℝ) by norm_num, show 1+2*(10080338547751309/50000000000000000000 : ℝ)=(25010080338547751309/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7173869450859984239/7175000000000000000 : ℝ)*(X 1 0+X 2 0)+(85482933239/107625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (5589/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (7173869450859984239/7175000000000000000 : ℝ)) (alpha := (85482933239/107625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7173869450859984239/7175000000000000000 : ℝ)*(X 0 1+X 2 1)+(85482933239/107625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (5589/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (7173869450859984239/7175000000000000000 : ℝ)) (alpha := (85482933239/107625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7173869450859984239/7175000000000000000 : ℝ)*(X 0 2+X 1 2)+(85482933239/107625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (5589/50000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (7173869450859984239/7175000000000000000 : ℝ)) (alpha := (85482933239/107625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-780175519/5000000000 : ℝ)*X 0 0+(5394668159/10000000000 : ℝ)*X 0 1+(5394668381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1054223143/2000000000 : ℝ)*X 1 0+(-433049103/2500000000 : ℝ)*X 1 1+(5394668189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271115389/10000000000 : ℝ)*X 2 0+(5394668463/10000000000 : ℝ)*X 2 1+(-1732196481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4435690089/10000000000 : ℝ)*X 0 0+(1035540543/2500000000 : ℝ)*X 0 1+(828432407/2000000000 : ℝ)*X 0 2+(4435690089/10000000000 : ℝ)*X 1 0+(1035540543/2500000000 : ℝ)*X 1 1+(828432407/2000000000 : ℝ)*X 1 2+(4435690089/10000000000 : ℝ)*X 2 0+(1035540543/2500000000 : ℝ)*X 2 1+(828432407/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-393531141/2000000000 : ℝ)*X 0 0+(8392533/16000000 : ℝ)*X 0 1+(1049066647/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((537449451/1000000000 : ℝ)*X 1 0+(-1794824347/10000000000 : ℝ)*X 1 1+(2622666539/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074899013/2000000000 : ℝ)*X 2 0+(524533281/1000000000 : ℝ)*X 2 1+(-358964791/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((100820827/250000000 : ℝ)*X 0 0+(217173213/500000000 : ℝ)*X 0 1+(4343465871/10000000000 : ℝ)*X 0 2+(100820827/250000000 : ℝ)*X 1 0+(217173213/500000000 : ℝ)*X 1 1+(4343465871/10000000000 : ℝ)*X 1 2+(100820827/250000000 : ℝ)*X 2 0+(217173213/500000000 : ℝ)*X 2 1+(4343465871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-940624959/5000000000 : ℝ)*X 0 0+(5139938623/10000000000 : ℝ)*X 0 1+(54148789/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5257121833/10000000000 : ℝ)*X 1 0+(-861746387/5000000000 : ℝ)*X 1 1+(5414878871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5257121731/10000000000 : ℝ)*X 2 0+(5414878981/10000000000 : ℝ)*X 2 1+(-861746381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4489068999/10000000000 : ℝ)*X 0 0+(4114883911/10000000000 : ℝ)*X 0 1+(411488379/1000000000 : ℝ)*X 0 2+(4489068999/10000000000 : ℝ)*X 1 0+(4114883911/10000000000 : ℝ)*X 1 1+(411488379/1000000000 : ℝ)*X 1 2+(4489068999/10000000000 : ℝ)*X 2 0+(4114883911/10000000000 : ℝ)*X 2 1+(411488379/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1646338721/10000000000 : ℝ)*X 0 0+(5496901027/10000000000 : ℝ)*X 0 1+(653785587/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2692456367/5000000000 : ℝ)*X 1 0+(-1800967817/10000000000 : ℝ)*X 1 1+(653785691/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1346228451/2500000000 : ℝ)*X 2 0+(5230284281/10000000000 : ℝ)*X 2 1+(-450242011/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1995687001/5000000000 : ℝ)*X 0 0+(872745057/2000000000 : ℝ)*X 0 1+(436372433/1000000000 : ℝ)*X 0 2+(1995687001/5000000000 : ℝ)*X 1 0+(872745057/2000000000 : ℝ)*X 1 1+(436372433/1000000000 : ℝ)*X 1 2+(1995687001/5000000000 : ℝ)*X 2 0+(872745057/2000000000 : ℝ)*X 2 1+(436372433/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63861/100000 : ℝ) ≤ (-57273529210372987580812404395313/89687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1853237/2500000000000 : ℝ)*(upper0) + (49951301/50000000000000 : ℝ)*(lower1) + (117170053/100000000000000 : ℝ)*(lower2) + (151890523/100000000000000 : ℝ)*(lower3) + (13208291/20000000000000 : ℝ)*(upper5) + (583362813411863/25000000000000 : ℝ)*(major0) + (583362813411863/25000000000000 : ℝ)*(major1) + (583362813411863/25000000000000 : ℝ)*(major2) + (402695821/6250000000000 : ℝ)*(sp2) + (1655666260271907/50000000000000 : ℝ)*(sp4) + (1655666260271907/50000000000000 : ℝ)*(sp5) + (1655663038705339/50000000000000 : ℝ)*(sp6) + (688421448644233/50000000000000 : ℝ)*(sp7) + (6709276789/50000000000000 : ℝ)*(sp15) + (344214078960511/25000000000000 : ℝ)*(f.failure) + (1655666260271907/50000000000000 : ℝ)*(f.sum) + (38530632615019/10762500000000000000000000000 : ℝ)*base66 + (775876827009040253/76875000000000000000000000000000 : ℝ)*base67 + (1279902285166540253/76875000000000000000000000000000 : ℝ)*base69 + (1007907721929040253/76875000000000000000000000000000 : ℝ)*base71 + (25880346636961/2690625000000000000000000000 : ℝ)*base74 + (951290780262790253/76875000000000000000000000000000 : ℝ)*base75 + (786717372815290253/76875000000000000000000000000000 : ℝ)*base77 + (755951103912790253/76875000000000000000000000000000 : ℝ)*base79 + (4625611057493/1345312500000000000000000000 : ℝ)*base82 + (1107023/312500000000000000000 : ℝ)*base89 + (1107023/312500000000000000000 : ℝ)*base91 + (1107023/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58989/100000 : ℝ) ≤ (21163044663190725312182373238327/35875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12412179/25000000000000 : ℝ)*(lower0) + (10047433/100000000000000 : ℝ)*(upper1) + (82836091/100000000000000 : ℝ)*(upper2) + (241492847182669/10000000000000 : ℝ)*(major0) + (241492847182669/10000000000000 : ℝ)*(major1) + (241492847182669/10000000000000 : ℝ)*(major2) + (105789331885893/3125000000000 : ℝ)*(sp0) + (1692627441622729/50000000000000 : ℝ)*(sp1) + (211578711189177/6250000000000 : ℝ)*(sp2) + (712465201081967/50000000000000 : ℝ)*(sp3) + (361786431/20000000000000 : ℝ)*(sp6) + (788089191/12500000000000 : ℝ)*(sp9) + (1665109373/100000000000000 : ℝ)*(sp11) + (256761041/10000000000000 : ℝ)*(sp12) + (1424932067273307/100000000000000 : ℝ)*(f.failure) + (1692630593979493/50000000000000 : ℝ)*(f.sum) + (7372833731353/4305000000000000000000000000 : ℝ)*base65 + (59780105829830239/30750000000000000000000000000000 : ℝ)*base67 + (63273764896580239/30750000000000000000000000000000 : ℝ)*base69 + (254620656113330239/30750000000000000000000000000000 : ℝ)*base71 + (12138516826813/4305000000000000000000000000 : ℝ)*base73 + (27978140348919761/30750000000000000000000000000000 : ℝ)*base76 + (93459800671580239/30750000000000000000000000000000 : ℝ)*base77 + (118988774114169761/30750000000000000000000000000000 : ℝ)*base80 + (4984616626487/4305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3559051/1250000000000000000000 : ℝ)*base89 + (3559051/1250000000000000000000 : ℝ)*base91 + (3559051/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40549/50000 : ℝ) ≤ (145473722701448672032880248574717/179375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139333/1000000000000 : ℝ)*(upper1) + (4323763/50000000000000 : ℝ)*(upper2) + (2240477/50000000000000 : ℝ)*(upper3) + (3367951/25000000000000 : ℝ)*(lower5) + (1299404661086333/50000000000000 : ℝ)*(major0) + (1299404661086333/50000000000000 : ℝ)*(major1) + (1299404661086333/50000000000000 : ℝ)*(major2) + (270997491/50000000000000 : ℝ)*(sp0) + (20331670797/100000000000000 : ℝ)*(sp2) + (1172687007/20000000000000 : ℝ)*(sp3) + (363715342671297/10000000000000 : ℝ)*(sp8) + (227322123044247/6250000000000 : ℝ)*(sp9) + (727426727407431/20000000000000 : ℝ)*(sp10) + (766712683898943/50000000000000 : ℝ)*(sp11) + (1533431231232921/100000000000000 : ℝ)*(f.failure) + (227322123044247/6250000000000 : ℝ)*(f.sum) + (66901326070129/21525000000000000000000000000 : ℝ)*base66 + (1261402327884973823/153750000000000000000000000000000 : ℝ)*base67 + (1446634993836223823/153750000000000000000000000000000 : ℝ)*base69 + (1121460057118723823/153750000000000000000000000000000 : ℝ)*base71 + (46614880005373/10762500000000000000000000000 : ℝ)*base73 + (2247813167398723823/153750000000000000000000000000000 : ℝ)*base75 + (676569930111223823/153750000000000000000000000000000 : ℝ)*base77 + (1841301876617473823/153750000000000000000000000000000 : ℝ)*base79 + (11639921296877/10762500000000000000000000000 : ℝ)*base82 + (5413847/1250000000000000000000 : ℝ)*base90 + (5413847/1250000000000000000000 : ℝ)*base92 + (5413847/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21619/25000 : ℝ) ≤ (-155111959819885019256919102567333/179375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183384673/100000000000000 : ℝ)*(lower2) + (301516567/100000000000000 : ℝ)*(upper3) + (196159833/100000000000000 : ℝ)*(upper5) + (2639732232412649/100000000000000 : ℝ)*(major0) + (2639732232412649/100000000000000 : ℝ)*(major1) + (2639732232412649/100000000000000 : ℝ)*(major2) + (4527741977/100000000000000 : ℝ)*(sp4) + (209182145951/100000000000000 : ℝ)*(sp6) + (37884883167/100000000000000 : ℝ)*(sp7) + (202011183/100000000000000 : ℝ)*(sp8) + (3750706403111019/100000000000000 : ℝ)*(sp12) + (3750711132864179/100000000000000 : ℝ)*(sp13) + (937625487679557/25000000000000 : ℝ)*(sp14) + (97346248076749/6250000000000 : ℝ)*(sp15) + (1557577854111151/100000000000000 : ℝ)*(f.failure) + (3750711132864179/100000000000000 : ℝ)*(f.sum) + (5502549044597/10762500000000000000000000000 : ℝ)*base65 + (1630255079148940381/307500000000000000000000000000000 : ℝ)*base68 + (2214066505233559619/307500000000000000000000000000000 : ℝ)*base69 + (712839814698559619/307500000000000000000000000000000 : ℝ)*base71 + (74781751195481/21525000000000000000000000000 : ℝ)*base74 + (3045794967386059619/307500000000000000000000000000000 : ℝ)*base75 + (700141374341059619/307500000000000000000000000000000 : ℝ)*base77 + (2665304446068559619/307500000000000000000000000000000 : ℝ)*base79 + (489703337257/2690625000000000000000000000 : ℝ)*base82 + (1803457/1250000000000000000000 : ℝ)*base90 + (1803457/1250000000000000000000 : ℝ)*base92 + (1803457/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1588_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58989/100000 : ℝ) else (40549/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21619/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1588_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1588_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58989/100000 : ℝ) else (40549/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21619/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1588_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58989/100000 : ℝ) else (40549/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21619/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1588_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

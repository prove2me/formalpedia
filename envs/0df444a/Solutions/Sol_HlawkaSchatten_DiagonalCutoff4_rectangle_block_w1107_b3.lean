-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1107_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:01.72911+00:00
-- url     : https://prove2.me/submissions/665841c5-d3ea-4d0d-a172-e8eb5989c4f5

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
theorem support_rectangle_w1107_s9_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183741571/10000000000 : ℝ)*x 0 + (1348402319/2500000000 : ℝ)*x 1 + (5265204757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183741571/10000000000 : ℝ)^2075 ≤ (1326599936399/10000000000000 : ℝ)^1563 := by
    have hnat : (2183741571 : ℕ)^2075*10000000000000^1563 ≤ 1326599936399^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183741571 10000000000 1326599936399 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348402319/2500000000 : ℝ)^2075 ≤ (44060544134263/100000000000000 : ℝ)^1563 := by
    have hnat : (1348402319 : ℕ)^2075*100000000000000^1563 ≤ 44060544134263^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348402319 2500000000 44060544134263 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265204757/10000000000 : ℝ)^2075 ≤ (21336728239641/50000000000000 : ℝ)^1563 := by
    have hnat : (5265204757 : ℕ)^2075*50000000000000^1563 ≤ 21336728239641^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265204757 10000000000 21336728239641 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183741571/10000000000 : ℝ), (1348402319/2500000000 : ℝ), (5265204757/10000000000 : ℝ)] ![(1326599936399/10000000000000 : ℝ), (44060544134263/100000000000000 : ℝ), (21336728239641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183741571/10000000000 : ℝ)|^2075 ≤ (1326599936399/10000000000000 : ℝ)^1563
        have hw : |(-2183741571/10000000000 : ℝ)|=(2183741571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348402319/2500000000 : ℝ)|^2075 ≤ (44060544134263/100000000000000 : ℝ)^1563
        have hw : |(1348402319/2500000000 : ℝ)|=(1348402319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265204757/10000000000 : ℝ)|^2075 ≤ (21336728239641/50000000000000 : ℝ)^1563
        have hw : |(5265204757/10000000000 : ℝ)|=(5265204757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s9_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336215661/2500000000 : ℝ)*x 0 + (-1799103/8000000 : ℝ)*x 1 + (5265204759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336215661/2500000000 : ℝ)^2075 ≤ (8706534227639/20000000000000 : ℝ)^1563 := by
    have hnat : (1336215661 : ℕ)^2075*20000000000000^1563 ≤ 8706534227639^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336215661 2500000000 8706534227639 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1799103/8000000 : ℝ)^2075 ≤ (6896936172931/50000000000000 : ℝ)^1563 := by
    have hnat : (1799103 : ℕ)^2075*50000000000000^1563 ≤ 6896936172931^1563*8000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799103 8000000 6896936172931 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265204759/10000000000 : ℝ)^2075 ≤ (21336728250401/50000000000000 : ℝ)^1563 := by
    have hnat : (5265204759 : ℕ)^2075*50000000000000^1563 ≤ 21336728250401^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265204759 10000000000 21336728250401 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336215661/2500000000 : ℝ), (-1799103/8000000 : ℝ), (5265204759/10000000000 : ℝ)] ![(8706534227639/20000000000000 : ℝ), (6896936172931/50000000000000 : ℝ), (21336728250401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336215661/2500000000 : ℝ)|^2075 ≤ (8706534227639/20000000000000 : ℝ)^1563
        have hw : |(1336215661/2500000000 : ℝ)|=(1336215661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1799103/8000000 : ℝ)|^2075 ≤ (6896936172931/50000000000000 : ℝ)^1563
        have hw : |(-1799103/8000000 : ℝ)|=(1799103/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265204759/10000000000 : ℝ)|^2075 ≤ (21336728250401/50000000000000 : ℝ)^1563
        have hw : |(5265204759/10000000000 : ℝ)|=(5265204759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s9_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068972519/2000000000 : ℝ)*x 0 + (3290753/6250000 : ℝ)*x 1 + (-1124439381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068972519/2000000000 : ℝ)^2075 ≤ (2720791913023/6250000000000 : ℝ)^1563 := by
    have hnat : (1068972519 : ℕ)^2075*6250000000000^1563 ≤ 2720791913023^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068972519 2000000000 2720791913023 6250000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3290753/6250000 : ℝ)^2075 ≤ (42673456941951/100000000000000 : ℝ)^1563 := by
    have hnat : (3290753 : ℕ)^2075*100000000000000^1563 ≤ 42673456941951^1563*6250000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3290753 6250000 42673456941951 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124439381/5000000000 : ℝ)^2075 ≤ (13793872443577/100000000000000 : ℝ)^1563 := by
    have hnat : (1124439381 : ℕ)^2075*100000000000000^1563 ≤ 13793872443577^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124439381 5000000000 13793872443577 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068972519/2000000000 : ℝ), (3290753/6250000 : ℝ), (-1124439381/5000000000 : ℝ)] ![(2720791913023/6250000000000 : ℝ), (42673456941951/100000000000000 : ℝ), (13793872443577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068972519/2000000000 : ℝ)|^2075 ≤ (2720791913023/6250000000000 : ℝ)^1563
        have hw : |(1068972519/2000000000 : ℝ)|=(1068972519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3290753/6250000 : ℝ)|^2075 ≤ (42673456941951/100000000000000 : ℝ)^1563
        have hw : |(3290753/6250000 : ℝ)|=(3290753/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1124439381/5000000000 : ℝ)|^2075 ≤ (13793872443577/100000000000000 : ℝ)^1563
        have hw : |(-1124439381/5000000000 : ℝ)|=(1124439381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s9_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4369629823/10000000000 : ℝ)*x 0 + (265289051/625000000 : ℝ)*x 1 + (4498329563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369629823/10000000000 : ℝ)^2075 ≤ (16658398352921/50000000000000 : ℝ)^1563 := by
    have hnat : (4369629823 : ℕ)^2075*50000000000000^1563 ≤ 16658398352921^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369629823 10000000000 16658398352921 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265289051/625000000 : ℝ)^2075 ≤ (16028715085143/50000000000000 : ℝ)^1563 := by
    have hnat : (265289051 : ℕ)^2075*50000000000000^1563 ≤ 16028715085143^1563*625000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265289051 625000000 16028715085143 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498329563/10000000000 : ℝ)^2075 ≤ (34625773111177/100000000000000 : ℝ)^1563 := by
    have hnat : (4498329563 : ℕ)^2075*100000000000000^1563 ≤ 34625773111177^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498329563 10000000000 34625773111177 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369629823/10000000000 : ℝ), (265289051/625000000 : ℝ), (4498329563/10000000000 : ℝ)] ![(16658398352921/50000000000000 : ℝ), (16028715085143/50000000000000 : ℝ), (34625773111177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369629823/10000000000 : ℝ)|^2075 ≤ (16658398352921/50000000000000 : ℝ)^1563
        have hw : |(4369629823/10000000000 : ℝ)|=(4369629823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265289051/625000000 : ℝ)|^2075 ≤ (16028715085143/50000000000000 : ℝ)^1563
        have hw : |(265289051/625000000 : ℝ)|=(265289051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498329563/10000000000 : ℝ)|^2075 ≤ (34625773111177/100000000000000 : ℝ)^1563
        have hw : |(4498329563/10000000000 : ℝ)|=(4498329563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s9_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091873359/5000000000 : ℝ)*x 0 + (5265527197/10000000000 : ℝ)*x 1 + (2696642769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091873359/5000000000 : ℝ)^2075 ≤ (6633020436969/50000000000000 : ℝ)^1563 := by
    have hnat : (1091873359 : ℕ)^2075*50000000000000^1563 ≤ 6633020436969^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091873359 5000000000 6633020436969 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265527197/10000000000 : ℝ)^2075 ≤ (21338462941933/50000000000000 : ℝ)^1563 := by
    have hnat : (5265527197 : ℕ)^2075*50000000000000^1563 ≤ 21338462941933^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265527197 10000000000 21338462941933 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696642769/5000000000 : ℝ)^2075 ≤ (5507129153831/12500000000000 : ℝ)^1563 := by
    have hnat : (2696642769 : ℕ)^2075*12500000000000^1563 ≤ 5507129153831^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696642769 5000000000 5507129153831 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091873359/5000000000 : ℝ), (5265527197/10000000000 : ℝ), (2696642769/5000000000 : ℝ)] ![(6633020436969/50000000000000 : ℝ), (21338462941933/50000000000000 : ℝ), (5507129153831/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091873359/5000000000 : ℝ)|^2075 ≤ (6633020436969/50000000000000 : ℝ)^1563
        have hw : |(-1091873359/5000000000 : ℝ)|=(1091873359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265527197/10000000000 : ℝ)|^2075 ≤ (21338462941933/50000000000000 : ℝ)^1563
        have hw : |(5265527197/10000000000 : ℝ)|=(5265527197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696642769/5000000000 : ℝ)|^2075 ≤ (5507129153831/12500000000000 : ℝ)^1563
        have hw : |(2696642769/5000000000 : ℝ)|=(2696642769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s9_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4369639219/10000000000 : ℝ)*x 0 + (4497693627/10000000000 : ℝ)*x 1 + (849052689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369639219/10000000000 : ℝ)^2075 ≤ (832922295367/2500000000000 : ℝ)^1563 := by
    have hnat : (4369639219 : ℕ)^2075*2500000000000^1563 ≤ 832922295367^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369639219 10000000000 832922295367 2500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497693627/10000000000 : ℝ)^2075 ≤ (8654818661911/25000000000000 : ℝ)^1563 := by
    have hnat : (4497693627 : ℕ)^2075*25000000000000^1563 ≤ 8654818661911^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497693627 10000000000 8654818661911 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849052689/2000000000 : ℝ)^2075 ≤ (8015958382343/25000000000000 : ℝ)^1563 := by
    have hnat : (849052689 : ℕ)^2075*25000000000000^1563 ≤ 8015958382343^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849052689 2000000000 8015958382343 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369639219/10000000000 : ℝ), (4497693627/10000000000 : ℝ), (849052689/2000000000 : ℝ)] ![(832922295367/2500000000000 : ℝ), (8654818661911/25000000000000 : ℝ), (8015958382343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369639219/10000000000 : ℝ)|^2075 ≤ (832922295367/2500000000000 : ℝ)^1563
        have hw : |(4369639219/10000000000 : ℝ)|=(4369639219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497693627/10000000000 : ℝ)|^2075 ≤ (8654818661911/25000000000000 : ℝ)^1563
        have hw : |(4497693627/10000000000 : ℝ)|=(4497693627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849052689/2000000000 : ℝ)|^2075 ≤ (8015958382343/25000000000000 : ℝ)^1563
        have hw : |(849052689/2000000000 : ℝ)|=(849052689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2827/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3507/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11307/100000 : ℝ) ^ (8299/2048 : ℝ) ≤ (14585813888874349/100000000000000000000 : ℝ) := by
    have hpowers : (11307/100000 : ℝ)^8299 ≤ (14585813888874349/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11307 : ℕ)^8299*100000000000000000000^2048 ≤ 14585813888874349^2048*100000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11307 100000 14585813888874349 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11307/100000 : ℝ)) (X := (14585813888874349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3507/25000 : ℝ) ^ (8299/2048 : ℝ) ≤ (34947562415722301/100000000000000000000 : ℝ) := by
    have hpowers : (3507/25000 : ℝ)^8299 ≤ (34947562415722301/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3507 : ℕ)^8299*100000000000000000000^2048 ≤ 34947562415722301^2048*25000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3507 25000 34947562415722301 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3507/25000 : ℝ)) (X := (34947562415722301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014585813888874349/50000000000000000000 : ℝ) ≤ (5000359904393081/5000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50014585813888874349/50000000000000000000 : ℝ)^2048 ≤ (5000359904393081/5000000000000000 : ℝ)^8299 := by
      have hnat : (50014585813888874349 : ℕ)^2048*5000000000000000^8299 ≤ 5000359904393081^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014585813888874349 50000000000000000000 5000359904393081 5000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000359904393081/5000000000000000 : ℝ)) (X := (50014585813888874349/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000990667526091933/2000000000000000000 : ℝ) ≤ (10001222140448969/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (2000990667526091933/2000000000000000000 : ℝ)^2048 ≤ (10001222140448969/10000000000000000 : ℝ)^8299 := by
      have hnat : (2000990667526091933 : ℕ)^2048*10000000000000000^8299 ≤ 10001222140448969^8299*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000990667526091933 2000000000000000000 10001222140448969 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001222140448969/10000000000000000 : ℝ)) (X := (2000990667526091933/2000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034947562415722301/50000000000000000000 : ℝ) ≤ (312553889753493/312500000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50034947562415722301/50000000000000000000 : ℝ)^2048 ≤ (312553889753493/312500000000000 : ℝ)^8299 := by
      have hnat : (50034947562415722301 : ℕ)^2048*312500000000000^8299 ≤ 312553889753493^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034947562415722301 50000000000000000000 312553889753493 312500000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312553889753493/312500000000000 : ℝ)) (X := (50034947562415722301/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14585813888874349/100000000000000000000 : ℝ) ≤ ((1133358286311851221/1133750000000000000 : ℝ)+2*(502331662807/272100000000000 : ℝ)*(11307/100000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (1133358286311851221/1133750000000000000 : ℝ)+2*(502331662807/272100000000000 : ℝ)*(11307/100000 : ℝ)=(5000359904393081/5000000000000000 : ℝ) by norm_num, show 1+2*(14585813888874349/100000000000000000000 : ℝ)=(50014585813888874349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34947562415722301/100000000000000000000 : ℝ)+(14585813888874349/100000000000000000000 : ℝ) ≤ ((1133358286311851221/1133750000000000000 : ℝ)+(502331662807/272100000000000 : ℝ)*((3507/25000 : ℝ)+(11307/100000 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (1133358286311851221/1133750000000000000 : ℝ)+(502331662807/272100000000000 : ℝ)*((3507/25000 : ℝ)+(11307/100000 : ℝ))=(10001222140448969/10000000000000000 : ℝ) by norm_num, show 1+(34947562415722301/100000000000000000000 : ℝ)+(14585813888874349/100000000000000000000 : ℝ)=(2000990667526091933/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34947562415722301/100000000000000000000 : ℝ) ≤ ((1133358286311851221/1133750000000000000 : ℝ)+2*(502331662807/272100000000000 : ℝ)*(3507/25000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (1133358286311851221/1133750000000000000 : ℝ)+2*(502331662807/272100000000000 : ℝ)*(3507/25000 : ℝ)=(312553889753493/312500000000000 : ℝ) by norm_num, show 1+2*(34947562415722301/100000000000000000000 : ℝ)=(50034947562415722301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1133358286311851221/1133750000000000000 : ℝ)*(X 1 0+X 2 0)+(502331662807/272100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (1133358286311851221/1133750000000000000 : ℝ)) (alpha := (502331662807/272100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1133358286311851221/1133750000000000000 : ℝ)*(X 0 1+X 2 1)+(502331662807/272100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (1133358286311851221/1133750000000000000 : ℝ)) (alpha := (502331662807/272100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1133358286311851221/1133750000000000000 : ℝ)*(X 0 2+X 1 2)+(502331662807/272100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (1133358286311851221/1133750000000000000 : ℝ)) (alpha := (502331662807/272100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2183741571/10000000000 : ℝ)*X 0 0+(1348402319/2500000000 : ℝ)*X 0 1+(5265204757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336215661/2500000000 : ℝ)*X 1 0+(-1799103/8000000 : ℝ)*X 1 1+(5265204759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068972519/2000000000 : ℝ)*X 2 0+(3290753/6250000 : ℝ)*X 2 1+(-1124439381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369629823/10000000000 : ℝ)*X 0 0+(265289051/625000000 : ℝ)*X 0 1+(4498329563/10000000000 : ℝ)*X 0 2+(4369629823/10000000000 : ℝ)*X 1 0+(265289051/625000000 : ℝ)*X 1 1+(4498329563/10000000000 : ℝ)*X 1 2+(4369629823/10000000000 : ℝ)*X 2 0+(265289051/625000000 : ℝ)*X 2 1+(4498329563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1091873359/5000000000 : ℝ)*X 0 0+(5265527197/10000000000 : ℝ)*X 0 1+(2696642769/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4369639219/10000000000 : ℝ)*X 0 0+(4497693627/10000000000 : ℝ)*X 0 1+(849052689/2000000000 : ℝ)*X 0 2+(4369639219/10000000000 : ℝ)*X 1 0+(4497693627/10000000000 : ℝ)*X 1 1+(849052689/2000000000 : ℝ)*X 1 2+(4369639219/10000000000 : ℝ)*X 2 0+(4497693627/10000000000 : ℝ)*X 2 1+(849052689/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52687552891225435585698497/14171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38536433/4000000000000 : ℝ)*(base19) + (86481343/10000000000000 : ℝ)*(base23) + (14538033/100000000000000 : ℝ)*(lower2) + (59015653/50000000000000 : ℝ)*(upper3) + (16530241/25000000000000 : ℝ)*(upper5) + (1466194878670931/25000000000000 : ℝ)*(major0) + (1466194878670931/25000000000000 : ℝ)*(major1) + (1466194878670931/25000000000000 : ℝ)*(major2) + (1557583436506641/20000000000000 : ℝ)*(sp0) + (1946985685002137/25000000000000 : ℝ)*(sp1) + (7787942838605943/100000000000000 : ℝ)*(sp2) + (492700247651277/12500000000000 : ℝ)*(sp3) + (3315110771/12500000000000 : ℝ)*(sp4) + (13220812701/100000000000000 : ℝ)*(sp5) + (3941615202022917/100000000000000 : ℝ)*(f.failure) + (7787943703419373/100000000000000 : ℝ)*(f.sum) + (4310904657857/3401250000000000000000000000 : ℝ)*base65 + (753259936950460997/85031250000000000000000000000000 : ℝ)*base68 + (825665985830070253/85031250000000000000000000000000 : ℝ)*base69 + (777933857157664003/85031250000000000000000000000000 : ℝ)*base71 + (3117667195553/13605000000000000000000000000 : ℝ)*base73 + (525064755432476503/85031250000000000000000000000000 : ℝ)*base75 + (417442072416007753/85031250000000000000000000000000 : ℝ)*base77 + (1652976079919335997/85031250000000000000000000000000 : ℝ)*base80 + (5585257690133/13605000000000000000000000000 : ℝ)*base81 + (14033/400000000000000000000 : ℝ)*base90 + (14033/400000000000000000000 : ℝ)*base92 + (14033/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1107_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1107_box_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-205567393/1000000000 : ℝ)*x 0 + (5376805309/10000000000 : ℝ)*x 1 + (336050329/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205567393/1000000000 : ℝ)^2075 ≤ (765200254809/6250000000000 : ℝ)^1563 := by
    have hnat : (205567393 : ℕ)^2075*6250000000000^1563 ≤ 765200254809^1563*1000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205567393 1000000000 765200254809 6250000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376805309/10000000000 : ℝ)^2075 ≤ (43878398195933/100000000000000 : ℝ)^1563 := by
    have hnat : (5376805309 : ℕ)^2075*100000000000000^1563 ≤ 43878398195933^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376805309 10000000000 43878398195933 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336050329/625000000 : ℝ)^2075 ≤ (21939198854203/50000000000000 : ℝ)^1563 := by
    have hnat : (336050329 : ℕ)^2075*50000000000000^1563 ≤ 21939198854203^1563*625000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336050329 625000000 21939198854203 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205567393/1000000000 : ℝ), (5376805309/10000000000 : ℝ), (336050329/625000000 : ℝ)] ![(765200254809/6250000000000 : ℝ), (43878398195933/100000000000000 : ℝ), (21939198854203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205567393/1000000000 : ℝ)|^2075 ≤ (765200254809/6250000000000 : ℝ)^1563
        have hw : |(-205567393/1000000000 : ℝ)|=(205567393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376805309/10000000000 : ℝ)|^2075 ≤ (43878398195933/100000000000000 : ℝ)^1563
        have hw : |(5376805309/10000000000 : ℝ)|=(5376805309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336050329/625000000 : ℝ)|^2075 ≤ (21939198854203/50000000000000 : ℝ)^1563
        have hw : |(336050329/625000000 : ℝ)|=(336050329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2647821789/5000000000 : ℝ)*x 0 + (-1082826877/5000000000 : ℝ)*x 1 + (672100667/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647821789/5000000000 : ℝ)^2075 ≤ (43001279919831/100000000000000 : ℝ)^1563 := by
    have hnat : (2647821789 : ℕ)^2075*100000000000000^1563 ≤ 43001279919831^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647821789 5000000000 43001279919831 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082826877/5000000000 : ℝ)^2075 ≤ (13120321579889/100000000000000 : ℝ)^1563 := by
    have hnat : (1082826877 : ℕ)^2075*100000000000000^1563 ≤ 13120321579889^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082826877 5000000000 13120321579889 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672100667/1250000000 : ℝ)^2075 ≤ (43878398488449/100000000000000 : ℝ)^1563 := by
    have hnat : (672100667 : ℕ)^2075*100000000000000^1563 ≤ 43878398488449^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672100667 1250000000 43878398488449 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647821789/5000000000 : ℝ), (-1082826877/5000000000 : ℝ), (672100667/1250000000 : ℝ)] ![(43001279919831/100000000000000 : ℝ), (13120321579889/100000000000000 : ℝ), (43878398488449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647821789/5000000000 : ℝ)|^2075 ≤ (43001279919831/100000000000000 : ℝ)^1563
        have hw : |(2647821789/5000000000 : ℝ)|=(2647821789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1082826877/5000000000 : ℝ)|^2075 ≤ (13120321579889/100000000000000 : ℝ)^1563
        have hw : |(-1082826877/5000000000 : ℝ)|=(1082826877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672100667/1250000000 : ℝ)|^2075 ≤ (43878398488449/100000000000000 : ℝ)^1563
        have hw : |(672100667/1250000000 : ℝ)|=(672100667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2647821747/5000000000 : ℝ)*x 0 + (5376805183/10000000000 : ℝ)*x 1 + (-2165654073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647821747/5000000000 : ℝ)^2075 ≤ (8600255802861/20000000000000 : ℝ)^1563 := by
    have hnat : (2647821747 : ℕ)^2075*20000000000000^1563 ≤ 8600255802861^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647821747 5000000000 8600255802861 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376805183/10000000000 : ℝ)^2075 ≤ (43878396830859/100000000000000 : ℝ)^1563 := by
    have hnat : (5376805183 : ℕ)^2075*100000000000000^1563 ≤ 43878396830859^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376805183 10000000000 43878396830859 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165654073/10000000000 : ℝ)^2075 ≤ (2624064829117/20000000000000 : ℝ)^1563 := by
    have hnat : (2165654073 : ℕ)^2075*20000000000000^1563 ≤ 2624064829117^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165654073 10000000000 2624064829117 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647821747/5000000000 : ℝ), (5376805183/10000000000 : ℝ), (-2165654073/10000000000 : ℝ)] ![(8600255802861/20000000000000 : ℝ), (43878396830859/100000000000000 : ℝ), (2624064829117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647821747/5000000000 : ℝ)|^2075 ≤ (8600255802861/20000000000000 : ℝ)^1563
        have hw : |(2647821747/5000000000 : ℝ)|=(2647821747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376805183/10000000000 : ℝ)|^2075 ≤ (43878396830859/100000000000000 : ℝ)^1563
        have hw : |(5376805183/10000000000 : ℝ)|=(5376805183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2165654073/10000000000 : ℝ)|^2075 ≤ (2624064829117/20000000000000 : ℝ)^1563
        have hw : |(-2165654073/10000000000 : ℝ)|=(2165654073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2238778427/5000000000 : ℝ)*x 0 + (4317798429/10000000000 : ℝ)*x 1 + (539724887/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238778427/5000000000 : ℝ)^2075 ≤ (34413658040921/100000000000000 : ℝ)^1563 := by
    have hnat : (2238778427 : ℕ)^2075*100000000000000^1563 ≤ 34413658040921^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238778427 5000000000 34413658040921 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4317798429/10000000000 : ℝ)^2075 ≤ (32793167604277/100000000000000 : ℝ)^1563 := by
    have hnat : (4317798429 : ℕ)^2075*100000000000000^1563 ≤ 32793167604277^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317798429 10000000000 32793167604277 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539724887/1250000000 : ℝ)^2075 ≤ (32793174329489/100000000000000 : ℝ)^1563 := by
    have hnat : (539724887 : ℕ)^2075*100000000000000^1563 ≤ 32793174329489^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539724887 1250000000 32793174329489 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238778427/5000000000 : ℝ), (4317798429/10000000000 : ℝ), (539724887/1250000000 : ℝ)] ![(34413658040921/100000000000000 : ℝ), (32793167604277/100000000000000 : ℝ), (32793174329489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238778427/5000000000 : ℝ)|^2075 ≤ (34413658040921/100000000000000 : ℝ)^1563
        have hw : |(2238778427/5000000000 : ℝ)|=(2238778427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4317798429/10000000000 : ℝ)|^2075 ≤ (32793167604277/100000000000000 : ℝ)^1563
        have hw : |(4317798429/10000000000 : ℝ)|=(4317798429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539724887/1250000000 : ℝ)|^2075 ≤ (32793174329489/100000000000000 : ℝ)^1563
        have hw : |(539724887/1250000000 : ℝ)|=(539724887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2313187599/10000000000 : ℝ)*x 0 + (52806773/100000000 : ℝ)*x 1 + (5280676897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2313187599/10000000000 : ℝ)^2075 ≤ (2863994041799/20000000000000 : ℝ)^1563 := by
    have hnat : (2313187599 : ℕ)^2075*20000000000000^1563 ≤ 2863994041799^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2313187599 10000000000 2863994041799 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52806773/100000000 : ℝ)^2075 ≤ (5355002132269/12500000000000 : ℝ)^1563 := by
    have hnat : (52806773 : ℕ)^2075*12500000000000^1563 ≤ 5355002132269^1563*100000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52806773 100000000 5355002132269 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280676897/10000000000 : ℝ)^2075 ≤ (42840012717807/100000000000000 : ℝ)^1563 := by
    have hnat : (5280676897 : ℕ)^2075*100000000000000^1563 ≤ 42840012717807^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280676897 10000000000 42840012717807 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2313187599/10000000000 : ℝ), (52806773/100000000 : ℝ), (5280676897/10000000000 : ℝ)] ![(2863994041799/20000000000000 : ℝ), (5355002132269/12500000000000 : ℝ), (42840012717807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2313187599/10000000000 : ℝ)|^2075 ≤ (2863994041799/20000000000000 : ℝ)^1563
        have hw : |(-2313187599/10000000000 : ℝ)|=(2313187599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52806773/100000000 : ℝ)|^2075 ≤ (5355002132269/12500000000000 : ℝ)^1563
        have hw : |(52806773/100000000 : ℝ)|=(52806773/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280676897/10000000000 : ℝ)|^2075 ≤ (42840012717807/100000000000000 : ℝ)^1563
        have hw : |(5280676897/10000000000 : ℝ)|=(5280676897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5363611539/10000000000 : ℝ)*x 0 + (-13771011/62500000 : ℝ)*x 1 + (5280677419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363611539/10000000000 : ℝ)^2075 ≤ (43735515443193/100000000000000 : ℝ)^1563 := by
    have hnat : (5363611539 : ℕ)^2075*100000000000000^1563 ≤ 43735515443193^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363611539 10000000000 43735515443193 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13771011/62500000 : ℝ)^2075 ≤ (6712233100161/50000000000000 : ℝ)^1563 := by
    have hnat : (13771011 : ℕ)^2075*50000000000000^1563 ≤ 6712233100161^1563*62500000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13771011 62500000 6712233100161 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280677419/10000000000 : ℝ)^2075 ≤ (2677501146237/6250000000000 : ℝ)^1563 := by
    have hnat : (5280677419 : ℕ)^2075*6250000000000^1563 ≤ 2677501146237^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280677419 10000000000 2677501146237 6250000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363611539/10000000000 : ℝ), (-13771011/62500000 : ℝ), (5280677419/10000000000 : ℝ)] ![(43735515443193/100000000000000 : ℝ), (6712233100161/50000000000000 : ℝ), (2677501146237/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363611539/10000000000 : ℝ)|^2075 ≤ (43735515443193/100000000000000 : ℝ)^1563
        have hw : |(5363611539/10000000000 : ℝ)|=(5363611539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13771011/62500000 : ℝ)|^2075 ≤ (6712233100161/50000000000000 : ℝ)^1563
        have hw : |(-13771011/62500000 : ℝ)|=(13771011/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280677419/10000000000 : ℝ)|^2075 ≤ (2677501146237/6250000000000 : ℝ)^1563
        have hw : |(5280677419/10000000000 : ℝ)|=(5280677419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5363611903/10000000000 : ℝ)*x 0 + (5280676683/10000000000 : ℝ)*x 1 + (-1101681127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363611903/10000000000 : ℝ)^2075 ≤ (43735519383567/100000000000000 : ℝ)^1563 := by
    have hnat : (5363611903 : ℕ)^2075*100000000000000^1563 ≤ 43735519383567^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363611903 10000000000 43735519383567 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280676683/10000000000 : ℝ)^2075 ≤ (42840010413009/100000000000000 : ℝ)^1563 := by
    have hnat : (5280676683 : ℕ)^2075*100000000000000^1563 ≤ 42840010413009^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280676683 10000000000 42840010413009 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101681127/5000000000 : ℝ)^2075 ≤ (13424470196063/100000000000000 : ℝ)^1563 := by
    have hnat : (1101681127 : ℕ)^2075*100000000000000^1563 ≤ 13424470196063^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101681127 5000000000 13424470196063 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363611903/10000000000 : ℝ), (5280676683/10000000000 : ℝ), (-1101681127/5000000000 : ℝ)] ![(43735519383567/100000000000000 : ℝ), (42840010413009/100000000000000 : ℝ), (13424470196063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363611903/10000000000 : ℝ)|^2075 ≤ (43735519383567/100000000000000 : ℝ)^1563
        have hw : |(5363611903/10000000000 : ℝ)|=(5363611903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280676683/10000000000 : ℝ)|^2075 ≤ (42840010413009/100000000000000 : ℝ)^1563
        have hw : |(5280676683/10000000000 : ℝ)|=(5280676683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1101681127/5000000000 : ℝ)|^2075 ≤ (13424470196063/100000000000000 : ℝ)^1563
        have hw : |(-1101681127/5000000000 : ℝ)|=(1101681127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4261355977/10000000000 : ℝ)*x 0 + (4425878211/10000000000 : ℝ)*x 1 + (4425877953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261355977/10000000000 : ℝ)^2075 ≤ (1007040407497/3125000000000 : ℝ)^1563 := by
    have hnat : (4261355977 : ℕ)^2075*3125000000000^1563 ≤ 1007040407497^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261355977 10000000000 1007040407497 3125000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4425878211/10000000000 : ℝ)^2075 ≤ (33887354788519/100000000000000 : ℝ)^1563 := by
    have hnat : (4425878211 : ℕ)^2075*100000000000000^1563 ≤ 33887354788519^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425878211 10000000000 33887354788519 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4425877953/10000000000 : ℝ)^2075 ≤ (3388735216601/10000000000000 : ℝ)^1563 := by
    have hnat : (4425877953 : ℕ)^2075*10000000000000^1563 ≤ 3388735216601^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425877953 10000000000 3388735216601 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261355977/10000000000 : ℝ), (4425878211/10000000000 : ℝ), (4425877953/10000000000 : ℝ)] ![(1007040407497/3125000000000 : ℝ), (33887354788519/100000000000000 : ℝ), (3388735216601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261355977/10000000000 : ℝ)|^2075 ≤ (1007040407497/3125000000000 : ℝ)^1563
        have hw : |(4261355977/10000000000 : ℝ)|=(4261355977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4425878211/10000000000 : ℝ)|^2075 ≤ (33887354788519/100000000000000 : ℝ)^1563
        have hw : |(4425878211/10000000000 : ℝ)|=(4425878211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4425877953/10000000000 : ℝ)|^2075 ≤ (3388735216601/10000000000000 : ℝ)^1563
        have hw : |(4425877953/10000000000 : ℝ)|=(4425877953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_8 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1129689473/5000000000 : ℝ)*x 0 + (2607684197/5000000000 : ℝ)*x 1 + (336650693/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1129689473/5000000000 : ℝ)^2075 ≤ (3469859936581/25000000000000 : ℝ)^1563 := by
    have hnat : (1129689473 : ℕ)^2075*25000000000000^1563 ≤ 3469859936581^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129689473 5000000000 3469859936581 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607684197/5000000000 : ℝ)^2075 ≤ (21069031683253/50000000000000 : ℝ)^1563 := by
    have hnat : (2607684197 : ℕ)^2075*50000000000000^1563 ≤ 21069031683253^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607684197 5000000000 21069031683253 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336650693/625000000 : ℝ)^2075 ≤ (43982496865007/100000000000000 : ℝ)^1563 := by
    have hnat : (336650693 : ℕ)^2075*100000000000000^1563 ≤ 43982496865007^1563*625000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336650693 625000000 43982496865007 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1129689473/5000000000 : ℝ), (2607684197/5000000000 : ℝ), (336650693/625000000 : ℝ)] ![(3469859936581/25000000000000 : ℝ), (21069031683253/50000000000000 : ℝ), (43982496865007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1129689473/5000000000 : ℝ)|^2075 ≤ (3469859936581/25000000000000 : ℝ)^1563
        have hw : |(-1129689473/5000000000 : ℝ)|=(1129689473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607684197/5000000000 : ℝ)|^2075 ≤ (21069031683253/50000000000000 : ℝ)^1563
        have hw : |(2607684197/5000000000 : ℝ)|=(2607684197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336650693/625000000 : ℝ)|^2075 ≤ (43982496865007/100000000000000 : ℝ)^1563
        have hw : |(336650693/625000000 : ℝ)|=(336650693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_9 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288848113/10000000000 : ℝ)*x 0 + (-2161816023/10000000000 : ℝ)*x 1 + (2693205521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288848113/10000000000 : ℝ)^2075 ≤ (21464019851253/50000000000000 : ℝ)^1563 := by
    have hnat : (5288848113 : ℕ)^2075*50000000000000^1563 ≤ 21464019851253^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288848113 10000000000 21464019851253 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161816023/10000000000 : ℝ)^2075 ≤ (104715711359/800000000000 : ℝ)^1563 := by
    have hnat : (2161816023 : ℕ)^2075*800000000000^1563 ≤ 104715711359^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161816023 10000000000 104715711359 800000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693205521/5000000000 : ℝ)^2075 ≤ (8796499273271/20000000000000 : ℝ)^1563 := by
    have hnat : (2693205521 : ℕ)^2075*20000000000000^1563 ≤ 8796499273271^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693205521 5000000000 8796499273271 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288848113/10000000000 : ℝ), (-2161816023/10000000000 : ℝ), (2693205521/5000000000 : ℝ)] ![(21464019851253/50000000000000 : ℝ), (104715711359/800000000000 : ℝ), (8796499273271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288848113/10000000000 : ℝ)|^2075 ≤ (21464019851253/50000000000000 : ℝ)^1563
        have hw : |(5288848113/10000000000 : ℝ)|=(5288848113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2161816023/10000000000 : ℝ)|^2075 ≤ (104715711359/800000000000 : ℝ)^1563
        have hw : |(-2161816023/10000000000 : ℝ)|=(2161816023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693205521/5000000000 : ℝ)|^2075 ≤ (8796499273271/20000000000000 : ℝ)^1563
        have hw : |(2693205521/5000000000 : ℝ)|=(2693205521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_10 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288848213/10000000000 : ℝ)*x 0 + (5386411063/10000000000 : ℝ)*x 1 + (-2161815861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288848213/10000000000 : ℝ)^2075 ≤ (2146402039003/5000000000000 : ℝ)^1563 := by
    have hnat : (5288848213 : ℕ)^2075*5000000000000^1563 ≤ 2146402039003^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288848213 10000000000 2146402039003 5000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386411063/10000000000 : ℝ)^2075 ≤ (21991248297/50000000000 : ℝ)^1563 := by
    have hnat : (5386411063 : ℕ)^2075*50000000000^1563 ≤ 21991248297^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386411063 10000000000 21991248297 50000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161815861/10000000000 : ℝ)^2075 ≤ (3272365654419/25000000000000 : ℝ)^1563 := by
    have hnat : (2161815861 : ℕ)^2075*25000000000000^1563 ≤ 3272365654419^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161815861 10000000000 3272365654419 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288848213/10000000000 : ℝ), (5386411063/10000000000 : ℝ), (-2161815861/10000000000 : ℝ)] ![(2146402039003/5000000000000 : ℝ), (21991248297/50000000000 : ℝ), (3272365654419/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288848213/10000000000 : ℝ)|^2075 ≤ (2146402039003/5000000000000 : ℝ)^1563
        have hw : |(5288848213/10000000000 : ℝ)|=(5288848213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386411063/10000000000 : ℝ)|^2075 ≤ (21991248297/50000000000 : ℝ)^1563
        have hw : |(5386411063/10000000000 : ℝ)|=(5386411063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2161815861/10000000000 : ℝ)|^2075 ≤ (3272365654419/25000000000000 : ℝ)^1563
        have hw : |(-2161815861/10000000000 : ℝ)|=(2161815861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_11 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2249444083/5000000000 : ℝ)*x 0 + (430699251/1000000000 : ℝ)*x 1 + (269187039/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2249444083/5000000000 : ℝ)^2075 ≤ (4328935197163/12500000000000 : ℝ)^1563 := by
    have hnat : (2249444083 : ℕ)^2075*12500000000000^1563 ≤ 4328935197163^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249444083 5000000000 4328935197163 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430699251/1000000000 : ℝ)^2075 ≤ (32684258626759/100000000000000 : ℝ)^1563 := by
    have hnat : (430699251 : ℕ)^2075*100000000000000^1563 ≤ 32684258626759^1563*1000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430699251 1000000000 32684258626759 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269187039/625000000 : ℝ)^2075 ≤ (8171064943813/25000000000000 : ℝ)^1563 := by
    have hnat : (269187039 : ℕ)^2075*25000000000000^1563 ≤ 8171064943813^1563*625000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269187039 625000000 8171064943813 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2249444083/5000000000 : ℝ), (430699251/1000000000 : ℝ), (269187039/625000000 : ℝ)] ![(4328935197163/12500000000000 : ℝ), (32684258626759/100000000000000 : ℝ), (8171064943813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2249444083/5000000000 : ℝ)|^2075 ≤ (4328935197163/12500000000000 : ℝ)^1563
        have hw : |(2249444083/5000000000 : ℝ)|=(2249444083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430699251/1000000000 : ℝ)|^2075 ≤ (32684258626759/100000000000000 : ℝ)^1563
        have hw : |(430699251/1000000000 : ℝ)|=(430699251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269187039/625000000 : ℝ)|^2075 ≤ (8171064943813/25000000000000 : ℝ)^1563
        have hw : |(269187039/625000000 : ℝ)|=(269187039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_12 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054912133/5000000000 : ℝ)*x 0 + (2720405109/5000000000 : ℝ)*x 1 + (659081829/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054912133/5000000000 : ℝ)^2075 ≤ (12673195670377/100000000000000 : ℝ)^1563 := by
    have hnat : (1054912133 : ℕ)^2075*100000000000000^1563 ≤ 12673195670377^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054912133 5000000000 12673195670377 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720405109/5000000000 : ℝ)^2075 ≤ (22286585284949/50000000000000 : ℝ)^1563 := by
    have hnat : (2720405109 : ℕ)^2075*50000000000000^1563 ≤ 22286585284949^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720405109 5000000000 22286585284949 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659081829/1250000000 : ℝ)^2075 ≤ (21376816874983/50000000000000 : ℝ)^1563 := by
    have hnat : (659081829 : ℕ)^2075*50000000000000^1563 ≤ 21376816874983^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659081829 1250000000 21376816874983 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054912133/5000000000 : ℝ), (2720405109/5000000000 : ℝ), (659081829/1250000000 : ℝ)] ![(12673195670377/100000000000000 : ℝ), (22286585284949/50000000000000 : ℝ), (21376816874983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054912133/5000000000 : ℝ)|^2075 ≤ (12673195670377/100000000000000 : ℝ)^1563
        have hw : |(-1054912133/5000000000 : ℝ)|=(1054912133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720405109/5000000000 : ℝ)|^2075 ≤ (22286585284949/50000000000000 : ℝ)^1563
        have hw : |(2720405109/5000000000 : ℝ)|=(2720405109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659081829/1250000000 : ℝ)|^2075 ≤ (21376816874983/50000000000000 : ℝ)^1563
        have hw : |(659081829/1250000000 : ℝ)|=(659081829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_13 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684640787/5000000000 : ℝ)*x 0 + (-220645077/1000000000 : ℝ)*x 1 + (164770467/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684640787/5000000000 : ℝ)^2075 ≤ (43796905349007/100000000000000 : ℝ)^1563 := by
    have hnat : (2684640787 : ℕ)^2075*100000000000000^1563 ≤ 43796905349007^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684640787 5000000000 43796905349007 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220645077/1000000000 : ℝ)^2075 ≤ (13449457528423/100000000000000 : ℝ)^1563 := by
    have hnat : (220645077 : ℕ)^2075*100000000000000^1563 ≤ 13449457528423^1563*1000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220645077 1000000000 13449457528423 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164770467/312500000 : ℝ)^2075 ≤ (42753637108559/100000000000000 : ℝ)^1563 := by
    have hnat : (164770467 : ℕ)^2075*100000000000000^1563 ≤ 42753637108559^1563*312500000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164770467 312500000 42753637108559 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684640787/5000000000 : ℝ), (-220645077/1000000000 : ℝ), (164770467/312500000 : ℝ)] ![(43796905349007/100000000000000 : ℝ), (13449457528423/100000000000000 : ℝ), (42753637108559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684640787/5000000000 : ℝ)|^2075 ≤ (43796905349007/100000000000000 : ℝ)^1563
        have hw : |(2684640787/5000000000 : ℝ)|=(2684640787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220645077/1000000000 : ℝ)|^2075 ≤ (13449457528423/100000000000000 : ℝ)^1563
        have hw : |(-220645077/1000000000 : ℝ)|=(220645077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164770467/312500000 : ℝ)|^2075 ≤ (42753637108559/100000000000000 : ℝ)^1563
        have hw : |(164770467/312500000 : ℝ)|=(164770467/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_14 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684640743/5000000000 : ℝ)*x 0 + (1054531001/2000000000 : ℝ)*x 1 + (-1103225403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684640743/5000000000 : ℝ)^2075 ≤ (2189845219803/5000000000000 : ℝ)^1563 := by
    have hnat : (2684640743 : ℕ)^2075*5000000000000^1563 ≤ 2189845219803^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684640743 5000000000 2189845219803 5000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054531001/2000000000 : ℝ)^2075 ≤ (5344204720651/12500000000000 : ℝ)^1563 := by
    have hnat : (1054531001 : ℕ)^2075*12500000000000^1563 ≤ 5344204720651^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054531001 2000000000 5344204720651 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103225403/5000000000 : ℝ)^2075 ≤ (2689891563949/20000000000000 : ℝ)^1563 := by
    have hnat : (1103225403 : ℕ)^2075*20000000000000^1563 ≤ 2689891563949^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103225403 5000000000 2689891563949 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684640743/5000000000 : ℝ), (1054531001/2000000000 : ℝ), (-1103225403/5000000000 : ℝ)] ![(2189845219803/5000000000000 : ℝ), (5344204720651/12500000000000 : ℝ), (2689891563949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684640743/5000000000 : ℝ)|^2075 ≤ (2189845219803/5000000000000 : ℝ)^1563
        have hw : |(2684640743/5000000000 : ℝ)|=(2684640743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054531001/2000000000 : ℝ)|^2075 ≤ (5344204720651/12500000000000 : ℝ)^1563
        have hw : |(1054531001/2000000000 : ℝ)|=(1054531001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103225403/5000000000 : ℝ)|^2075 ≤ (2689891563949/20000000000000 : ℝ)^1563
        have hw : |(-1103225403/5000000000 : ℝ)|=(1103225403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_box_15 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4243082357/10000000000 : ℝ)*x 0 + (443489297/1000000000 : ℝ)*x 1 + (4434892757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243082357/10000000000 : ℝ)^2075 ≤ (16020982827781/50000000000000 : ℝ)^1563 := by
    have hnat : (4243082357 : ℕ)^2075*50000000000000^1563 ≤ 16020982827781^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243082357 10000000000 16020982827781 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443489297/1000000000 : ℝ)^2075 ≤ (8494754562211/25000000000000 : ℝ)^1563 := by
    have hnat : (443489297 : ℕ)^2075*25000000000000^1563 ≤ 8494754562211^1563*1000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443489297 1000000000 8494754562211 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4434892757/10000000000 : ℝ)^2075 ≤ (16989508041153/50000000000000 : ℝ)^1563 := by
    have hnat : (4434892757 : ℕ)^2075*50000000000000^1563 ≤ 16989508041153^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434892757 10000000000 16989508041153 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243082357/10000000000 : ℝ), (443489297/1000000000 : ℝ), (4434892757/10000000000 : ℝ)] ![(16020982827781/50000000000000 : ℝ), (8494754562211/25000000000000 : ℝ), (16989508041153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243082357/10000000000 : ℝ)|^2075 ≤ (16020982827781/50000000000000 : ℝ)^1563
        have hw : |(4243082357/10000000000 : ℝ)|=(4243082357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(443489297/1000000000 : ℝ)|^2075 ≤ (8494754562211/25000000000000 : ℝ)^1563
        have hw : |(443489297/1000000000 : ℝ)|=(443489297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4434892757/10000000000 : ℝ)|^2075 ≤ (16989508041153/50000000000000 : ℝ)^1563
        have hw : |(4434892757/10000000000 : ℝ)|=(4434892757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62227/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7409/12500 : ℝ) ∧ (797/1000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41523/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2827/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2827/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2827/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2827/25000 : ℝ) ^ (8299/2048 : ℝ) ≤ (7295520957233299/50000000000000000000 : ℝ) := by
    have hpowers : (2827/25000 : ℝ)^8299 ≤ (7295520957233299/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2827 : ℕ)^8299*50000000000000000000^2048 ≤ 7295520957233299^2048*25000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2827 25000 7295520957233299 50000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2827/25000 : ℝ)) (X := (7295520957233299/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3507/25000 : ℝ) ^ (8299/2048 : ℝ) ≤ (34947562415722301/100000000000000000000 : ℝ) := by
    have hpowers : (3507/25000 : ℝ)^8299 ≤ (34947562415722301/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3507 : ℕ)^8299*100000000000000000000^2048 ≤ 34947562415722301^2048*25000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3507 25000 34947562415722301 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3507/25000 : ℝ)) (X := (34947562415722301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007295520957233299/25000000000000000000 : ℝ) ≤ (1250090008345059/1250000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (25007295520957233299/25000000000000000000 : ℝ)^2048 ≤ (1250090008345059/1250000000000000 : ℝ)^8299 := by
      have hnat : (25007295520957233299 : ℕ)^2048*1250000000000000^8299 ≤ 1250090008345059^8299*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007295520957233299 25000000000000000000 1250090008345059 1250000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250090008345059/1250000000000000 : ℝ)) (X := (25007295520957233299/25000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049538604330188899/100000000000000000000 : ℝ) ≤ (10001222269416353/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (100049538604330188899/100000000000000000000 : ℝ)^2048 ≤ (10001222269416353/10000000000000000 : ℝ)^8299 := by
      have hnat : (100049538604330188899 : ℕ)^2048*10000000000000000^8299 ≤ 10001222269416353^8299*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049538604330188899 100000000000000000000 10001222269416353 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001222269416353/10000000000000000 : ℝ)) (X := (100049538604330188899/100000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034947562415722301/50000000000000000000 : ℝ) ≤ (5000862236036117/5000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50034947562415722301/50000000000000000000 : ℝ)^2048 ≤ (5000862236036117/5000000000000000 : ℝ)^8299 := by
      have hnat : (50034947562415722301 : ℕ)^2048*5000000000000000^8299 ≤ 5000862236036117^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034947562415722301 50000000000000000000 5000862236036117 5000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000862236036117/5000000000000000 : ℝ)) (X := (50034947562415722301/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7295520957233299/50000000000000000000 : ℝ) ≤ ((3398825095790384893/3400000000000000000 : ℝ)+2*(502202655881/272000000000000 : ℝ)*(2827/25000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (3398825095790384893/3400000000000000000 : ℝ)+2*(502202655881/272000000000000 : ℝ)*(2827/25000 : ℝ)=(1250090008345059/1250000000000000 : ℝ) by norm_num, show 1+2*(7295520957233299/50000000000000000000 : ℝ)=(25007295520957233299/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34947562415722301/100000000000000000000 : ℝ)+(7295520957233299/50000000000000000000 : ℝ) ≤ ((3398825095790384893/3400000000000000000 : ℝ)+(502202655881/272000000000000 : ℝ)*((3507/25000 : ℝ)+(2827/25000 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (3398825095790384893/3400000000000000000 : ℝ)+(502202655881/272000000000000 : ℝ)*((3507/25000 : ℝ)+(2827/25000 : ℝ))=(10001222269416353/10000000000000000 : ℝ) by norm_num, show 1+(34947562415722301/100000000000000000000 : ℝ)+(7295520957233299/50000000000000000000 : ℝ)=(100049538604330188899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34947562415722301/100000000000000000000 : ℝ) ≤ ((3398825095790384893/3400000000000000000 : ℝ)+2*(502202655881/272000000000000 : ℝ)*(3507/25000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (3398825095790384893/3400000000000000000 : ℝ)+2*(502202655881/272000000000000 : ℝ)*(3507/25000 : ℝ)=(5000862236036117/5000000000000000 : ℝ) by norm_num, show 1+2*(34947562415722301/100000000000000000000 : ℝ)=(50034947562415722301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3398825095790384893/3400000000000000000 : ℝ)*(X 1 0+X 2 0)+(502202655881/272000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (3398825095790384893/3400000000000000000 : ℝ)) (alpha := (502202655881/272000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3398825095790384893/3400000000000000000 : ℝ)*(X 0 1+X 2 1)+(502202655881/272000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (3398825095790384893/3400000000000000000 : ℝ)) (alpha := (502202655881/272000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3398825095790384893/3400000000000000000 : ℝ)*(X 0 2+X 1 2)+(502202655881/272000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (2827/25000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (3398825095790384893/3400000000000000000 : ℝ)) (alpha := (502202655881/272000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-205567393/1000000000 : ℝ)*X 0 0+(5376805309/10000000000 : ℝ)*X 0 1+(336050329/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647821789/5000000000 : ℝ)*X 1 0+(-1082826877/5000000000 : ℝ)*X 1 1+(672100667/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647821747/5000000000 : ℝ)*X 2 0+(5376805183/10000000000 : ℝ)*X 2 1+(-2165654073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2238778427/5000000000 : ℝ)*X 0 0+(4317798429/10000000000 : ℝ)*X 0 1+(539724887/1250000000 : ℝ)*X 0 2+(2238778427/5000000000 : ℝ)*X 1 0+(4317798429/10000000000 : ℝ)*X 1 1+(539724887/1250000000 : ℝ)*X 1 2+(2238778427/5000000000 : ℝ)*X 2 0+(4317798429/10000000000 : ℝ)*X 2 1+(539724887/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2313187599/10000000000 : ℝ)*X 0 0+(52806773/100000000 : ℝ)*X 0 1+(5280676897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363611539/10000000000 : ℝ)*X 1 0+(-13771011/62500000 : ℝ)*X 1 1+(5280677419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363611903/10000000000 : ℝ)*X 2 0+(5280676683/10000000000 : ℝ)*X 2 1+(-1101681127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4261355977/10000000000 : ℝ)*X 0 0+(4425878211/10000000000 : ℝ)*X 0 1+(4425877953/10000000000 : ℝ)*X 0 2+(4261355977/10000000000 : ℝ)*X 1 0+(4425878211/10000000000 : ℝ)*X 1 1+(4425877953/10000000000 : ℝ)*X 1 2+(4261355977/10000000000 : ℝ)*X 2 0+(4425878211/10000000000 : ℝ)*X 2 1+(4425877953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1129689473/5000000000 : ℝ)*X 0 0+(2607684197/5000000000 : ℝ)*X 0 1+(336650693/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288848113/10000000000 : ℝ)*X 1 0+(-2161816023/10000000000 : ℝ)*X 1 1+(2693205521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288848213/10000000000 : ℝ)*X 2 0+(5386411063/10000000000 : ℝ)*X 2 1+(-2161815861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2249444083/5000000000 : ℝ)*X 0 0+(430699251/1000000000 : ℝ)*X 0 1+(269187039/625000000 : ℝ)*X 0 2+(2249444083/5000000000 : ℝ)*X 1 0+(430699251/1000000000 : ℝ)*X 1 1+(269187039/625000000 : ℝ)*X 1 2+(2249444083/5000000000 : ℝ)*X 2 0+(430699251/1000000000 : ℝ)*X 2 1+(269187039/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1054912133/5000000000 : ℝ)*X 0 0+(2720405109/5000000000 : ℝ)*X 0 1+(659081829/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684640787/5000000000 : ℝ)*X 1 0+(-220645077/1000000000 : ℝ)*X 1 1+(164770467/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684640743/5000000000 : ℝ)*X 2 0+(1054531001/2000000000 : ℝ)*X 2 1+(-1103225403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4243082357/10000000000 : ℝ)*X 0 0+(443489297/1000000000 : ℝ)*X 0 1+(4434892757/10000000000 : ℝ)*X 0 2+(4243082357/10000000000 : ℝ)*X 1 0+(443489297/1000000000 : ℝ)*X 1 1+(4434892757/10000000000 : ℝ)*X 1 2+(4243082357/10000000000 : ℝ)*X 2 0+(443489297/1000000000 : ℝ)*X 2 1+(4434892757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62227/100000 : ℝ) ≤ (-105782487532315094938721960669229/170000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (142318823/100000000000000 : ℝ)*(upper3) + (27841289/50000000000000 : ℝ)*(lower4) + (46433909/100000000000000 : ℝ)*(lower5) + (3891093703628549/100000000000000 : ℝ)*(major0) + (3891093703628549/100000000000000 : ℝ)*(major1) + (3891093703628549/100000000000000 : ℝ)*(major2) + (13116096133/50000000000000 : ℝ)*(sp2) + (1973746597/50000000000000 : ℝ)*(sp3) + (5187790113295231/100000000000000 : ℝ)*(sp4) + (129691915250161/2500000000000 : ℝ)*(sp5) + (1037553434226241/20000000000000 : ℝ)*(sp6) + (163445732541403/6250000000000 : ℝ)*(sp7) + (3290028241/100000000000000 : ℝ)*(sp8) + (14599164629/12500000000000 : ℝ)*(sp13) + (1307567834077821/50000000000000 : ℝ)*(f.failure) + (324237087707717/6250000000000 : ℝ)*(f.sum) + (4838787715469/13600000000000000000000000000 : ℝ)*base65 + (49299811998442779/20000000000000000000000000000000 : ℝ)*base68 + (358695651498442779/20000000000000000000000000000000 : ℝ)*base70 + (89526210161557221/20000000000000000000000000000000 : ℝ)*base71 + (31918907836269/13600000000000000000000000000 : ℝ)*base73 + (79681054558442779/20000000000000000000000000000000 : ℝ)*base76 + (14603209658442779/20000000000000000000000000000000 : ℝ)*base78 + (65905459221557221/20000000000000000000000000000000 : ℝ)*base79 + (80237060341331/13600000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (567529/200000000000000000000 : ℝ)*base90 + (567529/200000000000000000000 : ℝ)*base92 + (567529/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (7409/12500 : ℝ) ≤ (25191481455917767663855447017771/42500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5056469/20000000000000 : ℝ)*(upper0) + (31220617/50000000000000 : ℝ)*(lower1) + (36389819/20000000000000 : ℝ)*(upper2) + (1977335424137799/50000000000000 : ℝ)*(major0) + (1977335424137799/50000000000000 : ℝ)*(major1) + (1977335424137799/50000000000000 : ℝ)*(major2) + (653963532772539/12500000000000 : ℝ)*(sp0) + (261585497477497/5000000000000 : ℝ)*(sp1) + (261580279337217/5000000000000 : ℝ)*(sp2) + (1328930616466987/50000000000000 : ℝ)*(sp3) + (8973018799/100000000000000 : ℝ)*(sp5) + (1758188583/50000000000000 : ℝ)*(sp7) + (113335824399/100000000000000 : ℝ)*(sp10) + (5330194213/50000000000000 : ℝ)*(sp12) + (132893237465557/5000000000000 : ℝ)*(f.failure) + (5231718922568739/100000000000000 : ℝ)*(f.sum) + (789537267681/6800000000000000000000000000 : ℝ)*base66 + (73720337320949529/10000000000000000000000000000000 : ℝ)*base68 + (15800761139050471/10000000000000000000000000000000 : ℝ)*base69 + (67825495430949529/10000000000000000000000000000000 : ℝ)*base72 + (163788858183681/6800000000000000000000000000 : ℝ)*base74 + (118053519070949529/10000000000000000000000000000000 : ℝ)*base76 + (13462155090949529/10000000000000000000000000000000 : ℝ)*base78 + (162722608130949529/10000000000000000000000000000000 : ℝ)*base80 + (5968769786481/6800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (184607/20000000000000000000 : ℝ)*base89 + (184607/20000000000000000000 : ℝ)*base91 + (184607/20000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (797/1000 : ℝ) ≤ (135494786699987523108940883734251/170000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157403/20000000000000 : ℝ)*(upper0) + (42633151/100000000000000 : ℝ)*(lower1) + (68438073/100000000000000 : ℝ)*(lower3) + (1762209/2000000000000 : ℝ)*(upper4) + (4422763524398331/100000000000000 : ℝ)*(major0) + (4422763524398331/100000000000000 : ℝ)*(major1) + (4422763524398331/100000000000000 : ℝ)*(major2) + (1133658009/100000000000000 : ℝ)*(sp0) + (43626557811/100000000000000 : ℝ)*(sp2) + (13417566439/20000000000000 : ℝ)*(sp3) + (2923248351297921/50000000000000 : ℝ)*(sp8) + (116929956725077/2000000000000 : ℝ)*(sp9) + (5846454209696039/100000000000000 : ℝ)*(sp10) + (297239451947531/10000000000000 : ℝ)*(sp11) + (1486230803653753/50000000000000 : ℝ)*(f.failure) + (116929956725077/2000000000000 : ℝ)*(f.sum) + (80309229737811/13600000000000000000000000000 : ℝ)*base65 + (109956459243561701/20000000000000000000000000000000 : ℝ)*base68 + (1106240993796438299/20000000000000000000000000000000 : ℝ)*base69 + (267174665636438299/20000000000000000000000000000000 : ℝ)*base71 + (41579651346611/13600000000000000000000000000 : ℝ)*base73 + (437109869236438299/20000000000000000000000000000000 : ℝ)*base75 + (206897167816438299/20000000000000000000000000000000 : ℝ)*base77 + (59288986063561701/20000000000000000000000000000000 : ℝ)*base80 + (20552073406189/13600000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (696203/200000000000000000000 : ℝ)*base89 + (696203/200000000000000000000 : ℝ)*base91 + (696203/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-41523/50000 : ℝ) ≤ (-70586737876297119731760966106983/85000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29862063/100000000000000 : ℝ)*(lower0) + (77708089/100000000000000 : ℝ)*(upper3) + (5653921/50000000000000 : ℝ)*(lower4) + (4457514760161127/100000000000000 : ℝ)*(major0) + (4457514760161127/100000000000000 : ℝ)*(major1) + (4457514760161127/100000000000000 : ℝ)*(major2) + (1320622383/10000000000000 : ℝ)*(sp0) + (36176865599/50000000000000 : ℝ)*(sp5) + (7970501747/12500000000000 : ℝ)*(sp7) + (622754257/25000000000000 : ℝ)*(sp8) + (2973438797431363/50000000000000 : ℝ)*(sp12) + (2973410469186193/50000000000000 : ℝ)*(sp13) + (185840415378237/3125000000000 : ℝ)*(sp14) + (2995753537881667/100000000000000 : ℝ)*(sp15) + (748954325473911/25000000000000 : ℝ)*(f.failure) + (185840415378237/3125000000000 : ℝ)*(f.sum) + (17233043866687/13600000000000000000000000000 : ℝ)*base65 + (73777397535896583/20000000000000000000000000000000 : ℝ)*base67 + (66367257804103417/20000000000000000000000000000000 : ℝ)*base70 + (33417912315896583/20000000000000000000000000000000 : ℝ)*base71 + (81166615864287/13600000000000000000000000000 : ℝ)*base73 + (140430743595896583/20000000000000000000000000000000 : ℝ)*base75 + (62055181555896583/20000000000000000000000000000000 : ℝ)*base77 + (123885854535896583/20000000000000000000000000000000 : ℝ)*base79 + (22083715326913/13600000000000000000000000000 : ℝ)*base82 + (877061/100000000000000000000 : ℝ)*base89 + (877061/100000000000000000000 : ℝ)*base91 + (877061/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1107_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2827/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7409/12500 : ℝ) else (797/1000 : ℝ) ≤ X j i ∧ X j i ≤ (41523/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1107_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1107_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7409/12500 : ℝ) else (797/1000 : ℝ) ≤ X j i ∧ X j i ≤ (41523/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1107_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1107_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7409/12500 : ℝ) else (797/1000 : ℝ) ≤ X j i ∧ X j i ≤ (41523/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1107_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

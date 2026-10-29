-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1376_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:04.983525+00:00
-- url     : https://prove2.me/submissions/f23061f7-cc1b-421f-b83e-23bc969439b5

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
theorem support_rectangle_w1376_s0_0 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-357843183/2000000000 : ℝ)*x 0 + (2991180669/5000000000 : ℝ)*x 1 + (4818955981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357843183/2000000000 : ℝ)^271 ≤ (2627495432453/25000000000000 : ℝ)^207 := by
    have hnat : (357843183 : ℕ)^271*25000000000000^207 ≤ 2627495432453^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357843183 2000000000 2627495432453 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2991180669/5000000000 : ℝ)^271 ≤ (51037148812921/100000000000000 : ℝ)^207 := by
    have hnat : (2991180669 : ℕ)^271*100000000000000^207 ≤ 51037148812921^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991180669 5000000000 51037148812921 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4818955981/10000000000 : ℝ)^271 ≤ (19226434720501/50000000000000 : ℝ)^207 := by
    have hnat : (4818955981 : ℕ)^271*50000000000000^207 ≤ 19226434720501^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4818955981 10000000000 19226434720501 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357843183/2000000000 : ℝ), (2991180669/5000000000 : ℝ), (4818955981/10000000000 : ℝ)] ![(2627495432453/25000000000000 : ℝ), (51037148812921/100000000000000 : ℝ), (19226434720501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357843183/2000000000 : ℝ)|^271 ≤ (2627495432453/25000000000000 : ℝ)^207
        have hw : |(-357843183/2000000000 : ℝ)|=(357843183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2991180669/5000000000 : ℝ)|^271 ≤ (51037148812921/100000000000000 : ℝ)^207
        have hw : |(2991180669/5000000000 : ℝ)|=(2991180669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4818955981/10000000000 : ℝ)|^271 ≤ (19226434720501/50000000000000 : ℝ)^207
        have hw : |(4818955981/10000000000 : ℝ)|=(4818955981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s0_1 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5498009169/10000000000 : ℝ)*x 0 + (-24488729/100000000 : ℝ)*x 1 + (75296197/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5498009169/10000000000 : ℝ)^271 ≤ (357003554761/781250000000 : ℝ)^207 := by
    have hnat : (5498009169 : ℕ)^271*781250000000^207 ≤ 357003554761^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498009169 10000000000 357003554761 781250000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24488729/100000000 : ℝ)^271 ≤ (15850668979001/100000000000000 : ℝ)^207 := by
    have hnat : (24488729 : ℕ)^271*100000000000000^207 ≤ 15850668979001^207*100000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24488729 100000000 15850668979001 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75296197/156250000 : ℝ)^271 ≤ (38452875991017/100000000000000 : ℝ)^207 := by
    have hnat : (75296197 : ℕ)^271*100000000000000^207 ≤ 38452875991017^207*156250000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75296197 156250000 38452875991017 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5498009169/10000000000 : ℝ), (-24488729/100000000 : ℝ), (75296197/156250000 : ℝ)] ![(357003554761/781250000000 : ℝ), (15850668979001/100000000000000 : ℝ), (38452875991017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5498009169/10000000000 : ℝ)|^271 ≤ (357003554761/781250000000 : ℝ)^207
        have hw : |(5498009169/10000000000 : ℝ)|=(5498009169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24488729/100000000 : ℝ)|^271 ≤ (15850668979001/100000000000000 : ℝ)^207
        have hw : |(-24488729/100000000 : ℝ)|=(24488729/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75296197/156250000 : ℝ)|^271 ≤ (38452875991017/100000000000000 : ℝ)^207
        have hw : |(75296197/156250000 : ℝ)|=(75296197/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s0_2 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1374502263/2500000000 : ℝ)*x 0 + (301184743/625000000 : ℝ)*x 1 + (-1224436969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374502263/2500000000 : ℝ)^271 ≤ (4569645373631/10000000000000 : ℝ)^207 := by
    have hnat : (1374502263 : ℕ)^271*10000000000000^207 ≤ 4569645373631^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374502263 2500000000 4569645373631 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301184743/625000000 : ℝ)^271 ≤ (38452868469469/100000000000000 : ℝ)^207 := by
    have hnat : (301184743 : ℕ)^271*100000000000000^207 ≤ 38452868469469^207*625000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301184743 625000000 38452868469469 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1224436969/5000000000 : ℝ)^271 ≤ (30958355029/195312500000 : ℝ)^207 := by
    have hnat : (1224436969 : ℕ)^271*195312500000^207 ≤ 30958355029^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224436969 5000000000 30958355029 195312500000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374502263/2500000000 : ℝ), (301184743/625000000 : ℝ), (-1224436969/5000000000 : ℝ)] ![(4569645373631/10000000000000 : ℝ), (38452868469469/100000000000000 : ℝ), (30958355029/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374502263/2500000000 : ℝ)|^271 ≤ (4569645373631/10000000000000 : ℝ)^207
        have hw : |(1374502263/2500000000 : ℝ)|=(1374502263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301184743/625000000 : ℝ)|^271 ≤ (38452868469469/100000000000000 : ℝ)^207
        have hw : |(301184743/625000000 : ℝ)|=(301184743/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1224436969/5000000000 : ℝ)|^271 ≤ (30958355029/195312500000 : ℝ)^207
        have hw : |(-1224436969/5000000000 : ℝ)|=(1224436969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s0_3 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (65214081/156250000 : ℝ)*x 0 + (1552525663/5000000000 : ℝ)*x 1 + (5573096193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65214081/156250000 : ℝ)^271 ≤ (31856247801617/100000000000000 : ℝ)^207 := by
    have hnat : (65214081 : ℕ)^271*100000000000000^207 ≤ 31856247801617^207*156250000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65214081 156250000 31856247801617 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552525663/5000000000 : ℝ)^271 ≤ (21628542178601/100000000000000 : ℝ)^207 := by
    have hnat : (1552525663 : ℕ)^271*100000000000000^207 ≤ 21628542178601^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552525663 5000000000 21628542178601 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5573096193/10000000000 : ℝ)^271 ≤ (46515210005401/100000000000000 : ℝ)^207 := by
    have hnat : (5573096193 : ℕ)^271*100000000000000^207 ≤ 46515210005401^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573096193 10000000000 46515210005401 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65214081/156250000 : ℝ), (1552525663/5000000000 : ℝ), (5573096193/10000000000 : ℝ)] ![(31856247801617/100000000000000 : ℝ), (21628542178601/100000000000000 : ℝ), (46515210005401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65214081/156250000 : ℝ)|^271 ≤ (31856247801617/100000000000000 : ℝ)^207
        have hw : |(65214081/156250000 : ℝ)|=(65214081/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1552525663/5000000000 : ℝ)|^271 ≤ (21628542178601/100000000000000 : ℝ)^207
        have hw : |(1552525663/5000000000 : ℝ)|=(1552525663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5573096193/10000000000 : ℝ)|^271 ≤ (46515210005401/100000000000000 : ℝ)^207
        have hw : |(5573096193/10000000000 : ℝ)|=(5573096193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s0_4 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-179349737/1000000000 : ℝ)*x 0 + (2424417667/5000000000 : ℝ)*x 1 + (37196337/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179349737/1000000000 : ℝ)^271 ≤ (10542919187447/100000000000000 : ℝ)^207 := by
    have hnat : (179349737 : ℕ)^271*100000000000000^207 ≤ 10542919187447^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179349737 1000000000 10542919187447 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2424417667/5000000000 : ℝ)^271 ≤ (38765305689067/100000000000000 : ℝ)^207 := by
    have hnat : (2424417667 : ℕ)^271*100000000000000^207 ≤ 38765305689067^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424417667 5000000000 38765305689067 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37196337/62500000 : ℝ)^271 ≤ (50691775109861/100000000000000 : ℝ)^207 := by
    have hnat : (37196337 : ℕ)^271*100000000000000^207 ≤ 50691775109861^207*62500000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37196337 62500000 50691775109861 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179349737/1000000000 : ℝ), (2424417667/5000000000 : ℝ), (37196337/62500000 : ℝ)] ![(10542919187447/100000000000000 : ℝ), (38765305689067/100000000000000 : ℝ), (50691775109861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179349737/1000000000 : ℝ)|^271 ≤ (10542919187447/100000000000000 : ℝ)^207
        have hw : |(-179349737/1000000000 : ℝ)|=(179349737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2424417667/5000000000 : ℝ)|^271 ≤ (38765305689067/100000000000000 : ℝ)^207
        have hw : |(2424417667/5000000000 : ℝ)|=(2424417667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37196337/62500000 : ℝ)|^271 ≤ (50691775109861/100000000000000 : ℝ)^207
        have hw : |(37196337/62500000 : ℝ)|=(37196337/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s0_5 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5180741599/10000000000 : ℝ)*x 0 + (-82276139/625000000 : ℝ)*x 1 + (2975706259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180741599/10000000000 : ℝ)^271 ≤ (10568856376803/25000000000000 : ℝ)^207 := by
    have hnat : (5180741599 : ℕ)^271*25000000000000^207 ≤ 10568856376803^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180741599 10000000000 10568856376803 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82276139/625000000 : ℝ)^271 ≤ (7032815004009/100000000000000 : ℝ)^207 := by
    have hnat : (82276139 : ℕ)^271*100000000000000^207 ≤ 7032815004009^207*625000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82276139 625000000 7032815004009 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2975706259/5000000000 : ℝ)^271 ≤ (5069175947607/10000000000000 : ℝ)^207 := by
    have hnat : (2975706259 : ℕ)^271*10000000000000^207 ≤ 5069175947607^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2975706259 5000000000 5069175947607 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180741599/10000000000 : ℝ), (-82276139/625000000 : ℝ), (2975706259/5000000000 : ℝ)] ![(10568856376803/25000000000000 : ℝ), (7032815004009/100000000000000 : ℝ), (5069175947607/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180741599/10000000000 : ℝ)|^271 ≤ (10568856376803/25000000000000 : ℝ)^207
        have hw : |(5180741599/10000000000 : ℝ)|=(5180741599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82276139/625000000 : ℝ)|^271 ≤ (7032815004009/100000000000000 : ℝ)^207
        have hw : |(-82276139/625000000 : ℝ)|=(82276139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2975706259/5000000000 : ℝ)|^271 ≤ (5069175947607/10000000000000 : ℝ)^207
        have hw : |(2975706259/5000000000 : ℝ)|=(2975706259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s0_6 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5180740107/10000000000 : ℝ)*x 0 + (743926937/1250000000 : ℝ)*x 1 + (-658207877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180740107/10000000000 : ℝ)^271 ≤ (2642213098007/6250000000000 : ℝ)^207 := by
    have hnat : (5180740107 : ℕ)^271*6250000000000^207 ≤ 2642213098007^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180740107 10000000000 2642213098007 6250000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (743926937/1250000000 : ℝ)^271 ≤ (50691792683937/100000000000000 : ℝ)^207 := by
    have hnat : (743926937 : ℕ)^271*100000000000000^207 ≤ 50691792683937^207*1250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743926937 1250000000 50691792683937 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658207877/5000000000 : ℝ)^271 ≤ (7032797728491/100000000000000 : ℝ)^207 := by
    have hnat : (658207877 : ℕ)^271*100000000000000^207 ≤ 7032797728491^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658207877 5000000000 7032797728491 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180740107/10000000000 : ℝ), (743926937/1250000000 : ℝ), (-658207877/5000000000 : ℝ)] ![(2642213098007/6250000000000 : ℝ), (50691792683937/100000000000000 : ℝ), (7032797728491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180740107/10000000000 : ℝ)|^271 ≤ (2642213098007/6250000000000 : ℝ)^207
        have hw : |(5180740107/10000000000 : ℝ)|=(5180740107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(743926937/1250000000 : ℝ)|^271 ≤ (50691792683937/100000000000000 : ℝ)^207
        have hw : |(743926937/1250000000 : ℝ)|=(743926937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-658207877/5000000000 : ℝ)|^271 ≤ (7032797728491/100000000000000 : ℝ)^207
        have hw : |(-658207877/5000000000 : ℝ)|=(658207877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s0_7 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (32677929/78125000 : ℝ)*x 0 + (275485671/500000000 : ℝ)*x 1 + (634141007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32677929/78125000 : ℝ)^271 ≤ (31946947079823/100000000000000 : ℝ)^207 := by
    have hnat : (32677929 : ℕ)^271*100000000000000^207 ≤ 31946947079823^207*78125000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32677929 78125000 31946947079823 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275485671/500000000 : ℝ)^271 ≤ (45823852963031/100000000000000 : ℝ)^207 := by
    have hnat : (275485671 : ℕ)^271*100000000000000^207 ≤ 45823852963031^207*500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275485671 500000000 45823852963031 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634141007/2000000000 : ℝ)^271 ≤ (22229199941843/100000000000000 : ℝ)^207 := by
    have hnat : (634141007 : ℕ)^271*100000000000000^207 ≤ 22229199941843^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634141007 2000000000 22229199941843 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32677929/78125000 : ℝ), (275485671/500000000 : ℝ), (634141007/2000000000 : ℝ)] ![(31946947079823/100000000000000 : ℝ), (45823852963031/100000000000000 : ℝ), (22229199941843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32677929/78125000 : ℝ)|^271 ≤ (31946947079823/100000000000000 : ℝ)^207
        have hw : |(32677929/78125000 : ℝ)|=(32677929/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275485671/500000000 : ℝ)|^271 ≤ (45823852963031/100000000000000 : ℝ)^207
        have hw : |(275485671/500000000 : ℝ)|=(275485671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634141007/2000000000 : ℝ)|^271 ≤ (22229199941843/100000000000000 : ℝ)^207
        have hw : |(634141007/2000000000 : ℝ)|=(634141007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1376_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (833/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6657/25000 : ℝ)*pair X 0 0 := by
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
  have base53 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign3]
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
  have hpowlo : (0 : ℝ) ^ (4335/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4335 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4335*1^1024 ≤ 0^1024*1^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4335/1024 : ℝ) ≤ (2067099533979093447/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4335 ≤ (2067099533979093447/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4335*100000000000000000000^1024 ≤ 2067099533979093447^1024*5^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2067099533979093447 100000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2067099533979093447/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4335 := by
      have hnat : (1 : ℕ)^1024*1^4335 ≤ 1^4335*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102067099533979093447/100000000000000000000 : ℝ) ≤ (10048447535465511/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (102067099533979093447/100000000000000000000 : ℝ)^1024 ≤ (10048447535465511/10000000000000000 : ℝ)^4335 := by
      have hnat : (102067099533979093447 : ℕ)^1024*10000000000000000^4335 ≤ 10048447535465511^4335*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102067099533979093447 100000000000000000000 10048447535465511 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048447535465511/10000000000000000 : ℝ)) (X := (102067099533979093447/100000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52067099533979093447/50000000000000000000 : ℝ) ≤ (5048447535465511/5000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (52067099533979093447/50000000000000000000 : ℝ)^1024 ≤ (5048447535465511/5000000000000000 : ℝ)^4335 := by
      have hnat : (52067099533979093447 : ℕ)^1024*5000000000000000^4335 ≤ 5048447535465511^4335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52067099533979093447 50000000000000000000 5048447535465511 5000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048447535465511/5000000000000000 : ℝ)) (X := (52067099533979093447/50000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(48447535465511/4000000000000000 : ℝ)*(0 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48447535465511/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2067099533979093447/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(48447535465511/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4335/1024 : ℝ) := by
    rw [show (1 : ℝ)+(48447535465511/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10048447535465511/10000000000000000 : ℝ) by norm_num, show 1+(2067099533979093447/100000000000000000000 : ℝ)+(0 : ℝ)=(102067099533979093447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2067099533979093447/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(48447535465511/4000000000000000 : ℝ)*(2/5 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48447535465511/4000000000000000 : ℝ)*(2/5 : ℝ)=(5048447535465511/5000000000000000 : ℝ) by norm_num, show 1+2*(2067099533979093447/100000000000000000000 : ℝ)=(52067099533979093447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(48447535465511/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48447535465511/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(48447535465511/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48447535465511/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(48447535465511/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48447535465511/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-357843183/2000000000 : ℝ)*X 0 0+(2991180669/5000000000 : ℝ)*X 0 1+(4818955981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5498009169/10000000000 : ℝ)*X 1 0+(-24488729/100000000 : ℝ)*X 1 1+(75296197/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1374502263/2500000000 : ℝ)*X 2 0+(301184743/625000000 : ℝ)*X 2 1+(-1224436969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((65214081/156250000 : ℝ)*X 0 0+(1552525663/5000000000 : ℝ)*X 0 1+(5573096193/10000000000 : ℝ)*X 0 2+(65214081/156250000 : ℝ)*X 1 0+(1552525663/5000000000 : ℝ)*X 1 1+(5573096193/10000000000 : ℝ)*X 1 2+(65214081/156250000 : ℝ)*X 2 0+(1552525663/5000000000 : ℝ)*X 2 1+(5573096193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-179349737/1000000000 : ℝ)*X 0 0+(2424417667/5000000000 : ℝ)*X 0 1+(37196337/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5180741599/10000000000 : ℝ)*X 1 0+(-82276139/625000000 : ℝ)*X 1 1+(2975706259/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5180740107/10000000000 : ℝ)*X 2 0+(743926937/1250000000 : ℝ)*X 2 1+(-658207877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((32677929/78125000 : ℝ)*X 0 0+(275485671/500000000 : ℝ)*X 0 1+(634141007/2000000000 : ℝ)*X 0 2+(32677929/78125000 : ℝ)*X 1 0+(275485671/500000000 : ℝ)*X 1 1+(634141007/2000000000 : ℝ)*X 1 2+(32677929/78125000 : ℝ)*X 2 0+(275485671/500000000 : ℝ)*X 2 1+(634141007/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (751260672174671390759709/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24446997/10000000000000 : ℝ)*(base1) + (1747473397/100000000000000 : ℝ)*(base19) + (1729181707/100000000000000 : ℝ)*(base23) + (62479987/20000000000000 : ℝ)*(upper3) + (7457957/20000000000000 : ℝ)*(upper5) + (632370262578327/100000000000000 : ℝ)*(major0) + (632370262578327/100000000000000 : ℝ)*(major1) + (632370262578327/100000000000000 : ℝ)*(major2) + (42977590847147/5000000000000 : ℝ)*(sp0) + (171910899354773/20000000000000 : ℝ)*(sp1) + (171910903013111/20000000000000 : ℝ)*(sp2) + (40518096155159/10000000000000 : ℝ)*(sp3) + (1167943573/25000000000000 : ℝ)*(sp4) + (1412233803/50000000000000 : ℝ)*(sp7) + (202592015244583/50000000000000 : ℝ)*(f.failure) + (429778122123631/50000000000000 : ℝ)*(f.sum) + (191739173819903/200000000000000000000000000000 : ℝ)*base66 + (2076529801380097/400000000000000000000000000000 : ℝ)*base67 + (197667699419903/400000000000000000000000000000 : ℝ)*base70 + (1007616477780097/400000000000000000000000000000 : ℝ)*base71 + (550152572580097/200000000000000000000000000000 : ℝ)*base73 + (624780155419903/400000000000000000000000000000 : ℝ)*base76 + (578082207780097/400000000000000000000000000000 : ℝ)*base77 + (539429564580097/400000000000000000000000000000 : ℝ)*base79 + (172939546580097/200000000000000000000000000000 : ℝ)*base81 + (89193/39062500000000000000 : ℝ)*base89 + (89193/39062500000000000000 : ℝ)*base91 + (89193/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (261634728363861489298617/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223739083/100000000000000 : ℝ)*(base19) + (30521923/100000000000000 : ℝ)*(base53) + (28799761/25000000000000 : ℝ)*(upper2) + (72811647/50000000000000 : ℝ)*(upper4) + (667248612005451/100000000000000 : ℝ)*(major0) + (667248612005451/100000000000000 : ℝ)*(major1) + (667248612005451/100000000000000 : ℝ)*(major2) + (10688031/20000000000000 : ℝ)*(sp0) + (1570592427/100000000000000 : ℝ)*(sp2) + (47785519/25000000000000 : ℝ)*(sp3) + (113370643553969/12500000000000 : ℝ)*(sp4) + (113370622266603/12500000000000 : ℝ)*(sp5) + (22674090781987/2500000000000 : ℝ)*(sp6) + (21376587189267/5000000000000 : ℝ)*(sp7) + (53441491865927/12500000000000 : ℝ)*(f.failure) + (906965201871907/100000000000000 : ℝ)*(f.sum) + (587113245299539/200000000000000000000000000000 : ℝ)*base66 + (2720413300900461/400000000000000000000000000000 : ℝ)*base67 + (211933169300461/400000000000000000000000000000 : ℝ)*base69 + (26955098500461/400000000000000000000000000000 : ℝ)*base71 + (90282354500461/200000000000000000000000000000 : ℝ)*base73 + (2038058794500461/400000000000000000000000000000 : ℝ)*base75 + (1720311903300461/400000000000000000000000000000 : ℝ)*base77 + (2574481421700461/400000000000000000000000000000 : ℝ)*base79 + (368965069899539/200000000000000000000000000000 : ℝ)*base82 + (12693/39062500000000000000 : ℝ)*base89 + (12693/39062500000000000000 : ℝ)*base91 + (12693/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1376_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (833/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6657/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1376_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1376_s1_0 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-196914147/1000000000 : ℝ)*x 0 + (2813602147/5000000000 : ℝ)*x 1 + (202353913/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196914147/1000000000 : ℝ)^271 ≤ (11914678898359/100000000000000 : ℝ)^207 := by
    have hnat : (196914147 : ℕ)^271*100000000000000^207 ≤ 11914678898359^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196914147 1000000000 11914678898359 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2813602147/5000000000 : ℝ)^271 ≤ (47107329785993/100000000000000 : ℝ)^207 := by
    have hnat : (2813602147 : ℕ)^271*100000000000000^207 ≤ 47107329785993^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813602147 5000000000 47107329785993 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202353913/400000000 : ℝ)^271 ≤ (40977991294299/100000000000000 : ℝ)^207 := by
    have hnat : (202353913 : ℕ)^271*100000000000000^207 ≤ 40977991294299^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202353913 400000000 40977991294299 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196914147/1000000000 : ℝ), (2813602147/5000000000 : ℝ), (202353913/400000000 : ℝ)] ![(11914678898359/100000000000000 : ℝ), (47107329785993/100000000000000 : ℝ), (40977991294299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196914147/1000000000 : ℝ)|^271 ≤ (11914678898359/100000000000000 : ℝ)^207
        have hw : |(-196914147/1000000000 : ℝ)|=(196914147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2813602147/5000000000 : ℝ)|^271 ≤ (47107329785993/100000000000000 : ℝ)^207
        have hw : |(2813602147/5000000000 : ℝ)|=(2813602147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(202353913/400000000 : ℝ)|^271 ≤ (40977991294299/100000000000000 : ℝ)^207
        have hw : |(202353913/400000000 : ℝ)|=(202353913/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s1_1 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (675274079/1250000000 : ℝ)*x 0 + (-2271567339/10000000000 : ℝ)*x 1 + (1011769841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675274079/1250000000 : ℝ)^271 ≤ (2232833912157/5000000000000 : ℝ)^207 := by
    have hnat : (675274079 : ℕ)^271*5000000000000^207 ≤ 2232833912157^207*1250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675274079 1250000000 2232833912157 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2271567339/10000000000 : ℝ)^271 ≤ (2873063161883/20000000000000 : ℝ)^207 := by
    have hnat : (2271567339 : ℕ)^271*20000000000000^207 ≤ 2873063161883^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271567339 10000000000 2873063161883 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011769841/2000000000 : ℝ)^271 ≤ (40978005928773/100000000000000 : ℝ)^207 := by
    have hnat : (1011769841 : ℕ)^271*100000000000000^207 ≤ 40978005928773^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011769841 2000000000 40978005928773 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675274079/1250000000 : ℝ), (-2271567339/10000000000 : ℝ), (1011769841/2000000000 : ℝ)] ![(2232833912157/5000000000000 : ℝ), (2873063161883/20000000000000 : ℝ), (40978005928773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675274079/1250000000 : ℝ)|^271 ≤ (2232833912157/5000000000000 : ℝ)^207
        have hw : |(675274079/1250000000 : ℝ)|=(675274079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2271567339/10000000000 : ℝ)|^271 ≤ (2873063161883/20000000000000 : ℝ)^207
        have hw : |(-2271567339/10000000000 : ℝ)|=(2271567339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1011769841/2000000000 : ℝ)|^271 ≤ (40978005928773/100000000000000 : ℝ)^207
        have hw : |(1011769841/2000000000 : ℝ)|=(1011769841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s1_2 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5402193209/10000000000 : ℝ)*x 0 + (5058848017/10000000000 : ℝ)*x 1 + (-2271568107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402193209/10000000000 : ℝ)^271 ≤ (8931336897509/20000000000000 : ℝ)^207 := by
    have hnat : (5402193209 : ℕ)^271*20000000000000^207 ≤ 8931336897509^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402193209 10000000000 8931336897509 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5058848017/10000000000 : ℝ)^271 ≤ (51222491663/125000000000 : ℝ)^207 := by
    have hnat : (5058848017 : ℕ)^271*125000000000^207 ≤ 51222491663^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5058848017 10000000000 51222491663 125000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271568107/10000000000 : ℝ)^271 ≤ (7182661083921/50000000000000 : ℝ)^207 := by
    have hnat : (2271568107 : ℕ)^271*50000000000000^207 ≤ 7182661083921^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271568107 10000000000 7182661083921 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402193209/10000000000 : ℝ), (5058848017/10000000000 : ℝ), (-2271568107/10000000000 : ℝ)] ![(8931336897509/20000000000000 : ℝ), (51222491663/125000000000 : ℝ), (7182661083921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402193209/10000000000 : ℝ)|^271 ≤ (8931336897509/20000000000000 : ℝ)^207
        have hw : |(5402193209/10000000000 : ℝ)|=(5402193209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5058848017/10000000000 : ℝ)|^271 ≤ (51222491663/125000000000 : ℝ)^207
        have hw : |(5058848017/10000000000 : ℝ)|=(5058848017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2271568107/10000000000 : ℝ)|^271 ≤ (7182661083921/50000000000000 : ℝ)^207
        have hw : |(-2271568107/10000000000 : ℝ)|=(2271568107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s1_3 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4286223247/10000000000 : ℝ)*x 0 + (148883413/400000000 : ℝ)*x 1 + (985558089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286223247/10000000000 : ℝ)^271 ≤ (8246319189861/25000000000000 : ℝ)^207 := by
    have hnat : (4286223247 : ℕ)^271*25000000000000^207 ≤ 8246319189861^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286223247 10000000000 8246319189861 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148883413/400000000 : ℝ)^271 ≤ (13710477612999/50000000000000 : ℝ)^207 := by
    have hnat : (148883413 : ℕ)^271*50000000000000^207 ≤ 13710477612999^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148883413 400000000 13710477612999 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985558089/2000000000 : ℝ)^271 ≤ (1979688399857/5000000000000 : ℝ)^207 := by
    have hnat : (985558089 : ℕ)^271*5000000000000^207 ≤ 1979688399857^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985558089 2000000000 1979688399857 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286223247/10000000000 : ℝ), (148883413/400000000 : ℝ), (985558089/2000000000 : ℝ)] ![(8246319189861/25000000000000 : ℝ), (13710477612999/50000000000000 : ℝ), (1979688399857/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286223247/10000000000 : ℝ)|^271 ≤ (8246319189861/25000000000000 : ℝ)^207
        have hw : |(4286223247/10000000000 : ℝ)|=(4286223247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(148883413/400000000 : ℝ)|^271 ≤ (13710477612999/50000000000000 : ℝ)^207
        have hw : |(148883413/400000000 : ℝ)|=(148883413/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(985558089/2000000000 : ℝ)|^271 ≤ (1979688399857/5000000000000 : ℝ)^207
        have hw : |(985558089/2000000000 : ℝ)|=(985558089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s1_4 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1969619039/10000000000 : ℝ)*x 0 + (5065794761/10000000000 : ℝ)*x 1 + (1405033583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1969619039/10000000000 : ℝ)^271 ≤ (11918462076389/100000000000000 : ℝ)^207 := by
    have hnat : (1969619039 : ℕ)^271*100000000000000^207 ≤ 11918462076389^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969619039 10000000000 11918462076389 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5065794761/10000000000 : ℝ)^271 ≤ (20525838517141/50000000000000 : ℝ)^207 := by
    have hnat : (5065794761 : ℕ)^271*50000000000000^207 ≤ 20525838517141^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5065794761 10000000000 20525838517141 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1405033583/2500000000 : ℝ)^271 ≤ (47029860875731/100000000000000 : ℝ)^207 := by
    have hnat : (1405033583 : ℕ)^271*100000000000000^207 ≤ 47029860875731^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405033583 2500000000 47029860875731 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1969619039/10000000000 : ℝ), (5065794761/10000000000 : ℝ), (1405033583/2500000000 : ℝ)] ![(11918462076389/100000000000000 : ℝ), (20525838517141/50000000000000 : ℝ), (47029860875731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1969619039/10000000000 : ℝ)|^271 ≤ (11918462076389/100000000000000 : ℝ)^207
        have hw : |(-1969619039/10000000000 : ℝ)|=(1969619039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5065794761/10000000000 : ℝ)|^271 ≤ (20525838517141/50000000000000 : ℝ)^207
        have hw : |(5065794761/10000000000 : ℝ)|=(5065794761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1405033583/2500000000 : ℝ)|^271 ≤ (47029860875731/100000000000000 : ℝ)^207
        have hw : |(1405033583/2500000000 : ℝ)|=(1405033583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s1_5 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (210172073/400000000 : ℝ)*x 0 + (-855141/5000000 : ℝ)*x 1 + (5620134431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210172073/400000000 : ℝ)^271 ≤ (4306299192319/10000000000000 : ℝ)^207 := by
    have hnat : (210172073 : ℕ)^271*10000000000000^207 ≤ 4306299192319^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210172073 400000000 4306299192319 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (855141/5000000 : ℝ)^271 ≤ (9907146098549/100000000000000 : ℝ)^207 := by
    have hnat : (855141 : ℕ)^271*100000000000000^207 ≤ 9907146098549^207*5000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855141 5000000 9907146098549 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5620134431/10000000000 : ℝ)^271 ≤ (4702986196031/10000000000000 : ℝ)^207 := by
    have hnat : (5620134431 : ℕ)^271*10000000000000^207 ≤ 4702986196031^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620134431 10000000000 4702986196031 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210172073/400000000 : ℝ), (-855141/5000000 : ℝ), (5620134431/10000000000 : ℝ)] ![(4306299192319/10000000000000 : ℝ), (9907146098549/100000000000000 : ℝ), (4702986196031/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210172073/400000000 : ℝ)|^271 ≤ (4306299192319/10000000000000 : ℝ)^207
        have hw : |(210172073/400000000 : ℝ)|=(210172073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-855141/5000000 : ℝ)|^271 ≤ (9907146098549/100000000000000 : ℝ)^207
        have hw : |(-855141/5000000 : ℝ)|=(855141/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5620134431/10000000000 : ℝ)|^271 ≤ (4702986196031/10000000000000 : ℝ)^207
        have hw : |(5620134431/10000000000 : ℝ)|=(5620134431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s1_6 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5254301721/10000000000 : ℝ)*x 0 + (281006727/500000000 : ℝ)*x 1 + (-171028199/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254301721/10000000000 : ℝ)^271 ≤ (430629908073/1000000000000 : ℝ)^207 := by
    have hnat : (5254301721 : ℕ)^271*1000000000000^207 ≤ 430629908073^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254301721 10000000000 430629908073 1000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281006727/500000000 : ℝ)^271 ≤ (23514931577221/50000000000000 : ℝ)^207 := by
    have hnat : (281006727 : ℕ)^271*50000000000000^207 ≤ 23514931577221^207*500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281006727 500000000 23514931577221 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171028199/1000000000 : ℝ)^271 ≤ (1238393252839/12500000000000 : ℝ)^207 := by
    have hnat : (171028199 : ℕ)^271*12500000000000^207 ≤ 1238393252839^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171028199 1000000000 1238393252839 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254301721/10000000000 : ℝ), (281006727/500000000 : ℝ), (-171028199/1000000000 : ℝ)] ![(430629908073/1000000000000 : ℝ), (23514931577221/50000000000000 : ℝ), (1238393252839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254301721/10000000000 : ℝ)|^271 ≤ (430629908073/1000000000000 : ℝ)^207
        have hw : |(5254301721/10000000000 : ℝ)|=(5254301721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281006727/500000000 : ℝ)|^271 ≤ (23514931577221/50000000000000 : ℝ)^207
        have hw : |(281006727/500000000 : ℝ)|=(281006727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-171028199/1000000000 : ℝ)|^271 ≤ (1238393252839/12500000000000 : ℝ)^207
        have hw : |(-171028199/1000000000 : ℝ)|=(171028199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s1_7 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2143618549/5000000000 : ℝ)*x 0 + (2456527577/5000000000 : ℝ)*x 1 + (46713503/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143618549/5000000000 : ℝ)^271 ≤ (16497745831887/50000000000000 : ℝ)^207 := by
    have hnat : (2143618549 : ℕ)^271*50000000000000^207 ≤ 16497745831887^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143618549 5000000000 16497745831887 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2456527577/5000000000 : ℝ)^271 ≤ (39438839494523/100000000000000 : ℝ)^207 := by
    have hnat : (2456527577 : ℕ)^271*100000000000000^207 ≤ 39438839494523^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2456527577 5000000000 39438839494523 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46713503/125000000 : ℝ)^271 ≤ (430713575397/1562500000000 : ℝ)^207 := by
    have hnat : (46713503 : ℕ)^271*1562500000000^207 ≤ 430713575397^207*125000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46713503 125000000 430713575397 1562500000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143618549/5000000000 : ℝ), (2456527577/5000000000 : ℝ), (46713503/125000000 : ℝ)] ![(16497745831887/50000000000000 : ℝ), (39438839494523/100000000000000 : ℝ), (430713575397/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143618549/5000000000 : ℝ)|^271 ≤ (16497745831887/50000000000000 : ℝ)^207
        have hw : |(2143618549/5000000000 : ℝ)|=(2143618549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2456527577/5000000000 : ℝ)|^271 ≤ (39438839494523/100000000000000 : ℝ)^207
        have hw : |(2456527577/5000000000 : ℝ)|=(2456527577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46713503/125000000 : ℝ)|^271 ≤ (430713575397/1562500000000 : ℝ)^207
        have hw : |(46713503/125000000 : ℝ)|=(46713503/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1376_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6657/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (833/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7199/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4803/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6657/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (833/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6657/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (833/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6657/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (833/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6657/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (833/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6657/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (833/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6657/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (833/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (833/50000 : ℝ) ^ (4335/1024 : ℝ) ≤ (2962386440831/100000000000000000000 : ℝ) := by
    have hpowers : (833/50000 : ℝ)^4335 ≤ (2962386440831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (833 : ℕ)^4335*100000000000000000000^1024 ≤ 2962386440831^1024*50000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        833 50000 2962386440831 100000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (833/50000 : ℝ)) (X := (2962386440831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6657/25000 : ℝ) ^ (4335/1024 : ℝ) ≤ (73834460155271073/20000000000000000000 : ℝ) := by
    have hpowers : (6657/25000 : ℝ)^4335 ≤ (73834460155271073/20000000000000000000 : ℝ)^1024 := by
      have hnat : (6657 : ℕ)^4335*20000000000000000000^1024 ≤ 73834460155271073^1024*25000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6657 25000 73834460155271073 20000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6657/25000 : ℝ)) (X := (73834460155271073/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000002962386440831/50000000000000000000 : ℝ) ≤ (1000000013995311/1000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (50000002962386440831/50000000000000000000 : ℝ)^1024 ≤ (1000000013995311/1000000000000000 : ℝ)^4335 := by
      have hnat : (50000002962386440831 : ℕ)^1024*1000000000000000^4335 ≤ 1000000013995311^4335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000002962386440831 50000000000000000000 1000000013995311 1000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000013995311/1000000000000000 : ℝ)) (X := (50000002962386440831/50000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25092293815790699049/25000000000000000000 : ℝ) ≤ (1000870827336387/1000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (25092293815790699049/25000000000000000000 : ℝ)^1024 ≤ (1000870827336387/1000000000000000 : ℝ)^4335 := by
      have hnat : (25092293815790699049 : ℕ)^1024*1000000000000000^4335 ≤ 1000870827336387^4335*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25092293815790699049 25000000000000000000 1000870827336387 1000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000870827336387/1000000000000000 : ℝ)) (X := (25092293815790699049/25000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10073834460155271073/10000000000000000000 : ℝ) ≤ (1001741640677463/1000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (10073834460155271073/10000000000000000000 : ℝ)^1024 ≤ (1001741640677463/1000000000000000 : ℝ)^4335 := by
      have hnat : (10073834460155271073 : ℕ)^1024*1000000000000000^4335 ≤ 1001741640677463^4335*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10073834460155271073 10000000000000000000 1001741640677463 1000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001741640677463/1000000000000000 : ℝ)) (X := (10073834460155271073/10000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2962386440831/100000000000000000000 : ℝ) ≤ ((71311710855138537/71320000000000000 : ℝ)+2*(31100476467/8915000000000 : ℝ)*(833/50000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (71311710855138537/71320000000000000 : ℝ)+2*(31100476467/8915000000000 : ℝ)*(833/50000 : ℝ)=(1000000013995311/1000000000000000 : ℝ) by norm_num, show 1+2*(2962386440831/100000000000000000000 : ℝ)=(50000002962386440831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73834460155271073/20000000000000000000 : ℝ)+(2962386440831/100000000000000000000 : ℝ) ≤ ((71311710855138537/71320000000000000 : ℝ)+(31100476467/8915000000000 : ℝ)*((6657/25000 : ℝ)+(833/50000 : ℝ)))^(4335/1024 : ℝ) := by
    rw [show (71311710855138537/71320000000000000 : ℝ)+(31100476467/8915000000000 : ℝ)*((6657/25000 : ℝ)+(833/50000 : ℝ))=(1000870827336387/1000000000000000 : ℝ) by norm_num, show 1+(73834460155271073/20000000000000000000 : ℝ)+(2962386440831/100000000000000000000 : ℝ)=(25092293815790699049/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73834460155271073/20000000000000000000 : ℝ) ≤ ((71311710855138537/71320000000000000 : ℝ)+2*(31100476467/8915000000000 : ℝ)*(6657/25000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (71311710855138537/71320000000000000 : ℝ)+2*(31100476467/8915000000000 : ℝ)*(6657/25000 : ℝ)=(1001741640677463/1000000000000000 : ℝ) by norm_num, show 1+2*(73834460155271073/20000000000000000000 : ℝ)=(10073834460155271073/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (71311710855138537/71320000000000000 : ℝ)*(X 1 0+X 2 0)+(31100476467/8915000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (833/50000 : ℝ)) (hi := (6657/25000 : ℝ)) (c := (71311710855138537/71320000000000000 : ℝ)) (alpha := (31100476467/8915000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (71311710855138537/71320000000000000 : ℝ)*(X 0 1+X 2 1)+(31100476467/8915000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (833/50000 : ℝ)) (hi := (6657/25000 : ℝ)) (c := (71311710855138537/71320000000000000 : ℝ)) (alpha := (31100476467/8915000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (71311710855138537/71320000000000000 : ℝ)*(X 0 2+X 1 2)+(31100476467/8915000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (833/50000 : ℝ)) (hi := (6657/25000 : ℝ)) (c := (71311710855138537/71320000000000000 : ℝ)) (alpha := (31100476467/8915000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-196914147/1000000000 : ℝ)*X 0 0+(2813602147/5000000000 : ℝ)*X 0 1+(202353913/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((675274079/1250000000 : ℝ)*X 1 0+(-2271567339/10000000000 : ℝ)*X 1 1+(1011769841/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5402193209/10000000000 : ℝ)*X 2 0+(5058848017/10000000000 : ℝ)*X 2 1+(-2271568107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4286223247/10000000000 : ℝ)*X 0 0+(148883413/400000000 : ℝ)*X 0 1+(985558089/2000000000 : ℝ)*X 0 2+(4286223247/10000000000 : ℝ)*X 1 0+(148883413/400000000 : ℝ)*X 1 1+(985558089/2000000000 : ℝ)*X 1 2+(4286223247/10000000000 : ℝ)*X 2 0+(148883413/400000000 : ℝ)*X 2 1+(985558089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1969619039/10000000000 : ℝ)*X 0 0+(5065794761/10000000000 : ℝ)*X 0 1+(1405033583/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210172073/400000000 : ℝ)*X 1 0+(-855141/5000000 : ℝ)*X 1 1+(5620134431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254301721/10000000000 : ℝ)*X 2 0+(281006727/500000000 : ℝ)*X 2 1+(-171028199/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2143618549/5000000000 : ℝ)*X 0 0+(2456527577/5000000000 : ℝ)*X 0 1+(46713503/125000000 : ℝ)*X 0 2+(2143618549/5000000000 : ℝ)*X 1 0+(2456527577/5000000000 : ℝ)*X 1 1+(46713503/125000000 : ℝ)*X 1 2+(2143618549/5000000000 : ℝ)*X 2 0+(2456527577/5000000000 : ℝ)*X 2 1+(46713503/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32653023080577092577/8915000000000000000000000 : ℝ) := by norm_num
    linear_combination (209411989/50000000000000 : ℝ)*(base19) + (63985357/10000000000000 : ℝ)*(base23) + (3950973/10000000000000 : ℝ)*(upper2) + (8475147/20000000000000 : ℝ)*(upper3) + (1294433909251797/100000000000000 : ℝ)*(major0) + (1294433909251797/100000000000000 : ℝ)*(major1) + (1294433909251797/100000000000000 : ℝ)*(major2) + (109966667526503/6250000000000 : ℝ)*(sp0) + (879736759774779/50000000000000 : ℝ)*(sp1) + (1759471836171047/100000000000000 : ℝ)*(sp2) + (207347946588347/25000000000000 : ℝ)*(sp3) + (453621843/6250000000000 : ℝ)*(sp4) + (1462348919/100000000000000 : ℝ)*(sp6) + (197168647/10000000000000 : ℝ)*(sp7) + (414696879019929/50000000000000 : ℝ)*(f.failure) + (54983560574173/3125000000000 : ℝ)*(f.sum) + (1805821790809/445750000000000000000000000 : ℝ)*base66 + (19104356682072989/7132000000000000000000000000000 : ℝ)*base67 + (33839019137239011/7132000000000000000000000000000 : ℝ)*base70 + (16279802311928989/7132000000000000000000000000000 : ℝ)*base71 + (1164840717599/891500000000000000000000000 : ℝ)*base74 + (38926159013407011/7132000000000000000000000000000 : ℝ)*base76 + (6496015183011/7132000000000000000000000000000 : ℝ)*base78 + (28855001860644989/7132000000000000000000000000000 : ℝ)*base79 + (10119166791447/1783000000000000000000000000 : ℝ)*base82 + (146859/39062500000000000000 : ℝ)*base89 + (146859/39062500000000000000 : ℝ)*base91 + (146859/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2985062786399953321784853/445750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33281481/50000000000000 : ℝ)*(base1) + (1343726783/100000000000000 : ℝ)*(base19) + (327713321/25000000000000 : ℝ)*(base23) + (40552247/25000000000000 : ℝ)*(upper3) + (148786513/100000000000000 : ℝ)*(upper5) + (265430672940517/20000000000000 : ℝ)*(major0) + (265430672940517/20000000000000 : ℝ)*(major1) + (663576682351293/50000000000000 : ℝ)*(major2) + (1449441631/20000000000000 : ℝ)*(sp1) + (36739053/500000000000 : ℝ)*(sp2) + (901974098474341/50000000000000 : ℝ)*(sp4) + (1803939539450781/100000000000000 : ℝ)*(sp5) + (450984867930459/25000000000000 : ℝ)*(sp6) + (212589577308123/25000000000000 : ℝ)*(sp7) + (170071675159091/20000000000000 : ℝ)*(f.failure) + (1803948130385719/100000000000000 : ℝ)*(f.sum) + (152859312341/89150000000000000000000000 : ℝ)*base65 + (2881627668265171/1426400000000000000000000000000 : ℝ)*base68 + (2890429759594341/3566000000000000000000000000000 : ℝ)*base69 + (9167428322163571/1426400000000000000000000000000 : ℝ)*base72 + (1928738829621/356600000000000000000000000 : ℝ)*base73 + (20118285833102341/3566000000000000000000000000000 : ℝ)*base75 + (12710451058905171/1426400000000000000000000000000 : ℝ)*base78 + (13509486156655571/1426400000000000000000000000000 : ℝ)*base80 + (154575968543/89150000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (56843/7812500000000000000 : ℝ)*base89 + (56843/7812500000000000000 : ℝ)*base91 + (10641/3906250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1376_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6657/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (833/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7199/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4803/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1376_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1376_s2_0 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-250802097/1250000000 : ℝ)*x 0 + (683849377/1250000000 : ℝ)*x 1 + (2595667299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250802097/1250000000 : ℝ)^271 ≤ (12210813490869/100000000000000 : ℝ)^207 := by
    have hnat : (250802097 : ℕ)^271*100000000000000^207 ≤ 12210813490869^207*1250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250802097 1250000000 12210813490869 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683849377/1250000000 : ℝ)^271 ≤ (11350139939897/25000000000000 : ℝ)^207 := by
    have hnat : (683849377 : ℕ)^271*25000000000000^207 ≤ 11350139939897^207*1250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683849377 1250000000 11350139939897 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2595667299/5000000000 : ℝ)^271 ≤ (42388626730861/100000000000000 : ℝ)^207 := by
    have hnat : (2595667299 : ℕ)^271*100000000000000^207 ≤ 42388626730861^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595667299 5000000000 42388626730861 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-250802097/1250000000 : ℝ), (683849377/1250000000 : ℝ), (2595667299/5000000000 : ℝ)] ![(12210813490869/100000000000000 : ℝ), (11350139939897/25000000000000 : ℝ), (42388626730861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-250802097/1250000000 : ℝ)|^271 ≤ (12210813490869/100000000000000 : ℝ)^207
        have hw : |(-250802097/1250000000 : ℝ)|=(250802097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683849377/1250000000 : ℝ)|^271 ≤ (11350139939897/25000000000000 : ℝ)^207
        have hw : |(683849377/1250000000 : ℝ)|=(683849377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2595667299/5000000000 : ℝ)|^271 ≤ (42388626730861/100000000000000 : ℝ)^207
        have hw : |(2595667299/5000000000 : ℝ)|=(2595667299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s2_1 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5363607659/10000000000 : ℝ)*x 0 + (-537639413/2500000000 : ℝ)*x 1 + (2595667347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363607659/10000000000 : ℝ)^271 ≤ (44239566024213/100000000000000 : ℝ)^207 := by
    have hnat : (5363607659 : ℕ)^271*100000000000000^207 ≤ 44239566024213^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363607659 10000000000 44239566024213 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537639413/2500000000 : ℝ)^271 ≤ (13371806204413/100000000000000 : ℝ)^207 := by
    have hnat : (537639413 : ℕ)^271*100000000000000^207 ≤ 13371806204413^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537639413 2500000000 13371806204413 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2595667347/5000000000 : ℝ)^271 ≤ (42388627757081/100000000000000 : ℝ)^207 := by
    have hnat : (2595667347 : ℕ)^271*100000000000000^207 ≤ 42388627757081^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595667347 5000000000 42388627757081 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363607659/10000000000 : ℝ), (-537639413/2500000000 : ℝ), (2595667347/5000000000 : ℝ)] ![(44239566024213/100000000000000 : ℝ), (13371806204413/100000000000000 : ℝ), (42388627757081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363607659/10000000000 : ℝ)|^271 ≤ (44239566024213/100000000000000 : ℝ)^207
        have hw : |(5363607659/10000000000 : ℝ)|=(5363607659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537639413/2500000000 : ℝ)|^271 ≤ (13371806204413/100000000000000 : ℝ)^207
        have hw : |(-537639413/2500000000 : ℝ)|=(537639413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2595667347/5000000000 : ℝ)|^271 ≤ (42388627757081/100000000000000 : ℝ)^207
        have hw : |(2595667347/5000000000 : ℝ)|=(2595667347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s2_2 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2681803801/5000000000 : ℝ)*x 0 + (5191334739/10000000000 : ℝ)*x 1 + (-537639417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681803801/5000000000 : ℝ)^271 ≤ (22119782704357/50000000000000 : ℝ)^207 := by
    have hnat : (2681803801 : ℕ)^271*50000000000000^207 ≤ 22119782704357^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681803801 5000000000 22119782704357 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5191334739/10000000000 : ℝ)^271 ≤ (21194314119061/50000000000000 : ℝ)^207 := by
    have hnat : (5191334739 : ℕ)^271*50000000000000^207 ≤ 21194314119061^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191334739 10000000000 21194314119061 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537639417/2500000000 : ℝ)^271 ≤ (13371806334657/100000000000000 : ℝ)^207 := by
    have hnat : (537639417 : ℕ)^271*100000000000000^207 ≤ 13371806334657^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537639417 2500000000 13371806334657 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681803801/5000000000 : ℝ), (5191334739/10000000000 : ℝ), (-537639417/2500000000 : ℝ)] ![(22119782704357/50000000000000 : ℝ), (21194314119061/50000000000000 : ℝ), (13371806334657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681803801/5000000000 : ℝ)|^271 ≤ (22119782704357/50000000000000 : ℝ)^207
        have hw : |(2681803801/5000000000 : ℝ)|=(2681803801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5191334739/10000000000 : ℝ)|^271 ≤ (21194314119061/50000000000000 : ℝ)^207
        have hw : |(5191334739/10000000000 : ℝ)|=(5191334739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537639417/2500000000 : ℝ)|^271 ≤ (13371806334657/100000000000000 : ℝ)^207
        have hw : |(-537639417/2500000000 : ℝ)|=(537639417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s2_3 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2156195891/5000000000 : ℝ)*x 0 + (2012662737/5000000000 : ℝ)*x 1 + (230908593/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156195891/5000000000 : ℝ)^271 ≤ (33249172769527/100000000000000 : ℝ)^207 := by
    have hnat : (2156195891 : ℕ)^271*100000000000000^207 ≤ 33249172769527^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156195891 5000000000 33249172769527 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012662737/5000000000 : ℝ)^271 ≤ (30381825973007/100000000000000 : ℝ)^207 := by
    have hnat : (2012662737 : ℕ)^271*100000000000000^207 ≤ 30381825973007^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012662737 5000000000 30381825973007 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230908593/500000000 : ℝ)^271 ≤ (36369001242857/100000000000000 : ℝ)^207 := by
    have hnat : (230908593 : ℕ)^271*100000000000000^207 ≤ 36369001242857^207*500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230908593 500000000 36369001242857 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156195891/5000000000 : ℝ), (2012662737/5000000000 : ℝ), (230908593/500000000 : ℝ)] ![(33249172769527/100000000000000 : ℝ), (30381825973007/100000000000000 : ℝ), (36369001242857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156195891/5000000000 : ℝ)|^271 ≤ (33249172769527/100000000000000 : ℝ)^207
        have hw : |(2156195891/5000000000 : ℝ)|=(2156195891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012662737/5000000000 : ℝ)|^271 ≤ (30381825973007/100000000000000 : ℝ)^207
        have hw : |(2012662737/5000000000 : ℝ)|=(2012662737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230908593/500000000 : ℝ)|^271 ≤ (36369001242857/100000000000000 : ℝ)^207
        have hw : |(230908593/500000000 : ℝ)|=(230908593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s2_4 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2006473399/10000000000 : ℝ)*x 0 + (324564001/625000000 : ℝ)*x 1 + (2734545537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2006473399/10000000000 : ℝ)^271 ≤ (12211264636923/100000000000000 : ℝ)^207 := by
    have hnat : (2006473399 : ℕ)^271*100000000000000^207 ≤ 12211264636923^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006473399 10000000000 12211264636923 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324564001/625000000 : ℝ)^271 ≤ (2120334358351/5000000000000 : ℝ)^207 := by
    have hnat : (324564001 : ℕ)^271*5000000000000^207 ≤ 2120334358351^207*625000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324564001 625000000 2120334358351 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734545537/5000000000 : ℝ)^271 ≤ (88636812841/195312500000 : ℝ)^207 := by
    have hnat : (2734545537 : ℕ)^271*195312500000^207 ≤ 88636812841^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734545537 5000000000 88636812841 195312500000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2006473399/10000000000 : ℝ), (324564001/625000000 : ℝ), (2734545537/5000000000 : ℝ)] ![(12211264636923/100000000000000 : ℝ), (2120334358351/5000000000000 : ℝ), (88636812841/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2006473399/10000000000 : ℝ)|^271 ≤ (12211264636923/100000000000000 : ℝ)^207
        have hw : |(-2006473399/10000000000 : ℝ)|=(2006473399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324564001/625000000 : ℝ)|^271 ≤ (2120334358351/5000000000000 : ℝ)^207
        have hw : |(324564001/625000000 : ℝ)|=(324564001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734545537/5000000000 : ℝ)|^271 ≤ (88636812841/195312500000 : ℝ)^207
        have hw : |(2734545537/5000000000 : ℝ)|=(2734545537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s2_5 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (132282927/250000000 : ℝ)*x 0 + (-23410023/125000000 : ℝ)*x 1 + (5469090779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132282927/250000000 : ℝ)^271 ≤ (10865146709023/25000000000000 : ℝ)^207 := by
    have hnat : (132282927 : ℕ)^271*25000000000000^207 ≤ 10865146709023^207*250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132282927 250000000 10865146709023 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23410023/125000000 : ℝ)^271 ≤ (11157368175433/100000000000000 : ℝ)^207 := by
    have hnat : (23410023 : ℕ)^271*100000000000000^207 ≤ 11157368175433^207*125000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23410023 125000000 11157368175433 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469090779/10000000000 : ℝ)^271 ≤ (45382044969873/100000000000000 : ℝ)^207 := by
    have hnat : (5469090779 : ℕ)^271*100000000000000^207 ≤ 45382044969873^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469090779 10000000000 45382044969873 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132282927/250000000 : ℝ), (-23410023/125000000 : ℝ), (5469090779/10000000000 : ℝ)] ![(10865146709023/25000000000000 : ℝ), (11157368175433/100000000000000 : ℝ), (45382044969873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132282927/250000000 : ℝ)|^271 ≤ (10865146709023/25000000000000 : ℝ)^207
        have hw : |(132282927/250000000 : ℝ)|=(132282927/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23410023/125000000 : ℝ)|^271 ≤ (11157368175433/100000000000000 : ℝ)^207
        have hw : |(-23410023/125000000 : ℝ)|=(23410023/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469090779/10000000000 : ℝ)|^271 ≤ (45382044969873/100000000000000 : ℝ)^207
        have hw : |(5469090779/10000000000 : ℝ)|=(5469090779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s2_6 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5291318567/10000000000 : ℝ)*x 0 + (341818181/625000000 : ℝ)*x 1 + (-468199907/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291318567/10000000000 : ℝ)^271 ≤ (10865150706461/25000000000000 : ℝ)^207 := by
    have hnat : (5291318567 : ℕ)^271*25000000000000^207 ≤ 10865150706461^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291318567 10000000000 10865150706461 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341818181/625000000 : ℝ)^271 ≤ (45382046240897/100000000000000 : ℝ)^207 := by
    have hnat : (341818181 : ℕ)^271*100000000000000^207 ≤ 45382046240897^207*625000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341818181 625000000 45382046240897 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468199907/2500000000 : ℝ)^271 ≤ (5578675461429/50000000000000 : ℝ)^207 := by
    have hnat : (468199907 : ℕ)^271*50000000000000^207 ≤ 5578675461429^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468199907 2500000000 5578675461429 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291318567/10000000000 : ℝ), (341818181/625000000 : ℝ), (-468199907/2500000000 : ℝ)] ![(10865150706461/25000000000000 : ℝ), (45382046240897/100000000000000 : ℝ), (5578675461429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291318567/10000000000 : ℝ)|^271 ≤ (10865150706461/25000000000000 : ℝ)^207
        have hw : |(5291318567/10000000000 : ℝ)|=(5291318567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341818181/625000000 : ℝ)|^271 ≤ (45382046240897/100000000000000 : ℝ)^207
        have hw : |(341818181/625000000 : ℝ)|=(341818181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468199907/2500000000 : ℝ)|^271 ≤ (5578675461429/50000000000000 : ℝ)^207
        have hw : |(-468199907/2500000000 : ℝ)|=(468199907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s2_7 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4312513629/10000000000 : ℝ)*x 0 + (2307294341/5000000000 : ℝ)*x 1 + (4028938721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312513629/10000000000 : ℝ)^271 ≤ (16625201346823/50000000000000 : ℝ)^207 := by
    have hnat : (4312513629 : ℕ)^271*50000000000000^207 ≤ 16625201346823^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312513629 10000000000 16625201346823 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2307294341/5000000000 : ℝ)^271 ≤ (36332062976461/100000000000000 : ℝ)^207 := by
    have hnat : (2307294341 : ℕ)^271*100000000000000^207 ≤ 36332062976461^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307294341 5000000000 36332062976461 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028938721/10000000000 : ℝ)^271 ≤ (30417534317341/100000000000000 : ℝ)^207 := by
    have hnat : (4028938721 : ℕ)^271*100000000000000^207 ≤ 30417534317341^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028938721 10000000000 30417534317341 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312513629/10000000000 : ℝ), (2307294341/5000000000 : ℝ), (4028938721/10000000000 : ℝ)] ![(16625201346823/50000000000000 : ℝ), (36332062976461/100000000000000 : ℝ), (30417534317341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312513629/10000000000 : ℝ)|^271 ≤ (16625201346823/50000000000000 : ℝ)^207
        have hw : |(4312513629/10000000000 : ℝ)|=(4312513629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2307294341/5000000000 : ℝ)|^271 ≤ (36332062976461/100000000000000 : ℝ)^207
        have hw : |(2307294341/5000000000 : ℝ)|=(2307294341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028938721/10000000000 : ℝ)|^271 ≤ (30417534317341/100000000000000 : ℝ)^207
        have hw : |(4028938721/10000000000 : ℝ)|=(4028938721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1376_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4803/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5033/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1997/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4803/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4803/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4803/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4803/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4803/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4803/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7199/100000 : ℝ) ^ (4335/1024 : ℝ) ≤ (1453375400258973/100000000000000000000 : ℝ) := by
    have hpowers : (7199/100000 : ℝ)^4335 ≤ (1453375400258973/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7199 : ℕ)^4335*100000000000000000000^1024 ≤ 1453375400258973^1024*100000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7199 100000 1453375400258973 100000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7199/100000 : ℝ)) (X := (1453375400258973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4803/25000 : ℝ) ^ (4335/1024 : ℝ) ≤ (9269947424056619/10000000000000000000 : ℝ) := by
    have hpowers : (4803/25000 : ℝ)^4335 ≤ (9269947424056619/10000000000000000000 : ℝ)^1024 := by
      have hnat : (4803 : ℕ)^4335*10000000000000000000^1024 ≤ 9269947424056619^1024*25000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4803 25000 9269947424056619 10000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4803/25000 : ℝ)) (X := (9269947424056619/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001453375400258973/50000000000000000000 : ℝ) ≤ (50000343307933/50000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (50001453375400258973/50000000000000000000 : ℝ)^1024 ≤ (50000343307933/50000000000000 : ℝ)^4335 := by
      have hnat : (50001453375400258973 : ℕ)^1024*50000000000000^4335 ≤ 50000343307933^4335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001453375400258973 50000000000000000000 50000343307933 50000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50000343307933/50000000000000 : ℝ)) (X := (50001453375400258973/50000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100094152849640825163/100000000000000000000 : ℝ) ≤ (1000222324961823/1000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (100094152849640825163/100000000000000000000 : ℝ)^1024 ≤ (1000222324961823/1000000000000000 : ℝ)^4335 := by
      have hnat : (100094152849640825163 : ℕ)^1024*1000000000000000^4335 ≤ 1000222324961823^4335*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100094152849640825163 100000000000000000000 1000222324961823 1000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000222324961823/1000000000000000 : ℝ)) (X := (100094152849640825163/100000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5009269947424056619/5000000000000000000 : ℝ) ≤ (500218891882493/500000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (5009269947424056619/5000000000000000000 : ℝ)^1024 ≤ (500218891882493/500000000000000 : ℝ)^4335 := by
      have hnat : (5009269947424056619 : ℕ)^1024*500000000000000^4335 ≤ 500218891882493^4335*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5009269947424056619 5000000000000000000 500218891882493 500000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500218891882493/500000000000000 : ℝ)) (X := (5009269947424056619/5000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1453375400258973/100000000000000000000 : ℝ) ≤ ((6004990153658020853/6006500000000000000 : ℝ)+2*(215458803163/120130000000000 : ℝ)*(7199/100000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (6004990153658020853/6006500000000000000 : ℝ)+2*(215458803163/120130000000000 : ℝ)*(7199/100000 : ℝ)=(50000343307933/50000000000000 : ℝ) by norm_num, show 1+2*(1453375400258973/100000000000000000000 : ℝ)=(50001453375400258973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9269947424056619/10000000000000000000 : ℝ)+(1453375400258973/100000000000000000000 : ℝ) ≤ ((6004990153658020853/6006500000000000000 : ℝ)+(215458803163/120130000000000 : ℝ)*((4803/25000 : ℝ)+(7199/100000 : ℝ)))^(4335/1024 : ℝ) := by
    rw [show (6004990153658020853/6006500000000000000 : ℝ)+(215458803163/120130000000000 : ℝ)*((4803/25000 : ℝ)+(7199/100000 : ℝ))=(1000222324961823/1000000000000000 : ℝ) by norm_num, show 1+(9269947424056619/10000000000000000000 : ℝ)+(1453375400258973/100000000000000000000 : ℝ)=(100094152849640825163/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9269947424056619/10000000000000000000 : ℝ) ≤ ((6004990153658020853/6006500000000000000 : ℝ)+2*(215458803163/120130000000000 : ℝ)*(4803/25000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (6004990153658020853/6006500000000000000 : ℝ)+2*(215458803163/120130000000000 : ℝ)*(4803/25000 : ℝ)=(500218891882493/500000000000000 : ℝ) by norm_num, show 1+2*(9269947424056619/10000000000000000000 : ℝ)=(5009269947424056619/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6004990153658020853/6006500000000000000 : ℝ)*(X 1 0+X 2 0)+(215458803163/120130000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (7199/100000 : ℝ)) (hi := (4803/25000 : ℝ)) (c := (6004990153658020853/6006500000000000000 : ℝ)) (alpha := (215458803163/120130000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6004990153658020853/6006500000000000000 : ℝ)*(X 0 1+X 2 1)+(215458803163/120130000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (7199/100000 : ℝ)) (hi := (4803/25000 : ℝ)) (c := (6004990153658020853/6006500000000000000 : ℝ)) (alpha := (215458803163/120130000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6004990153658020853/6006500000000000000 : ℝ)*(X 0 2+X 1 2)+(215458803163/120130000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (7199/100000 : ℝ)) (hi := (4803/25000 : ℝ)) (c := (6004990153658020853/6006500000000000000 : ℝ)) (alpha := (215458803163/120130000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-250802097/1250000000 : ℝ)*X 0 0+(683849377/1250000000 : ℝ)*X 0 1+(2595667299/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363607659/10000000000 : ℝ)*X 1 0+(-537639413/2500000000 : ℝ)*X 1 1+(2595667347/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681803801/5000000000 : ℝ)*X 2 0+(5191334739/10000000000 : ℝ)*X 2 1+(-537639417/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156195891/5000000000 : ℝ)*X 0 0+(2012662737/5000000000 : ℝ)*X 0 1+(230908593/500000000 : ℝ)*X 0 2+(2156195891/5000000000 : ℝ)*X 1 0+(2012662737/5000000000 : ℝ)*X 1 1+(230908593/500000000 : ℝ)*X 1 2+(2156195891/5000000000 : ℝ)*X 2 0+(2012662737/5000000000 : ℝ)*X 2 1+(230908593/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2006473399/10000000000 : ℝ)*X 0 0+(324564001/625000000 : ℝ)*X 0 1+(2734545537/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132282927/250000000 : ℝ)*X 1 0+(-23410023/125000000 : ℝ)*X 1 1+(5469090779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5291318567/10000000000 : ℝ)*X 2 0+(341818181/625000000 : ℝ)*X 2 1+(-468199907/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312513629/10000000000 : ℝ)*X 0 0+(2307294341/5000000000 : ℝ)*X 0 1+(4028938721/10000000000 : ℝ)*X 0 2+(4312513629/10000000000 : ℝ)*X 1 0+(2307294341/5000000000 : ℝ)*X 1 1+(4028938721/10000000000 : ℝ)*X 1 2+(4312513629/10000000000 : ℝ)*X 2 0+(2307294341/5000000000 : ℝ)*X 2 1+(4028938721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1885046441315387863861478943/300325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1056457153/100000000000000 : ℝ)*(base19) + (94287231/10000000000000 : ℝ)*(base23) + (40525847/100000000000000 : ℝ)*(lower2) + (33389883/20000000000000 : ℝ)*(upper3) + (85561649/100000000000000 : ℝ)*(upper5) + (2632571533945411/100000000000000 : ℝ)*(major0) + (2632571533945411/100000000000000 : ℝ)*(major1) + (658142883486353/25000000000000 : ℝ)*(major2) + (1789169584750033/50000000000000 : ℝ)*(sp0) + (894587907278763/25000000000000 : ℝ)*(sp1) + (1789175871349947/50000000000000 : ℝ)*(sp2) + (1686783409889839/100000000000000 : ℝ)*(sp3) + (13516072139/100000000000000 : ℝ)*(sp4) + (6763205827/100000000000000 : ℝ)*(sp7) + (843395086547833/50000000000000 : ℝ)*(f.failure) + (894588171393051/25000000000000 : ℝ)*(f.sum) + (9801617735703/12013000000000000000000000000 : ℝ)*base66 + (2194142479222455583/600650000000000000000000000000000 : ℝ)*base67 + (919405800261169109/150162500000000000000000000000000 : ℝ)*base69 + (3894202676652605583/600650000000000000000000000000000 : ℝ)*base71 + (30687607820801/12013000000000000000000000000 : ℝ)*base73 + (914729239369394109/150162500000000000000000000000000 : ℝ)*base75 + (1620693162603544417/600650000000000000000000000000000 : ℝ)*base78 + (2619527700813405583/600650000000000000000000000000000 : ℝ)*base79 + (31742646071991/12013000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (413693/39062500000000000000 : ℝ)*base89 + (413693/39062500000000000000 : ℝ)*base91 + (5767/9765625000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1258192834903014163736956677/150162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199653871/12500000000000 : ℝ)*(base19) + (243111387/6250000000000 : ℝ)*(base23) + (183704389/50000000000000 : ℝ)*(upper3) + (174733047/50000000000000 : ℝ)*(lower4) + (106672193/100000000000000 : ℝ)*(upper5) + (2664906978996497/100000000000000 : ℝ)*(major0) + (2664906978996497/100000000000000 : ℝ)*(major1) + (2664906978996497/100000000000000 : ℝ)*(major2) + (8979968103/100000000000000 : ℝ)*(sp1) + (13483234149/25000000000000 : ℝ)*(sp2) + (1811152469063997/50000000000000 : ℝ)*(sp4) + (1811147180464461/50000000000000 : ℝ)*(sp5) + (1811123557704603/50000000000000 : ℝ)*(sp6) + (1707508740569159/100000000000000 : ℝ)*(sp7) + (1707508740569159/100000000000000 : ℝ)*(f.failure) + (1811152469063997/50000000000000 : ℝ)*(f.sum) + (28884880193243/12013000000000000000000000000 : ℝ)*base66 + (1537927564318201941/600650000000000000000000000000000 : ℝ)*base67 + (2488474897763751941/600650000000000000000000000000000 : ℝ)*base69 + (1606585279419301941/600650000000000000000000000000000 : ℝ)*base71 + (8035495983649/3003250000000000000000000000 : ℝ)*base73 + (5463524281757151941/600650000000000000000000000000000 : ℝ)*base75 + (513133772052748059/600650000000000000000000000000000 : ℝ)*base78 + (1523215774192801941/600650000000000000000000000000000 : ℝ)*base79 + (3106030266163/12013000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5407/39062500000000000000 : ℝ)*base89 + (5407/39062500000000000000 : ℝ)*base91 + (5407/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1376_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4803/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5033/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1997/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1376_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1376_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5033/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1997/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1376_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1376_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1376_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5033/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1997/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1376_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

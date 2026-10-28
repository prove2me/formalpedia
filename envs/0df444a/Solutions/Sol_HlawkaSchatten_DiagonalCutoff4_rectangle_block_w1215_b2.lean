-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1215_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:54.092783+00:00
-- url     : https://prove2.me/submissions/db88f5c7-497f-4c4e-ae1d-59b2a6316375

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
theorem support_rectangle_w1215_s6_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066218397/5000000000 : ℝ)*x 0 + (26959629/50000000 : ℝ)*x 1 + (21066521/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066218397/5000000000 : ℝ)^1051 ≤ (2592960178899/20000000000000 : ℝ)^795 := by
    have hnat : (1066218397 : ℕ)^1051*20000000000000^795 ≤ 2592960178899^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066218397 5000000000 2592960178899 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26959629/50000000 : ℝ)^1051 ≤ (4419387377207/10000000000000 : ℝ)^795 := by
    have hnat : (26959629 : ℕ)^1051*10000000000000^795 ≤ 4419387377207^795*50000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26959629 50000000 4419387377207 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21066521/40000000 : ℝ)^1051 ≤ (42841325325637/100000000000000 : ℝ)^795 := by
    have hnat : (21066521 : ℕ)^1051*100000000000000^795 ≤ 42841325325637^795*40000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21066521 40000000 42841325325637 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066218397/5000000000 : ℝ), (26959629/50000000 : ℝ), (21066521/40000000 : ℝ)] ![(2592960178899/20000000000000 : ℝ), (4419387377207/10000000000000 : ℝ), (42841325325637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066218397/5000000000 : ℝ)|^1051 ≤ (2592960178899/20000000000000 : ℝ)^795
        have hw : |(-1066218397/5000000000 : ℝ)|=(1066218397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26959629/50000000 : ℝ)|^1051 ≤ (4419387377207/10000000000000 : ℝ)^795
        have hw : |(26959629/50000000 : ℝ)|=(26959629/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21066521/40000000 : ℝ)|^1051 ≤ (42841325325637/100000000000000 : ℝ)^795
        have hw : |(21066521/40000000 : ℝ)|=(21066521/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s6_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672251781/5000000000 : ℝ)*x 0 + (-2195974737/10000000000 : ℝ)*x 1 + (2633314907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672251781/5000000000 : ℝ)^1051 ≤ (21840376765629/50000000000000 : ℝ)^795 := by
    have hnat : (2672251781 : ℕ)^1051*50000000000000^795 ≤ 21840376765629^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672251781 5000000000 21840376765629 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195974737/10000000000 : ℝ)^1051 ≤ (13477925812097/100000000000000 : ℝ)^795 := by
    have hnat : (2195974737 : ℕ)^1051*100000000000000^795 ≤ 13477925812097^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195974737 10000000000 13477925812097 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633314907/5000000000 : ℝ)^1051 ≤ (2142066031847/5000000000000 : ℝ)^795 := by
    have hnat : (2633314907 : ℕ)^1051*5000000000000^795 ≤ 2142066031847^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633314907 5000000000 2142066031847 5000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672251781/5000000000 : ℝ), (-2195974737/10000000000 : ℝ), (2633314907/5000000000 : ℝ)] ![(21840376765629/50000000000000 : ℝ), (13477925812097/100000000000000 : ℝ), (2142066031847/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672251781/5000000000 : ℝ)|^1051 ≤ (21840376765629/50000000000000 : ℝ)^795
        have hw : |(2672251781/5000000000 : ℝ)|=(2672251781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195974737/10000000000 : ℝ)|^1051 ≤ (13477925812097/100000000000000 : ℝ)^795
        have hw : |(-2195974737/10000000000 : ℝ)|=(2195974737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633314907/5000000000 : ℝ)|^1051 ≤ (2142066031847/5000000000000 : ℝ)^795
        have hw : |(2633314907/5000000000 : ℝ)|=(2633314907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s6_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344503383/10000000000 : ℝ)*x 0 + (1053325993/2000000000 : ℝ)*x 1 + (-274496847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344503383/10000000000 : ℝ)^1051 ≤ (5460093949649/12500000000000 : ℝ)^795 := by
    have hnat : (5344503383 : ℕ)^1051*12500000000000^795 ≤ 5460093949649^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344503383 10000000000 5460093949649 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053325993/2000000000 : ℝ)^1051 ≤ (21420661130389/50000000000000 : ℝ)^795 := by
    have hnat : (1053325993 : ℕ)^1051*50000000000000^795 ≤ 21420661130389^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053325993 2000000000 21420661130389 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274496847/1250000000 : ℝ)^1051 ≤ (13477926128541/100000000000000 : ℝ)^795 := by
    have hnat : (274496847 : ℕ)^1051*100000000000000^795 ≤ 13477926128541^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274496847 1250000000 13477926128541 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344503383/10000000000 : ℝ), (1053325993/2000000000 : ℝ), (-274496847/1250000000 : ℝ)] ![(5460093949649/12500000000000 : ℝ), (21420661130389/50000000000000 : ℝ), (13477926128541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344503383/10000000000 : ℝ)|^1051 ≤ (5460093949649/12500000000000 : ℝ)^795
        have hw : |(5344503383/10000000000 : ℝ)|=(5344503383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053325993/2000000000 : ℝ)|^1051 ≤ (21420661130389/50000000000000 : ℝ)^795
        have hw : |(1053325993/2000000000 : ℝ)|=(1053325993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274496847/1250000000 : ℝ)|^1051 ≤ (13477926128541/100000000000000 : ℝ)^795
        have hw : |(-274496847/1250000000 : ℝ)|=(274496847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s6_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2177238989/5000000000 : ℝ)*x 0 + (845970079/2000000000 : ℝ)*x 1 + (224134877/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177238989/5000000000 : ℝ)^1051 ≤ (33317237184109/100000000000000 : ℝ)^795 := by
    have hnat : (2177238989 : ℕ)^1051*100000000000000^795 ≤ 33317237184109^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177238989 5000000000 33317237184109 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845970079/2000000000 : ℝ)^1051 ≤ (2003904296709/6250000000000 : ℝ)^795 := by
    have hnat : (845970079 : ℕ)^1051*6250000000000^795 ≤ 2003904296709^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845970079 2000000000 2003904296709 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224134877/500000000 : ℝ)^1051 ≤ (2163768378309/6250000000000 : ℝ)^795 := by
    have hnat : (224134877 : ℕ)^1051*6250000000000^795 ≤ 2163768378309^795*500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224134877 500000000 2163768378309 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177238989/5000000000 : ℝ), (845970079/2000000000 : ℝ), (224134877/500000000 : ℝ)] ![(33317237184109/100000000000000 : ℝ), (2003904296709/6250000000000 : ℝ), (2163768378309/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177238989/5000000000 : ℝ)|^1051 ≤ (33317237184109/100000000000000 : ℝ)^795
        have hw : |(2177238989/5000000000 : ℝ)|=(2177238989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845970079/2000000000 : ℝ)|^1051 ≤ (2003904296709/6250000000000 : ℝ)^795
        have hw : |(845970079/2000000000 : ℝ)|=(845970079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224134877/500000000 : ℝ)|^1051 ≤ (2163768378309/6250000000000 : ℝ)^795
        have hw : |(224134877/500000000 : ℝ)|=(224134877/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s6_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-426488353/2000000000 : ℝ)*x 0 + (2633473379/5000000000 : ℝ)*x 1 + (1078321597/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426488353/2000000000 : ℝ)^1051 ≤ (3241210212329/25000000000000 : ℝ)^795 := by
    have hnat : (426488353 : ℕ)^1051*25000000000000^795 ≤ 3241210212329^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426488353 2000000000 3241210212329 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633473379/5000000000 : ℝ)^1051 ≤ (21422364525651/50000000000000 : ℝ)^795 := by
    have hnat : (2633473379 : ℕ)^1051*50000000000000^795 ≤ 21422364525651^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633473379 5000000000 21422364525651 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078321597/2000000000 : ℝ)^1051 ≤ (441904300823/1000000000000 : ℝ)^795 := by
    have hnat : (1078321597 : ℕ)^1051*1000000000000^795 ≤ 441904300823^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078321597 2000000000 441904300823 1000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426488353/2000000000 : ℝ), (2633473379/5000000000 : ℝ), (1078321597/2000000000 : ℝ)] ![(3241210212329/25000000000000 : ℝ), (21422364525651/50000000000000 : ℝ), (441904300823/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426488353/2000000000 : ℝ)|^1051 ≤ (3241210212329/25000000000000 : ℝ)^795
        have hw : |(-426488353/2000000000 : ℝ)|=(426488353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633473379/5000000000 : ℝ)|^1051 ≤ (21422364525651/50000000000000 : ℝ)^795
        have hw : |(2633473379/5000000000 : ℝ)|=(2633473379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078321597/2000000000 : ℝ)|^1051 ≤ (441904300823/1000000000000 : ℝ)^795
        have hw : |(1078321597/2000000000 : ℝ)|=(1078321597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s6_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312592607/10000000000 : ℝ)*x 0 + (-258874579/1250000000 : ℝ)*x 1 + (1347902009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312592607/10000000000 : ℝ)^1051 ≤ (21668146339947/50000000000000 : ℝ)^795 := by
    have hnat : (5312592607 : ℕ)^1051*50000000000000^795 ≤ 21668146339947^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312592607 10000000000 21668146339947 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258874579/1250000000 : ℝ)^1051 ≤ (6236638334617/50000000000000 : ℝ)^795 := by
    have hnat : (258874579 : ℕ)^1051*50000000000000^795 ≤ 6236638334617^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258874579 1250000000 6236638334617 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347902009/2500000000 : ℝ)^1051 ≤ (22095215317453/50000000000000 : ℝ)^795 := by
    have hnat : (1347902009 : ℕ)^1051*50000000000000^795 ≤ 22095215317453^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347902009 2500000000 22095215317453 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312592607/10000000000 : ℝ), (-258874579/1250000000 : ℝ), (1347902009/2500000000 : ℝ)] ![(21668146339947/50000000000000 : ℝ), (6236638334617/50000000000000 : ℝ), (22095215317453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312592607/10000000000 : ℝ)|^1051 ≤ (21668146339947/50000000000000 : ℝ)^795
        have hw : |(5312592607/10000000000 : ℝ)|=(5312592607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258874579/1250000000 : ℝ)|^1051 ≤ (6236638334617/50000000000000 : ℝ)^795
        have hw : |(-258874579/1250000000 : ℝ)|=(258874579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347902009/2500000000 : ℝ)|^1051 ≤ (22095215317453/50000000000000 : ℝ)^795
        have hw : |(1347902009/2500000000 : ℝ)|=(1347902009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s6_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328148141/2500000000 : ℝ)*x 0 + (5391608073/10000000000 : ℝ)*x 1 + (-12943729/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328148141/2500000000 : ℝ)^1051 ≤ (43336292216181/100000000000000 : ℝ)^795 := by
    have hnat : (1328148141 : ℕ)^1051*100000000000000^795 ≤ 43336292216181^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328148141 2500000000 43336292216181 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391608073/10000000000 : ℝ)^1051 ≤ (44190431035817/100000000000000 : ℝ)^795 := by
    have hnat : (5391608073 : ℕ)^1051*100000000000000^795 ≤ 44190431035817^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391608073 10000000000 44190431035817 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12943729/62500000 : ℝ)^1051 ≤ (3118319183233/25000000000000 : ℝ)^795 := by
    have hnat : (12943729 : ℕ)^1051*25000000000000^795 ≤ 3118319183233^795*62500000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12943729 62500000 3118319183233 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328148141/2500000000 : ℝ), (5391608073/10000000000 : ℝ), (-12943729/62500000 : ℝ)] ![(43336292216181/100000000000000 : ℝ), (44190431035817/100000000000000 : ℝ), (3118319183233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328148141/2500000000 : ℝ)|^1051 ≤ (43336292216181/100000000000000 : ℝ)^795
        have hw : |(1328148141/2500000000 : ℝ)|=(1328148141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391608073/10000000000 : ℝ)|^1051 ≤ (44190431035817/100000000000000 : ℝ)^795
        have hw : |(5391608073/10000000000 : ℝ)|=(5391608073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12943729/62500000 : ℝ)|^1051 ≤ (3118319183233/25000000000000 : ℝ)^795
        have hw : |(-12943729/62500000 : ℝ)|=(12943729/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s6_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4354487997/10000000000 : ℝ)*x 0 + (56025727/125000000 : ℝ)*x 1 + (2115245849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354487997/10000000000 : ℝ)^1051 ≤ (16658669263467/50000000000000 : ℝ)^795 := by
    have hnat : (4354487997 : ℕ)^1051*50000000000000^795 ≤ 16658669263467^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354487997 10000000000 16658669263467 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56025727/125000000 : ℝ)^1051 ≤ (34613766115617/100000000000000 : ℝ)^795 := by
    have hnat : (56025727 : ℕ)^1051*100000000000000^795 ≤ 34613766115617^795*125000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56025727 125000000 34613766115617 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115245849/5000000000 : ℝ)^1051 ≤ (32068895349447/100000000000000 : ℝ)^795 := by
    have hnat : (2115245849 : ℕ)^1051*100000000000000^795 ≤ 32068895349447^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115245849 5000000000 32068895349447 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354487997/10000000000 : ℝ), (56025727/125000000 : ℝ), (2115245849/5000000000 : ℝ)] ![(16658669263467/50000000000000 : ℝ), (34613766115617/100000000000000 : ℝ), (32068895349447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354487997/10000000000 : ℝ)|^1051 ≤ (16658669263467/50000000000000 : ℝ)^795
        have hw : |(4354487997/10000000000 : ℝ)|=(4354487997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56025727/125000000 : ℝ)|^1051 ≤ (34613766115617/100000000000000 : ℝ)^795
        have hw : |(56025727/125000000 : ℝ)|=(56025727/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115245849/5000000000 : ℝ)|^1051 ≤ (32068895349447/100000000000000 : ℝ)^795
        have hw : |(2115245849/5000000000 : ℝ)|=(2115245849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11441/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5709/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5709/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5709/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5709/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5709/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5709/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5709/50000 : ℝ) ^ (8407/2048 : ℝ) ≤ (1353397952705409/10000000000000000000 : ℝ) := by
    have hpowers : (5709/50000 : ℝ)^8407 ≤ (1353397952705409/10000000000000000000 : ℝ)^2048 := by
      have hnat : (5709 : ℕ)^8407*10000000000000000000^2048 ≤ 1353397952705409^2048*50000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5709 50000 1353397952705409 10000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5709/50000 : ℝ)) (X := (1353397952705409/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14119/100000 : ℝ) ^ (8407/2048 : ℝ) ≤ (32356517428784613/100000000000000000000 : ℝ) := by
    have hpowers : (14119/100000 : ℝ)^8407 ≤ (32356517428784613/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14119 : ℕ)^8407*100000000000000000000^2048 ≤ 32356517428784613^2048*100000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14119 100000 32356517428784613 100000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14119/100000 : ℝ)) (X := (32356517428784613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001353397952705409/5000000000000000000 : ℝ) ≤ (5000329662817503/5000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (5001353397952705409/5000000000000000000 : ℝ)^2048 ≤ (5000329662817503/5000000000000000 : ℝ)^8407 := by
      have hnat : (5001353397952705409 : ℕ)^2048*5000000000000000^8407 ≤ 5000329662817503^8407*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001353397952705409 5000000000000000000 5000329662817503 5000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000329662817503/5000000000000000 : ℝ)) (X := (5001353397952705409/5000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045890496955838703/100000000000000000000 : ℝ) ≤ (2000223545689713/2000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (100045890496955838703/100000000000000000000 : ℝ)^2048 ≤ (2000223545689713/2000000000000000 : ℝ)^8407 := by
      have hnat : (100045890496955838703 : ℕ)^2048*2000000000000000^8407 ≤ 2000223545689713^8407*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045890496955838703 100000000000000000000 2000223545689713 2000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000223545689713/2000000000000000 : ℝ)) (X := (100045890496955838703/100000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032356517428784613/50000000000000000000 : ℝ) ≤ (2500394032815531/2500000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50032356517428784613/50000000000000000000 : ℝ)^2048 ≤ (2500394032815531/2500000000000000 : ℝ)^8407 := by
      have hnat : (50032356517428784613 : ℕ)^2048*2500000000000000^8407 ≤ 2500394032815531^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032356517428784613 50000000000000000000 2500394032815531 2500000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500394032815531/2500000000000000 : ℝ)) (X := (50032356517428784613/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1353397952705409/10000000000000000000 : ℝ) ≤ ((13500656375944858941/13505000000000000000 : ℝ)+2*(458402813559/270100000000000 : ℝ)*(5709/50000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (13500656375944858941/13505000000000000000 : ℝ)+2*(458402813559/270100000000000 : ℝ)*(5709/50000 : ℝ)=(5000329662817503/5000000000000000 : ℝ) by norm_num, show 1+2*(1353397952705409/10000000000000000000 : ℝ)=(5001353397952705409/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32356517428784613/100000000000000000000 : ℝ)+(1353397952705409/10000000000000000000 : ℝ) ≤ ((13500656375944858941/13505000000000000000 : ℝ)+(458402813559/270100000000000 : ℝ)*((14119/100000 : ℝ)+(5709/50000 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (13500656375944858941/13505000000000000000 : ℝ)+(458402813559/270100000000000 : ℝ)*((14119/100000 : ℝ)+(5709/50000 : ℝ))=(2000223545689713/2000000000000000 : ℝ) by norm_num, show 1+(32356517428784613/100000000000000000000 : ℝ)+(1353397952705409/10000000000000000000 : ℝ)=(100045890496955838703/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32356517428784613/100000000000000000000 : ℝ) ≤ ((13500656375944858941/13505000000000000000 : ℝ)+2*(458402813559/270100000000000 : ℝ)*(14119/100000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (13500656375944858941/13505000000000000000 : ℝ)+2*(458402813559/270100000000000 : ℝ)*(14119/100000 : ℝ)=(2500394032815531/2500000000000000 : ℝ) by norm_num, show 1+2*(32356517428784613/100000000000000000000 : ℝ)=(50032356517428784613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13500656375944858941/13505000000000000000 : ℝ)*(X 1 0+X 2 0)+(458402813559/270100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (5709/50000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (13500656375944858941/13505000000000000000 : ℝ)) (alpha := (458402813559/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13500656375944858941/13505000000000000000 : ℝ)*(X 0 1+X 2 1)+(458402813559/270100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (5709/50000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (13500656375944858941/13505000000000000000 : ℝ)) (alpha := (458402813559/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13500656375944858941/13505000000000000000 : ℝ)*(X 0 2+X 1 2)+(458402813559/270100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (5709/50000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (13500656375944858941/13505000000000000000 : ℝ)) (alpha := (458402813559/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1066218397/5000000000 : ℝ)*X 0 0+(26959629/50000000 : ℝ)*X 0 1+(21066521/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672251781/5000000000 : ℝ)*X 1 0+(-2195974737/10000000000 : ℝ)*X 1 1+(2633314907/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344503383/10000000000 : ℝ)*X 2 0+(1053325993/2000000000 : ℝ)*X 2 1+(-274496847/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177238989/5000000000 : ℝ)*X 0 0+(845970079/2000000000 : ℝ)*X 0 1+(224134877/500000000 : ℝ)*X 0 2+(2177238989/5000000000 : ℝ)*X 1 0+(845970079/2000000000 : ℝ)*X 1 1+(224134877/500000000 : ℝ)*X 1 2+(2177238989/5000000000 : ℝ)*X 2 0+(845970079/2000000000 : ℝ)*X 2 1+(224134877/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-426488353/2000000000 : ℝ)*X 0 0+(2633473379/5000000000 : ℝ)*X 0 1+(1078321597/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312592607/10000000000 : ℝ)*X 1 0+(-258874579/1250000000 : ℝ)*X 1 1+(1347902009/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328148141/2500000000 : ℝ)*X 2 0+(5391608073/10000000000 : ℝ)*X 2 1+(-12943729/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354487997/10000000000 : ℝ)*X 0 0+(56025727/125000000 : ℝ)*X 0 1+(2115245849/5000000000 : ℝ)*X 0 2+(4354487997/10000000000 : ℝ)*X 1 0+(56025727/125000000 : ℝ)*X 1 1+(2115245849/5000000000 : ℝ)*X 1 2+(4354487997/10000000000 : ℝ)*X 2 0+(56025727/125000000 : ℝ)*X 2 1+(2115245849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67343951736099793664795997/10550781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (163492831/25000000000000 : ℝ)*(base19) + (481424717/100000000000000 : ℝ)*(base23) + (19214269/50000000000000 : ℝ)*(lower3) + (59380967/100000000000000 : ℝ)*(lower4) + (57903/2000000000000 : ℝ)*(lower5) + (373003249930447/6250000000000 : ℝ)*(major0) + (373003249930447/6250000000000 : ℝ)*(major1) + (373003249930447/6250000000000 : ℝ)*(major2) + (1596226482497807/20000000000000 : ℝ)*(sp0) + (7981131758517711/100000000000000 : ℝ)*(sp1) + (7981129193340411/100000000000000 : ℝ)*(sp2) + (988741595767209/25000000000000 : ℝ)*(sp3) + (2737723907/100000000000000 : ℝ)*(sp6) + (1247363769/25000000000000 : ℝ)*(sp7) + (494371421565489/12500000000000 : ℝ)*(f.failure) + (1596226482497807/20000000000000 : ℝ)*(f.sum) + (248377347391991/6752500000000000000000000000 : ℝ)*base66 + (1799943762664101627/84406250000000000000000000000000 : ℝ)*base67 + (454785170962289127/84406250000000000000000000000000 : ℝ)*base69 + (1007842629508414127/84406250000000000000000000000000 : ℝ)*base71 + (113289413758397/13505000000000000000000000000 : ℝ)*base74 + (868310398969085873/84406250000000000000000000000000 : ℝ)*base76 + (1177182552174695377/84406250000000000000000000000000 : ℝ)*base77 + (1326364448788289127/84406250000000000000000000000000 : ℝ)*base79 + (280997100143/52753906250000000000000000 : ℝ)*base81 + (414511/250000000000000000000 : ℝ)*base90 + (414511/250000000000000000000 : ℝ)*base92 + (414511/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (944554799198771276008127499/168812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (995135181/100000000000000 : ℝ)*(base19) + (1039774091/100000000000000 : ℝ)*(base23) + (142547217/100000000000000 : ℝ)*(upper3) + (48888993/100000000000000 : ℝ)*(lower4) + (112850757/100000000000000 : ℝ)*(upper5) + (2999207402279387/50000000000000 : ℝ)*(major0) + (2999207402279387/50000000000000 : ℝ)*(major1) + (2999207402279387/50000000000000 : ℝ)*(major2) + (28561851209/100000000000000 : ℝ)*(sp1) + (15741197309/50000000000000 : ℝ)*(sp2) + (8021736907164453/100000000000000 : ℝ)*(sp4) + (4010853675089031/50000000000000 : ℝ)*(sp5) + (8021704384995743/100000000000000 : ℝ)*(sp6) + (1987546257721719/50000000000000 : ℝ)*(sp7) + (1987546257721719/50000000000000 : ℝ)*(f.failure) + (8021736907164453/100000000000000 : ℝ)*(f.sum) + (50290095457539/13505000000000000000000000000 : ℝ)*base66 + (5144505334690099167/675250000000000000000000000000000 : ℝ)*base67 + (2562087692196349167/675250000000000000000000000000000 : ℝ)*base69 + (1410457249090900833/675250000000000000000000000000000 : ℝ)*base72 + (33872414333149/13505000000000000000000000000 : ℝ)*base74 + (4615864515383099167/675250000000000000000000000000000 : ℝ)*base75 + (3892852496045599167/675250000000000000000000000000000 : ℝ)*base77 + (11598701334006349167/675250000000000000000000000000000 : ℝ)*base79 + (33729396281257/6752500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2858281/1000000000000000000000 : ℝ)*base90 + (2858281/1000000000000000000000 : ℝ)*base92 + (2858281/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1215_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1215_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1215_s7_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132456137/10000000000 : ℝ)*x 0 + (2695850041/5000000000 : ℝ)*x 1 + (5266843223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132456137/10000000000 : ℝ)^1051 ≤ (6482478182809/50000000000000 : ℝ)^795 := by
    have hnat : (2132456137 : ℕ)^1051*50000000000000^795 ≤ 6482478182809^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132456137 10000000000 6482478182809 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695850041/5000000000 : ℝ)^1051 ≤ (11047856998541/25000000000000 : ℝ)^795 := by
    have hnat : (2695850041 : ℕ)^1051*25000000000000^795 ≤ 11047856998541^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695850041 5000000000 11047856998541 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266843223/10000000000 : ℝ)^1051 ≤ (4284361562911/10000000000000 : ℝ)^795 := by
    have hnat : (5266843223 : ℕ)^1051*10000000000000^795 ≤ 4284361562911^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266843223 10000000000 4284361562911 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132456137/10000000000 : ℝ), (2695850041/5000000000 : ℝ), (5266843223/10000000000 : ℝ)] ![(6482478182809/50000000000000 : ℝ), (11047856998541/25000000000000 : ℝ), (4284361562911/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132456137/10000000000 : ℝ)|^1051 ≤ (6482478182809/50000000000000 : ℝ)^795
        have hw : |(-2132456137/10000000000 : ℝ)|=(2132456137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695850041/5000000000 : ℝ)|^1051 ≤ (11047856998541/25000000000000 : ℝ)^795
        have hw : |(2695850041/5000000000 : ℝ)|=(2695850041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266843223/10000000000 : ℝ)|^1051 ≤ (4284361562911/10000000000000 : ℝ)^795
        have hw : |(5266843223/10000000000 : ℝ)|=(5266843223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s7_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344446367/10000000000 : ℝ)*x 0 + (-1097884047/5000000000 : ℝ)*x 1 + (5266843191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344446367/10000000000 : ℝ)^1051 ≤ (21840067774751/50000000000000 : ℝ)^795 := by
    have hnat : (5344446367 : ℕ)^1051*50000000000000^795 ≤ 21840067774751^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344446367 10000000000 21840067774751 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097884047/5000000000 : ℝ)^1051 ≤ (13476249150461/100000000000000 : ℝ)^795 := by
    have hnat : (1097884047 : ℕ)^1051*100000000000000^795 ≤ 13476249150461^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097884047 5000000000 13476249150461 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266843191/10000000000 : ℝ)^1051 ≤ (42843615284981/100000000000000 : ℝ)^795 := by
    have hnat : (5266843191 : ℕ)^1051*100000000000000^795 ≤ 42843615284981^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266843191 10000000000 42843615284981 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344446367/10000000000 : ℝ), (-1097884047/5000000000 : ℝ), (5266843191/10000000000 : ℝ)] ![(21840067774751/50000000000000 : ℝ), (13476249150461/100000000000000 : ℝ), (42843615284981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344446367/10000000000 : ℝ)|^1051 ≤ (21840067774751/50000000000000 : ℝ)^795
        have hw : |(5344446367/10000000000 : ℝ)|=(5344446367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097884047/5000000000 : ℝ)|^1051 ≤ (13476249150461/100000000000000 : ℝ)^795
        have hw : |(-1097884047/5000000000 : ℝ)|=(1097884047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266843191/10000000000 : ℝ)|^1051 ≤ (42843615284981/100000000000000 : ℝ)^795
        have hw : |(5266843191/10000000000 : ℝ)|=(5266843191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s7_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668055793/1250000000 : ℝ)*x 0 + (1316710797/2500000000 : ℝ)*x 1 + (-34308877/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668055793/1250000000 : ℝ)^1051 ≤ (341251057039/781250000000 : ℝ)^795 := by
    have hnat : (668055793 : ℕ)^1051*781250000000^795 ≤ 341251057039^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668055793 1250000000 341251057039 781250000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316710797/2500000000 : ℝ)^1051 ≤ (42843615252719/100000000000000 : ℝ)^795 := by
    have hnat : (1316710797 : ℕ)^1051*100000000000000^795 ≤ 42843615252719^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316710797 2500000000 42843615252719 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34308877/156250000 : ℝ)^1051 ≤ (6738124713163/50000000000000 : ℝ)^795 := by
    have hnat : (34308877 : ℕ)^1051*50000000000000^795 ≤ 6738124713163^795*156250000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34308877 156250000 6738124713163 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668055793/1250000000 : ℝ), (1316710797/2500000000 : ℝ), (-34308877/156250000 : ℝ)] ![(341251057039/781250000000 : ℝ), (42843615252719/100000000000000 : ℝ), (6738124713163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668055793/1250000000 : ℝ)|^1051 ≤ (341251057039/781250000000 : ℝ)^795
        have hw : |(668055793/1250000000 : ℝ)|=(668055793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316710797/2500000000 : ℝ)|^1051 ≤ (42843615252719/100000000000000 : ℝ)^795
        have hw : |(1316710797/2500000000 : ℝ)|=(1316710797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34308877/156250000 : ℝ)|^1051 ≤ (6738124713163/50000000000000 : ℝ)^795
        have hw : |(-34308877/156250000 : ℝ)|=(34308877/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s7_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4354489463/10000000000 : ℝ)*x 0 + (105757291/250000000 : ℝ)*x 1 + (179290123/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354489463/10000000000 : ℝ)^1051 ≤ (4164669169453/12500000000000 : ℝ)^795 := by
    have hnat : (4354489463 : ℕ)^1051*12500000000000^795 ≤ 4164669169453^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354489463 10000000000 4164669169453 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105757291/250000000 : ℝ)^1051 ≤ (6413378100377/20000000000000 : ℝ)^795 := by
    have hnat : (105757291 : ℕ)^1051*20000000000000^795 ≤ 6413378100377^795*250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105757291 250000000 6413378100377 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179290123/400000000 : ℝ)^1051 ≤ (34615756125611/100000000000000 : ℝ)^795 := by
    have hnat : (179290123 : ℕ)^1051*100000000000000^795 ≤ 34615756125611^795*400000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179290123 400000000 34615756125611 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354489463/10000000000 : ℝ), (105757291/250000000 : ℝ), (179290123/400000000 : ℝ)] ![(4164669169453/12500000000000 : ℝ), (6413378100377/20000000000000 : ℝ), (34615756125611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354489463/10000000000 : ℝ)|^1051 ≤ (4164669169453/12500000000000 : ℝ)^795
        have hw : |(4354489463/10000000000 : ℝ)|=(4354489463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105757291/250000000 : ℝ)|^1051 ≤ (6413378100377/20000000000000 : ℝ)^795
        have hw : |(105757291/250000000 : ℝ)|=(105757291/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179290123/400000000 : ℝ)|^1051 ≤ (34615756125611/100000000000000 : ℝ)^795
        have hw : |(179290123/400000000 : ℝ)|=(179290123/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s7_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132460833/10000000000 : ℝ)*x 0 + (4114967/7812500 : ℝ)*x 1 + (5391384419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132460833/10000000000 : ℝ)^1051 ≤ (6482497055107/50000000000000 : ℝ)^795 := by
    have hnat : (2132460833 : ℕ)^1051*50000000000000^795 ≤ 6482497055107^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132460833 10000000000 6482497055107 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4114967/7812500 : ℝ)^1051 ≤ (42846998202491/100000000000000 : ℝ)^795 := by
    have hnat : (4114967 : ℕ)^1051*100000000000000^795 ≤ 42846998202491^795*7812500^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114967 7812500 42846998202491 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391384419/10000000000 : ℝ)^1051 ≤ (11047001917079/25000000000000 : ℝ)^795 := by
    have hnat : (5391384419 : ℕ)^1051*25000000000000^795 ≤ 11047001917079^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391384419 10000000000 11047001917079 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132460833/10000000000 : ℝ), (4114967/7812500 : ℝ), (5391384419/10000000000 : ℝ)] ![(6482497055107/50000000000000 : ℝ), (42846998202491/100000000000000 : ℝ), (11047001917079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132460833/10000000000 : ℝ)|^1051 ≤ (6482497055107/50000000000000 : ℝ)^795
        have hw : |(-2132460833/10000000000 : ℝ)|=(2132460833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4114967/7812500 : ℝ)|^1051 ≤ (42846998202491/100000000000000 : ℝ)^795
        have hw : |(4114967/7812500 : ℝ)|=(4114967/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391384419/10000000000 : ℝ)|^1051 ≤ (11047001917079/25000000000000 : ℝ)^795
        have hw : |(5391384419/10000000000 : ℝ)|=(5391384419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s7_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (53126473/100000000 : ℝ)*x 0 + (-414245371/2000000000 : ℝ)*x 1 + (2695692211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53126473/100000000 : ℝ)^1051 ≤ (21668441245737/50000000000000 : ℝ)^795 := by
    have hnat : (53126473 : ℕ)^1051*50000000000000^795 ≤ 21668441245737^795*100000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53126473 100000000 21668441245737 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414245371/2000000000 : ℝ)^1051 ≤ (2495021959819/20000000000000 : ℝ)^795 := by
    have hnat : (414245371 : ℕ)^1051*20000000000000^795 ≤ 2495021959819^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414245371 2000000000 2495021959819 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695692211/5000000000 : ℝ)^1051 ≤ (22094003850411/50000000000000 : ℝ)^795 := by
    have hnat : (2695692211 : ℕ)^1051*50000000000000^795 ≤ 22094003850411^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695692211 5000000000 22094003850411 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53126473/100000000 : ℝ), (-414245371/2000000000 : ℝ), (2695692211/5000000000 : ℝ)] ![(21668441245737/50000000000000 : ℝ), (2495021959819/20000000000000 : ℝ), (22094003850411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53126473/100000000 : ℝ)|^1051 ≤ (21668441245737/50000000000000 : ℝ)^795
        have hw : |(53126473/100000000 : ℝ)|=(53126473/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414245371/2000000000 : ℝ)|^1051 ≤ (2495021959819/20000000000000 : ℝ)^795
        have hw : |(-414245371/2000000000 : ℝ)|=(414245371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695692211/5000000000 : ℝ)|^1051 ≤ (22094003850411/50000000000000 : ℝ)^795
        have hw : |(2695692211/5000000000 : ℝ)|=(2695692211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s7_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656323649/5000000000 : ℝ)*x 0 + (5391384423/10000000000 : ℝ)*x 1 + (-258903357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656323649/5000000000 : ℝ)^1051 ≤ (21668441234953/50000000000000 : ℝ)^795 := by
    have hnat : (2656323649 : ℕ)^1051*50000000000000^795 ≤ 21668441234953^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656323649 5000000000 21668441234953 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391384423/10000000000 : ℝ)^1051 ≤ (44188007711657/100000000000000 : ℝ)^795 := by
    have hnat : (5391384423 : ℕ)^1051*100000000000000^795 ≤ 44188007711657^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391384423 10000000000 44188007711657 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258903357/1250000000 : ℝ)^1051 ≤ (12475109807057/100000000000000 : ℝ)^795 := by
    have hnat : (258903357 : ℕ)^1051*100000000000000^795 ≤ 12475109807057^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258903357 1250000000 12475109807057 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656323649/5000000000 : ℝ), (5391384423/10000000000 : ℝ), (-258903357/1250000000 : ℝ)] ![(21668441234953/50000000000000 : ℝ), (44188007711657/100000000000000 : ℝ), (12475109807057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656323649/5000000000 : ℝ)|^1051 ≤ (21668441234953/50000000000000 : ℝ)^795
        have hw : |(2656323649/5000000000 : ℝ)|=(2656323649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391384423/10000000000 : ℝ)|^1051 ≤ (44188007711657/100000000000000 : ℝ)^795
        have hw : |(5391384423/10000000000 : ℝ)|=(5391384423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258903357/1250000000 : ℝ)|^1051 ≤ (12475109807057/100000000000000 : ℝ)^795
        have hw : |(-258903357/1250000000 : ℝ)|=(258903357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s7_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (136078093/312500000 : ℝ)*x 0 + (4481618217/10000000000 : ℝ)*x 1 + (1057732201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136078093/312500000 : ℝ)^1051 ≤ (16658724790153/50000000000000 : ℝ)^795 := by
    have hnat : (136078093 : ℕ)^1051*50000000000000^795 ≤ 16658724790153^795*312500000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136078093 312500000 16658724790153 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481618217/10000000000 : ℝ)^1051 ≤ (17304637281443/50000000000000 : ℝ)^795 := by
    have hnat : (4481618217 : ℕ)^1051*50000000000000^795 ≤ 17304637281443^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481618217 10000000000 17304637281443 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057732201/2500000000 : ℝ)^1051 ≤ (641465516797/2000000000000 : ℝ)^795 := by
    have hnat : (1057732201 : ℕ)^1051*2000000000000^795 ≤ 641465516797^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057732201 2500000000 641465516797 2000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136078093/312500000 : ℝ), (4481618217/10000000000 : ℝ), (1057732201/2500000000 : ℝ)] ![(16658724790153/50000000000000 : ℝ), (17304637281443/50000000000000 : ℝ), (641465516797/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136078093/312500000 : ℝ)|^1051 ≤ (16658724790153/50000000000000 : ℝ)^795
        have hw : |(136078093/312500000 : ℝ)|=(136078093/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481618217/10000000000 : ℝ)|^1051 ≤ (17304637281443/50000000000000 : ℝ)^795
        have hw : |(4481618217/10000000000 : ℝ)|=(4481618217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057732201/2500000000 : ℝ)|^1051 ≤ (641465516797/2000000000000 : ℝ)^795
        have hw : |(1057732201/2500000000 : ℝ)|=(1057732201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2289/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11441/100000 : ℝ) ^ (8407/2048 : ℝ) ≤ (3411560355147459/25000000000000000000 : ℝ) := by
    have hpowers : (11441/100000 : ℝ)^8407 ≤ (3411560355147459/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11441 : ℕ)^8407*25000000000000000000^2048 ≤ 3411560355147459^2048*100000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11441 100000 3411560355147459 25000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11441/100000 : ℝ)) (X := (3411560355147459/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (8407/2048 : ℝ) ≤ (32131335294671193/100000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^8407 ≤ (32131335294671193/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2819 : ℕ)^8407*100000000000000000000^2048 ≤ 32131335294671193^2048*20000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 32131335294671193 100000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (32131335294671193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503411560355147459/12500000000000000000 : ℝ) ≤ (10000664794056599/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (12503411560355147459/12500000000000000000 : ℝ)^2048 ≤ (10000664794056599/10000000000000000 : ℝ)^8407 := by
      have hnat : (12503411560355147459 : ℕ)^2048*10000000000000000^8407 ≤ 10000664794056599^8407*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503411560355147459 12500000000000000000 10000664794056599 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000664794056599/10000000000000000 : ℝ)) (X := (12503411560355147459/12500000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045777576715261029/100000000000000000000 : ℝ) ≤ (5000557489295591/5000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (100045777576715261029/100000000000000000000 : ℝ)^2048 ≤ (5000557489295591/5000000000000000 : ℝ)^8407 := by
      have hnat : (100045777576715261029 : ℕ)^2048*5000000000000000^8407 ≤ 5000557489295591^8407*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045777576715261029 100000000000000000000 5000557489295591 5000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000557489295591/5000000000000000 : ℝ)) (X := (100045777576715261029/100000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032131335294671193/50000000000000000000 : ℝ) ≤ (2000313032625153/2000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50032131335294671193/50000000000000000000 : ℝ)^2048 ≤ (2000313032625153/2000000000000000 : ℝ)^8407 := by
      have hnat : (50032131335294671193 : ℕ)^2048*2000000000000000^8407 ≤ 2000313032625153^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032131335294671193 50000000000000000000 2000313032625153 2000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000313032625153/2000000000000000 : ℝ)) (X := (50032131335294671193/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3411560355147459/25000000000000000000 : ℝ) ≤ ((1326573162045294277/1327000000000000000 : ℝ)+2*(450184534583/265400000000000 : ℝ)*(11441/100000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (1326573162045294277/1327000000000000000 : ℝ)+2*(450184534583/265400000000000 : ℝ)*(11441/100000 : ℝ)=(10000664794056599/10000000000000000 : ℝ) by norm_num, show 1+2*(3411560355147459/25000000000000000000 : ℝ)=(12503411560355147459/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32131335294671193/100000000000000000000 : ℝ)+(3411560355147459/25000000000000000000 : ℝ) ≤ ((1326573162045294277/1327000000000000000 : ℝ)+(450184534583/265400000000000 : ℝ)*((2819/20000 : ℝ)+(11441/100000 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (1326573162045294277/1327000000000000000 : ℝ)+(450184534583/265400000000000 : ℝ)*((2819/20000 : ℝ)+(11441/100000 : ℝ))=(5000557489295591/5000000000000000 : ℝ) by norm_num, show 1+(32131335294671193/100000000000000000000 : ℝ)+(3411560355147459/25000000000000000000 : ℝ)=(100045777576715261029/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32131335294671193/100000000000000000000 : ℝ) ≤ ((1326573162045294277/1327000000000000000 : ℝ)+2*(450184534583/265400000000000 : ℝ)*(2819/20000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (1326573162045294277/1327000000000000000 : ℝ)+2*(450184534583/265400000000000 : ℝ)*(2819/20000 : ℝ)=(2000313032625153/2000000000000000 : ℝ) by norm_num, show 1+2*(32131335294671193/100000000000000000000 : ℝ)=(50032131335294671193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1326573162045294277/1327000000000000000 : ℝ)*(X 1 0+X 2 0)+(450184534583/265400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (11441/100000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (1326573162045294277/1327000000000000000 : ℝ)) (alpha := (450184534583/265400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1326573162045294277/1327000000000000000 : ℝ)*(X 0 1+X 2 1)+(450184534583/265400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (11441/100000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (1326573162045294277/1327000000000000000 : ℝ)) (alpha := (450184534583/265400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1326573162045294277/1327000000000000000 : ℝ)*(X 0 2+X 1 2)+(450184534583/265400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (11441/100000 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (1326573162045294277/1327000000000000000 : ℝ)) (alpha := (450184534583/265400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2132456137/10000000000 : ℝ)*X 0 0+(2695850041/5000000000 : ℝ)*X 0 1+(5266843223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344446367/10000000000 : ℝ)*X 1 0+(-1097884047/5000000000 : ℝ)*X 1 1+(5266843191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668055793/1250000000 : ℝ)*X 2 0+(1316710797/2500000000 : ℝ)*X 2 1+(-34308877/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354489463/10000000000 : ℝ)*X 0 0+(105757291/250000000 : ℝ)*X 0 1+(179290123/400000000 : ℝ)*X 0 2+(4354489463/10000000000 : ℝ)*X 1 0+(105757291/250000000 : ℝ)*X 1 1+(179290123/400000000 : ℝ)*X 1 2+(4354489463/10000000000 : ℝ)*X 2 0+(105757291/250000000 : ℝ)*X 2 1+(179290123/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2132460833/10000000000 : ℝ)*X 0 0+(4114967/7812500 : ℝ)*X 0 1+(5391384419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((53126473/100000000 : ℝ)*X 1 0+(-414245371/2000000000 : ℝ)*X 1 1+(2695692211/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656323649/5000000000 : ℝ)*X 2 0+(5391384423/10000000000 : ℝ)*X 2 1+(-258903357/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136078093/312500000 : ℝ)*X 0 0+(4481618217/10000000000 : ℝ)*X 0 1+(1057732201/2500000000 : ℝ)*X 0 2+(136078093/312500000 : ℝ)*X 1 0+(4481618217/10000000000 : ℝ)*X 1 1+(1057732201/2500000000 : ℝ)*X 1 2+(136078093/312500000 : ℝ)*X 2 0+(4481618217/10000000000 : ℝ)*X 2 1+(1057732201/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (336079840868554135740982527/33175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (974508891/50000000000000 : ℝ)*(base19) + (1807214151/100000000000000 : ℝ)*(base23) + (57364861/100000000000000 : ℝ)*(lower2) + (143153081/50000000000000 : ℝ)*(upper3) + (145073557/100000000000000 : ℝ)*(upper5) + (2994548165547583/50000000000000 : ℝ)*(major0) + (2994548165547583/50000000000000 : ℝ)*(major1) + (2994548165547583/50000000000000 : ℝ)*(major2) + (2002306511946513/25000000000000 : ℝ)*(sp0) + (4004636561949353/50000000000000 : ℝ)*(sp1) + (125144894776599/1562500000000 : ℝ)*(sp2) + (496110947425427/12500000000000 : ℝ)*(sp3) + (9805026087/20000000000000 : ℝ)*(sp4) + (1483609329/5000000000000 : ℝ)*(sp7) + (992229312897499/25000000000000 : ℝ)*(f.failure) + (1001159384114561/12500000000000 : ℝ)*(f.sum) + (21134370506913/3317500000000000000000000000 : ℝ)*base66 + (766659905084127491/66350000000000000000000000000000 : ℝ)*base67 + (443368175416177491/66350000000000000000000000000000 : ℝ)*base69 + (352219839320972509/66350000000000000000000000000000 : ℝ)*base72 + (6594785974529/6635000000000000000000000000 : ℝ)*base73 + (1091077340861427491/66350000000000000000000000000000 : ℝ)*base75 + (356848314601672509/66350000000000000000000000000000 : ℝ)*base78 + (488785753163727491/66350000000000000000000000000000 : ℝ)*base79 + (22709052720769/6635000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2717499/500000000000000000000 : ℝ)*base89 + (2717499/500000000000000000000 : ℝ)*base91 + (2717499/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99173650410744550735262991/33175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68455237/12500000000000 : ℝ)*(base19) + (295287161/50000000000000 : ℝ)*(base23) + (62616381/100000000000000 : ℝ)*(upper3) + (16859/80000000000 : ℝ)*(lower4) + (783691/1250000000000 : ℝ)*(upper5) + (6019400480913861/100000000000000 : ℝ)*(major0) + (6019400480913861/100000000000000 : ℝ)*(major1) + (6019400480913861/100000000000000 : ℝ)*(major2) + (482234009/3125000000000 : ℝ)*(sp1) + (515103769/3125000000000 : ℝ)*(sp2) + (4024900669173907/50000000000000 : ℝ)*(sp4) + (804978535921763/10000000000000 : ℝ)*(sp5) + (8049784264452883/100000000000000 : ℝ)*(sp6) + (1994499761916463/50000000000000 : ℝ)*(sp7) + (1994499761916463/50000000000000 : ℝ)*(f.failure) + (4024900669173907/50000000000000 : ℝ)*(f.sum) + (49383589699817/13270000000000000000000000000 : ℝ)*base66 + (992953779123311503/132700000000000000000000000000000 : ℝ)*base68 + (1128130092230911503/132700000000000000000000000000000 : ℝ)*base70 + (1298559608626311503/132700000000000000000000000000000 : ℝ)*base72 + (23872629115563/13270000000000000000000000000 : ℝ)*base73 + (3720623217856311503/132700000000000000000000000000000 : ℝ)*base76 + (819136880519311503/132700000000000000000000000000000 : ℝ)*base78 + (95276035819588497/132700000000000000000000000000000 : ℝ)*base79 + (42123282325677/13270000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5256463/1000000000000000000000 : ℝ)*base89 + (5256463/1000000000000000000000 : ℝ)*base91 + (5256463/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1215_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1215_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1215_s8_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132462231/10000000000 : ℝ)*x 0 + (5391656053/10000000000 : ℝ)*x 1 + (5266883031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132462231/10000000000 : ℝ)^1051 ≤ (1620625668349/12500000000000 : ℝ)^795 := by
    have hnat : (2132462231 : ℕ)^1051*12500000000000^795 ≤ 1620625668349^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132462231 10000000000 1620625668349 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391656053/10000000000 : ℝ)^1051 ≤ (22095475459863/50000000000000 : ℝ)^795 := by
    have hnat : (5391656053 : ℕ)^1051*50000000000000^795 ≤ 22095475459863^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391656053 10000000000 22095475459863 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266883031/10000000000 : ℝ)^1051 ≤ (10711010931531/25000000000000 : ℝ)^795 := by
    have hnat : (5266883031 : ℕ)^1051*25000000000000^795 ≤ 10711010931531^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266883031 10000000000 10711010931531 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132462231/10000000000 : ℝ), (5391656053/10000000000 : ℝ), (5266883031/10000000000 : ℝ)] ![(1620625668349/12500000000000 : ℝ), (22095475459863/50000000000000 : ℝ), (10711010931531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132462231/10000000000 : ℝ)|^1051 ≤ (1620625668349/12500000000000 : ℝ)^795
        have hw : |(-2132462231/10000000000 : ℝ)|=(2132462231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391656053/10000000000 : ℝ)|^1051 ≤ (22095475459863/50000000000000 : ℝ)^795
        have hw : |(5391656053/10000000000 : ℝ)|=(5391656053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266883031/10000000000 : ℝ)|^1051 ≤ (10711010931531/25000000000000 : ℝ)^795
        have hw : |(5266883031/10000000000 : ℝ)|=(5266883031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s8_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668054293/1250000000 : ℝ)*x 0 + (-2195731069/10000000000 : ℝ)*x 1 + (1053376641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668054293/1250000000 : ℝ)^1051 ≤ (21840002821703/50000000000000 : ℝ)^795 := by
    have hnat : (668054293 : ℕ)^1051*50000000000000^795 ≤ 21840002821703^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668054293 1250000000 21840002821703 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195731069/10000000000 : ℝ)^1051 ≤ (2695189748417/20000000000000 : ℝ)^795 := by
    have hnat : (2195731069 : ℕ)^1051*20000000000000^795 ≤ 2695189748417^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195731069 10000000000 2695189748417 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053376641/2000000000 : ℝ)^1051 ≤ (4284404559733/10000000000000 : ℝ)^795 := by
    have hnat : (1053376641 : ℕ)^1051*10000000000000^795 ≤ 4284404559733^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053376641 2000000000 4284404559733 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668054293/1250000000 : ℝ), (-2195731069/10000000000 : ℝ), (1053376641/2000000000 : ℝ)] ![(21840002821703/50000000000000 : ℝ), (2695189748417/20000000000000 : ℝ), (4284404559733/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668054293/1250000000 : ℝ)|^1051 ≤ (21840002821703/50000000000000 : ℝ)^795
        have hw : |(668054293/1250000000 : ℝ)|=(668054293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195731069/10000000000 : ℝ)|^1051 ≤ (2695189748417/20000000000000 : ℝ)^795
        have hw : |(-2195731069/10000000000 : ℝ)|=(2195731069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053376641/2000000000 : ℝ)|^1051 ≤ (4284404559733/10000000000000 : ℝ)^795
        have hw : |(1053376641/2000000000 : ℝ)|=(1053376641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s8_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344434643/10000000000 : ℝ)*x 0 + (5266882977/10000000000 : ℝ)*x 1 + (-1097865487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344434643/10000000000 : ℝ)^1051 ≤ (1092000221851/2500000000000 : ℝ)^795 := by
    have hnat : (5344434643 : ℕ)^1051*2500000000000^795 ≤ 1092000221851^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344434643 10000000000 1092000221851 2500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266882977/10000000000 : ℝ)^1051 ≤ (8568808629081/20000000000000 : ℝ)^795 := by
    have hnat : (5266882977 : ℕ)^1051*20000000000000^795 ≤ 8568808629081^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266882977 10000000000 8568808629081 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097865487/5000000000 : ℝ)^1051 ≤ (1347594797129/10000000000000 : ℝ)^795 := by
    have hnat : (1097865487 : ℕ)^1051*10000000000000^795 ≤ 1347594797129^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097865487 5000000000 1347594797129 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344434643/10000000000 : ℝ), (5266882977/10000000000 : ℝ), (-1097865487/5000000000 : ℝ)] ![(1092000221851/2500000000000 : ℝ), (8568808629081/20000000000000 : ℝ), (1347594797129/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344434643/10000000000 : ℝ)|^1051 ≤ (1092000221851/2500000000000 : ℝ)^795
        have hw : |(5344434643/10000000000 : ℝ)|=(5344434643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266882977/10000000000 : ℝ)|^1051 ≤ (8568808629081/20000000000000 : ℝ)^795
        have hw : |(5266882977/10000000000 : ℝ)|=(5266882977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097865487/5000000000 : ℝ)|^1051 ≤ (1347594797129/10000000000000 : ℝ)^795
        have hw : |(-1097865487/5000000000 : ℝ)|=(1097865487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s8_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4354491849/10000000000 : ℝ)*x 0 + (2115187963/5000000000 : ℝ)*x 1 + (224108399/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354491849/10000000000 : ℝ)^1051 ≤ (1665868874509/5000000000000 : ℝ)^795 := by
    have hnat : (4354491849 : ℕ)^1051*5000000000000^795 ≤ 1665868874509^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354491849 10000000000 1665868874509 5000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115187963/5000000000 : ℝ)^1051 ≤ (32067735156121/100000000000000 : ℝ)^795 := by
    have hnat : (2115187963 : ℕ)^1051*100000000000000^795 ≤ 32067735156121^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115187963 5000000000 32067735156121 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224108399/500000000 : ℝ)^1051 ≤ (6922977466747/20000000000000 : ℝ)^795 := by
    have hnat : (224108399 : ℕ)^1051*20000000000000^795 ≤ 6922977466747^795*500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224108399 500000000 6922977466747 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354491849/10000000000 : ℝ), (2115187963/5000000000 : ℝ), (224108399/500000000 : ℝ)] ![(1665868874509/5000000000000 : ℝ), (32067735156121/100000000000000 : ℝ), (6922977466747/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354491849/10000000000 : ℝ)|^1051 ≤ (1665868874509/5000000000000 : ℝ)^795
        have hw : |(4354491849/10000000000 : ℝ)|=(4354491849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115187963/5000000000 : ℝ)|^1051 ≤ (32067735156121/100000000000000 : ℝ)^795
        have hw : |(2115187963/5000000000 : ℝ)|=(2115187963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224108399/500000000 : ℝ)|^1051 ≤ (6922977466747/20000000000000 : ℝ)^795
        have hw : |(224108399/500000000 : ℝ)|=(224108399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s8_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-26655837/125000000 : ℝ)*x 0 + (5267197181/10000000000 : ℝ)*x 1 + (1347835187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26655837/125000000 : ℝ)^1051 ≤ (1620630419583/12500000000000 : ℝ)^795 := by
    have hnat : (26655837 : ℕ)^1051*12500000000000^795 ≤ 1620630419583^795*125000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26655837 125000000 1620630419583 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267197181/10000000000 : ℝ)^1051 ≤ (10711855536459/25000000000000 : ℝ)^795 := by
    have hnat : (5267197181 : ℕ)^1051*25000000000000^795 ≤ 10711855536459^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267197181 10000000000 10711855536459 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347835187/2500000000 : ℝ)^1051 ≤ (1380860452559/3125000000000 : ℝ)^795 := by
    have hnat : (1347835187 : ℕ)^1051*3125000000000^795 ≤ 1380860452559^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347835187 2500000000 1380860452559 3125000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26655837/125000000 : ℝ), (5267197181/10000000000 : ℝ), (1347835187/2500000000 : ℝ)] ![(1620630419583/12500000000000 : ℝ), (10711855536459/25000000000000 : ℝ), (1380860452559/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26655837/125000000 : ℝ)|^1051 ≤ (1620630419583/12500000000000 : ℝ)^795
        have hw : |(-26655837/125000000 : ℝ)|=(26655837/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267197181/10000000000 : ℝ)|^1051 ≤ (10711855536459/25000000000000 : ℝ)^795
        have hw : |(5267197181/10000000000 : ℝ)|=(5267197181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347835187/2500000000 : ℝ)|^1051 ≤ (1380860452559/3125000000000 : ℝ)^795
        have hw : |(1347835187/2500000000 : ℝ)|=(1347835187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s8_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328164227/2500000000 : ℝ)*x 0 + (-2071273333/10000000000 : ℝ)*x 1 + (5391340703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328164227/2500000000 : ℝ)^1051 ≤ (21668493052373/50000000000000 : ℝ)^795 := by
    have hnat : (1328164227 : ℕ)^1051*50000000000000^795 ≤ 21668493052373^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328164227 2500000000 21668493052373 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071273333/10000000000 : ℝ)^1051 ≤ (389858746373/3125000000000 : ℝ)^795 := by
    have hnat : (2071273333 : ℕ)^1051*3125000000000^795 ≤ 389858746373^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071273333 10000000000 389858746373 3125000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391340703/10000000000 : ℝ)^1051 ≤ (44187533994303/100000000000000 : ℝ)^795 := by
    have hnat : (5391340703 : ℕ)^1051*100000000000000^795 ≤ 44187533994303^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391340703 10000000000 44187533994303 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328164227/2500000000 : ℝ), (-2071273333/10000000000 : ℝ), (5391340703/10000000000 : ℝ)] ![(21668493052373/50000000000000 : ℝ), (389858746373/3125000000000 : ℝ), (44187533994303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328164227/2500000000 : ℝ)|^1051 ≤ (21668493052373/50000000000000 : ℝ)^795
        have hw : |(1328164227/2500000000 : ℝ)|=(1328164227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2071273333/10000000000 : ℝ)|^1051 ≤ (389858746373/3125000000000 : ℝ)^795
        have hw : |(-2071273333/10000000000 : ℝ)|=(2071273333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391340703/10000000000 : ℝ)|^1051 ≤ (44187533994303/100000000000000 : ℝ)^795
        have hw : |(5391340703/10000000000 : ℝ)|=(5391340703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s8_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312657059/10000000000 : ℝ)*x 0 + (2695670361/5000000000 : ℝ)*x 1 + (-2071273103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312657059/10000000000 : ℝ)^1051 ≤ (2166849386657/5000000000000 : ℝ)^795 := by
    have hnat : (5312657059 : ℕ)^1051*5000000000000^795 ≤ 2166849386657^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312657059 10000000000 2166849386657 5000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695670361/5000000000 : ℝ)^1051 ≤ (11046883550043/25000000000000 : ℝ)^795 := by
    have hnat : (2695670361 : ℕ)^1051*25000000000000^795 ≤ 11046883550043^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695670361 5000000000 11046883550043 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071273103/10000000000 : ℝ)^1051 ≤ (1559434756567/12500000000000 : ℝ)^795 := by
    have hnat : (2071273103 : ℕ)^1051*12500000000000^795 ≤ 1559434756567^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071273103 10000000000 1559434756567 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312657059/10000000000 : ℝ), (2695670361/5000000000 : ℝ), (-2071273103/10000000000 : ℝ)] ![(2166849386657/5000000000000 : ℝ), (11046883550043/25000000000000 : ℝ), (1559434756567/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312657059/10000000000 : ℝ)|^1051 ≤ (2166849386657/5000000000000 : ℝ)^795
        have hw : |(5312657059/10000000000 : ℝ)|=(5312657059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695670361/5000000000 : ℝ)|^1051 ≤ (11046883550043/25000000000000 : ℝ)^795
        have hw : |(2695670361/5000000000 : ℝ)|=(2695670361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2071273103/10000000000 : ℝ)|^1051 ≤ (1559434756567/12500000000000 : ℝ)^795
        have hw : |(-2071273103/10000000000 : ℝ)|=(2071273103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s8_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4354501201/10000000000 : ℝ)*x 0 + (896306821/2000000000 : ℝ)*x 1 + (1057753061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354501201/10000000000 : ℝ)^1051 ≤ (2082342005397/6250000000000 : ℝ)^795 := by
    have hnat : (4354501201 : ℕ)^1051*6250000000000^795 ≤ 2082342005397^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354501201 10000000000 2082342005397 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896306821/2000000000 : ℝ)^1051 ≤ (17304207923127/50000000000000 : ℝ)^795 := by
    have hnat : (896306821 : ℕ)^1051*50000000000000^795 ≤ 17304207923127^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896306821 2000000000 17304207923127 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057753061/2500000000 : ℝ)^1051 ≤ (16037056028301/50000000000000 : ℝ)^795 := by
    have hnat : (1057753061 : ℕ)^1051*50000000000000^795 ≤ 16037056028301^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057753061 2500000000 16037056028301 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354501201/10000000000 : ℝ), (896306821/2000000000 : ℝ), (1057753061/2500000000 : ℝ)] ![(2082342005397/6250000000000 : ℝ), (17304207923127/50000000000000 : ℝ), (16037056028301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354501201/10000000000 : ℝ)|^1051 ≤ (2082342005397/6250000000000 : ℝ)^795
        have hw : |(4354501201/10000000000 : ℝ)|=(4354501201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896306821/2000000000 : ℝ)|^1051 ≤ (17304207923127/50000000000000 : ℝ)^795
        have hw : |(896306821/2000000000 : ℝ)|=(896306821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057753061/2500000000 : ℝ)|^1051 ≤ (16037056028301/50000000000000 : ℝ)^795
        have hw : |(1057753061/2500000000 : ℝ)|=(1057753061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5723/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14089/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2289/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2289/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2289/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2289/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2289/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2289/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2289/20000 : ℝ) ^ (8407/2048 : ℝ) ≤ (13665836899042561/100000000000000000000 : ℝ) := by
    have hpowers : (2289/20000 : ℝ)^8407 ≤ (13665836899042561/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2289 : ℕ)^8407*100000000000000000000^2048 ≤ 13665836899042561^2048*20000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2289 20000 13665836899042561 100000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2289/20000 : ℝ)) (X := (13665836899042561/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (8407/2048 : ℝ) ≤ (32084571945164223/100000000000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^8407 ≤ (32084571945164223/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1409 : ℕ)^8407*100000000000000000000^2048 ≤ 32084571945164223^2048*10000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 32084571945164223 100000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (32084571945164223/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013665836899042561/50000000000000000000 : ℝ) ≤ (10000665748576671/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50013665836899042561/50000000000000000000 : ℝ)^2048 ≤ (10000665748576671/10000000000000000 : ℝ)^8407 := by
      have hnat : (50013665836899042561 : ℕ)^2048*10000000000000000^8407 ≤ 10000665748576671^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013665836899042561 50000000000000000000 10000665748576671 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000665748576671/10000000000000000 : ℝ)) (X := (50013665836899042561/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563214850138190731/1562500000000000000 : ℝ) ≤ (10001114316993137/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (1563214850138190731/1562500000000000000 : ℝ)^2048 ≤ (10001114316993137/10000000000000000 : ℝ)^8407 := by
      have hnat : (1563214850138190731 : ℕ)^2048*10000000000000000^8407 ≤ 10001114316993137^8407*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563214850138190731 1562500000000000000 10001114316993137 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001114316993137/10000000000000000 : ℝ)) (X := (1563214850138190731/1562500000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032084571945164223/50000000000000000000 : ℝ) ≤ (10001562885409603/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50032084571945164223/50000000000000000000 : ℝ)^2048 ≤ (10001562885409603/10000000000000000 : ℝ)^8407 := by
      have hnat : (50032084571945164223 : ℕ)^2048*10000000000000000^8407 ≤ 10001562885409603^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032084571945164223 50000000000000000000 10001562885409603 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001562885409603/10000000000000000 : ℝ)) (X := (50032084571945164223/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13665836899042561/100000000000000000000 : ℝ) ≤ ((5288298634786477611/5290000000000000000 : ℝ)+2*(224284208233/132250000000000 : ℝ)*(2289/20000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (5288298634786477611/5290000000000000000 : ℝ)+2*(224284208233/132250000000000 : ℝ)*(2289/20000 : ℝ)=(10000665748576671/10000000000000000 : ℝ) by norm_num, show 1+2*(13665836899042561/100000000000000000000 : ℝ)=(50013665836899042561/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32084571945164223/100000000000000000000 : ℝ)+(13665836899042561/100000000000000000000 : ℝ) ≤ ((5288298634786477611/5290000000000000000 : ℝ)+(224284208233/132250000000000 : ℝ)*((1409/10000 : ℝ)+(2289/20000 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (5288298634786477611/5290000000000000000 : ℝ)+(224284208233/132250000000000 : ℝ)*((1409/10000 : ℝ)+(2289/20000 : ℝ))=(10001114316993137/10000000000000000 : ℝ) by norm_num, show 1+(32084571945164223/100000000000000000000 : ℝ)+(13665836899042561/100000000000000000000 : ℝ)=(1563214850138190731/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32084571945164223/100000000000000000000 : ℝ) ≤ ((5288298634786477611/5290000000000000000 : ℝ)+2*(224284208233/132250000000000 : ℝ)*(1409/10000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (5288298634786477611/5290000000000000000 : ℝ)+2*(224284208233/132250000000000 : ℝ)*(1409/10000 : ℝ)=(10001562885409603/10000000000000000 : ℝ) by norm_num, show 1+2*(32084571945164223/100000000000000000000 : ℝ)=(50032084571945164223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5288298634786477611/5290000000000000000 : ℝ)*(X 1 0+X 2 0)+(224284208233/132250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (5288298634786477611/5290000000000000000 : ℝ)) (alpha := (224284208233/132250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5288298634786477611/5290000000000000000 : ℝ)*(X 0 1+X 2 1)+(224284208233/132250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (5288298634786477611/5290000000000000000 : ℝ)) (alpha := (224284208233/132250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5288298634786477611/5290000000000000000 : ℝ)*(X 0 2+X 1 2)+(224284208233/132250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (2289/20000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (5288298634786477611/5290000000000000000 : ℝ)) (alpha := (224284208233/132250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2132462231/10000000000 : ℝ)*X 0 0+(5391656053/10000000000 : ℝ)*X 0 1+(5266883031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668054293/1250000000 : ℝ)*X 1 0+(-2195731069/10000000000 : ℝ)*X 1 1+(1053376641/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344434643/10000000000 : ℝ)*X 2 0+(5266882977/10000000000 : ℝ)*X 2 1+(-1097865487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354491849/10000000000 : ℝ)*X 0 0+(2115187963/5000000000 : ℝ)*X 0 1+(224108399/500000000 : ℝ)*X 0 2+(4354491849/10000000000 : ℝ)*X 1 0+(2115187963/5000000000 : ℝ)*X 1 1+(224108399/500000000 : ℝ)*X 1 2+(4354491849/10000000000 : ℝ)*X 2 0+(2115187963/5000000000 : ℝ)*X 2 1+(224108399/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-26655837/125000000 : ℝ)*X 0 0+(5267197181/10000000000 : ℝ)*X 0 1+(1347835187/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328164227/2500000000 : ℝ)*X 1 0+(-2071273333/10000000000 : ℝ)*X 1 1+(5391340703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312657059/10000000000 : ℝ)*X 2 0+(2695670361/5000000000 : ℝ)*X 2 1+(-2071273103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354501201/10000000000 : ℝ)*X 0 0+(896306821/2000000000 : ℝ)*X 0 1+(1057753061/2500000000 : ℝ)*X 0 2+(4354501201/10000000000 : ℝ)*X 1 0+(896306821/2000000000 : ℝ)*X 1 1+(1057753061/2500000000 : ℝ)*X 1 2+(4354501201/10000000000 : ℝ)*X 2 0+(896306821/2000000000 : ℝ)*X 2 1+(1057753061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2202769973669646852678443397/264500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41065171/2500000000000 : ℝ)*(base19) + (356983083/20000000000000 : ℝ)*(base23) + (163582231/100000000000000 : ℝ)*(lower2) + (1720039/781250000000 : ℝ)*(upper3) + (58163863/25000000000000 : ℝ)*(upper5) + (5993118826093691/100000000000000 : ℝ)*(major0) + (5993118826093691/100000000000000 : ℝ)*(major1) + (5993118826093691/100000000000000 : ℝ)*(major2) + (8014598470497469/100000000000000 : ℝ)*(sp0) + (160293056223213/2000000000000 : ℝ)*(sp1) + (320586106754083/4000000000000 : ℝ)*(sp2) + (79431102181607/2000000000000 : ℝ)*(sp3) + (55983270021/100000000000000 : ℝ)*(sp4) + (27811737771/100000000000000 : ℝ)*(sp7) + (3971582920818121/100000000000000 : ℝ)*(f.failure) + (801465445376749/10000000000000 : ℝ)*(f.sum) + (9664675857493/1653125000000000000000000000 : ℝ)*base66 + (3039765623702972201/529000000000000000000000000000000 : ℝ)*base67 + (5418281525620972201/529000000000000000000000000000000 : ℝ)*base69 + (5036275831529027799/529000000000000000000000000000000 : ℝ)*base72 + (8872326370119/13225000000000000000000000000 : ℝ)*base74 + (5453608673033972201/529000000000000000000000000000000 : ℝ)*base75 + (6258832192154027799/529000000000000000000000000000000 : ℝ)*base78 + (11757375303309972201/529000000000000000000000000000000 : ℝ)*base79 + (16309512346839/3306250000000000000000000000 : ℝ)*base81 + (7401879/2000000000000000000000 : ℝ)*base90 + (7401879/2000000000000000000000 : ℝ)*base92 + (7401879/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10747379723859764076573/13225000000000000000000000000 : ℝ) := by norm_num
    linear_combination (599397077/100000000000000 : ℝ)*(base19) + (8127889/800000000000 : ℝ)*(base23) + (82444263/50000000000000 : ℝ)*(lower1) + (2347027/3125000000000 : ℝ)*(upper3) + (34399831/100000000000000 : ℝ)*(lower4) + (510079/1562500000000 : ℝ)*(upper5) + (3011710107548163/50000000000000 : ℝ)*(major0) + (3011710107548163/50000000000000 : ℝ)*(major1) + (3011710107548163/50000000000000 : ℝ)*(major2) + (10272411493/50000000000000 : ℝ)*(sp2) + (8055177039609619/100000000000000 : ℝ)*(sp4) + (8055176440212541/100000000000000 : ℝ)*(sp5) + (2013788869700127/25000000000000 : ℝ)*(sp6) + (498957920436809/12500000000000 : ℝ)*(sp7) + (498957920436809/12500000000000 : ℝ)*(f.failure) + (8055177039609619/100000000000000 : ℝ)*(f.sum) + (2050108388571/3306250000000000000000000000 : ℝ)*base66 + (7642650571407338593/264500000000000000000000000000000 : ℝ)*base67 + (2898472843267161407/264500000000000000000000000000000 : ℝ)*base70 + (11501310804892838593/264500000000000000000000000000000 : ℝ)*base71 + (2957158071341/13225000000000000000000000000 : ℝ)*base73 + (13303083240026661407/264500000000000000000000000000000 : ℝ)*base76 + (1572449878366161407/264500000000000000000000000000000 : ℝ)*base78 + (3305085431801838593/264500000000000000000000000000000 : ℝ)*base79 + (18457829773521/3306250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1056809/250000000000000000000 : ℝ)*base89 + (1056809/250000000000000000000 : ℝ)*base91 + (1056809/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1215_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1215_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1215_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1215_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1215_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1215_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1215_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

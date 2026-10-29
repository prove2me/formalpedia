-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1468_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:09:31.604019+00:00
-- url     : https://prove2.me/submissions/182df35e-1417-4d7c-a73f-80fa6c0e1702

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
theorem support_rectangle_w1468_s0_0 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1733514347/10000000000 : ℝ)*x 0 + (297375971/500000000 : ℝ)*x 1 + (1209012361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1733514347/10000000000 : ℝ)^4433 ≤ (2048073027239/20000000000000 : ℝ)^3409 := by
    have hnat : (1733514347 : ℕ)^4433*20000000000000^3409 ≤ 2048073027239^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733514347 10000000000 2048073027239 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297375971/500000000 : ℝ)^4433 ≤ (25440203337447/50000000000000 : ℝ)^3409 := by
    have hnat : (297375971 : ℕ)^4433*50000000000000^3409 ≤ 25440203337447^3409*500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297375971 500000000 25440203337447 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209012361/2500000000 : ℝ)^4433 ≤ (9719807043771/25000000000000 : ℝ)^3409 := by
    have hnat : (1209012361 : ℕ)^4433*25000000000000^3409 ≤ 9719807043771^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209012361 2500000000 9719807043771 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1733514347/10000000000 : ℝ), (297375971/500000000 : ℝ), (1209012361/2500000000 : ℝ)] ![(2048073027239/20000000000000 : ℝ), (25440203337447/50000000000000 : ℝ), (9719807043771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1733514347/10000000000 : ℝ)|^4433 ≤ (2048073027239/20000000000000 : ℝ)^3409
        have hw : |(-1733514347/10000000000 : ℝ)|=(1733514347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(297375971/500000000 : ℝ)|^4433 ≤ (25440203337447/50000000000000 : ℝ)^3409
        have hw : |(297375971/500000000 : ℝ)|=(297375971/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1209012361/2500000000 : ℝ)|^4433 ≤ (9719807043771/25000000000000 : ℝ)^3409
        have hw : |(1209012361/2500000000 : ℝ)|=(1209012361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s0_1 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2743806843/5000000000 : ℝ)*x 0 + (-1180072533/5000000000 : ℝ)*x 1 + (967209893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2743806843/5000000000 : ℝ)^4433 ≤ (45824655141943/100000000000000 : ℝ)^3409 := by
    have hnat : (2743806843 : ℕ)^4433*100000000000000^3409 ≤ 45824655141943^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743806843 5000000000 45824655141943 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1180072533/5000000000 : ℝ)^4433 ≤ (15296116447699/100000000000000 : ℝ)^3409 := by
    have hnat : (1180072533 : ℕ)^4433*100000000000000^3409 ≤ 15296116447699^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180072533 5000000000 15296116447699 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967209893/2000000000 : ℝ)^4433 ≤ (19439614197313/50000000000000 : ℝ)^3409 := by
    have hnat : (967209893 : ℕ)^4433*50000000000000^3409 ≤ 19439614197313^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967209893 2000000000 19439614197313 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2743806843/5000000000 : ℝ), (-1180072533/5000000000 : ℝ), (967209893/2000000000 : ℝ)] ![(45824655141943/100000000000000 : ℝ), (15296116447699/100000000000000 : ℝ), (19439614197313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2743806843/5000000000 : ℝ)|^4433 ≤ (45824655141943/100000000000000 : ℝ)^3409
        have hw : |(2743806843/5000000000 : ℝ)|=(2743806843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1180072533/5000000000 : ℝ)|^4433 ≤ (15296116447699/100000000000000 : ℝ)^3409
        have hw : |(-1180072533/5000000000 : ℝ)|=(1180072533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967209893/2000000000 : ℝ)|^4433 ≤ (19439614197313/50000000000000 : ℝ)^3409
        have hw : |(967209893/2000000000 : ℝ)|=(967209893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s0_2 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2743807153/5000000000 : ℝ)*x 0 + (193441983/400000000 : ℝ)*x 1 + (-236014413/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2743807153/5000000000 : ℝ)^4433 ≤ (4582466187447/10000000000000 : ℝ)^3409 := by
    have hnat : (2743807153 : ℕ)^4433*10000000000000^3409 ≤ 4582466187447^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743807153 5000000000 4582466187447 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193441983/400000000 : ℝ)^4433 ≤ (19439614772303/50000000000000 : ℝ)^3409 := by
    have hnat : (193441983 : ℕ)^4433*50000000000000^3409 ≤ 19439614772303^3409*400000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193441983 400000000 19439614772303 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236014413/1000000000 : ℝ)^4433 ≤ (15296108559297/100000000000000 : ℝ)^3409 := by
    have hnat : (236014413 : ℕ)^4433*100000000000000^3409 ≤ 15296108559297^3409*1000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236014413 1000000000 15296108559297 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2743807153/5000000000 : ℝ), (193441983/400000000 : ℝ), (-236014413/1000000000 : ℝ)] ![(4582466187447/10000000000000 : ℝ), (19439614772303/50000000000000 : ℝ), (15296108559297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2743807153/5000000000 : ℝ)|^4433 ≤ (4582466187447/10000000000000 : ℝ)^3409
        have hw : |(2743807153/5000000000 : ℝ)|=(2743807153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193441983/400000000 : ℝ)|^4433 ≤ (19439614772303/50000000000000 : ℝ)^3409
        have hw : |(193441983/400000000 : ℝ)|=(193441983/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-236014413/1000000000 : ℝ)|^4433 ≤ (15296108559297/100000000000000 : ℝ)^3409
        have hw : |(-236014413/1000000000 : ℝ)|=(236014413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s0_3 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2078613873/5000000000 : ℝ)*x 0 + (3091811629/10000000000 : ℝ)*x 1 + (1106845153/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078613873/5000000000 : ℝ)^4433 ≤ (31937402793641/100000000000000 : ℝ)^3409 := by
    have hnat : (2078613873 : ℕ)^4433*100000000000000^3409 ≤ 31937402793641^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078613873 5000000000 31937402793641 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091811629/10000000000 : ℝ)^4433 ≤ (21731141029801/100000000000000 : ℝ)^3409 := by
    have hnat : (3091811629 : ℕ)^4433*100000000000000^3409 ≤ 21731141029801^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091811629 10000000000 21731141029801 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106845153/2000000000 : ℝ)^4433 ≤ (1853258246223/4000000000000 : ℝ)^3409 := by
    have hnat : (1106845153 : ℕ)^4433*4000000000000^3409 ≤ 1853258246223^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106845153 2000000000 1853258246223 4000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2078613873/5000000000 : ℝ), (3091811629/10000000000 : ℝ), (1106845153/2000000000 : ℝ)] ![(31937402793641/100000000000000 : ℝ), (21731141029801/100000000000000 : ℝ), (1853258246223/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2078613873/5000000000 : ℝ)|^4433 ≤ (31937402793641/100000000000000 : ℝ)^3409
        have hw : |(2078613873/5000000000 : ℝ)|=(2078613873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091811629/10000000000 : ℝ)|^4433 ≤ (21731141029801/100000000000000 : ℝ)^3409
        have hw : |(3091811629/10000000000 : ℝ)|=(3091811629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1106845153/2000000000 : ℝ)|^4433 ≤ (1853258246223/4000000000000 : ℝ)^3409
        have hw : |(1106845153/2000000000 : ℝ)|=(1106845153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s0_4 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-868714103/5000000000 : ℝ)*x 0 + (4864619967/10000000000 : ℝ)*x 1 + (1479480211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868714103/5000000000 : ℝ)^4433 ≤ (1283805064083/12500000000000 : ℝ)^3409 := by
    have hnat : (868714103 : ℕ)^4433*12500000000000^3409 ≤ 1283805064083^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868714103 5000000000 1283805064083 12500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4864619967/10000000000 : ℝ)^4433 ≤ (39178179493/100000000000 : ℝ)^3409 := by
    have hnat : (4864619967 : ℕ)^4433*100000000000^3409 ≤ 39178179493^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4864619967 10000000000 39178179493 100000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1479480211/2500000000 : ℝ)^4433 ≤ (50551379973761/100000000000000 : ℝ)^3409 := by
    have hnat : (1479480211 : ℕ)^4433*100000000000000^3409 ≤ 50551379973761^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479480211 2500000000 50551379973761 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-868714103/5000000000 : ℝ), (4864619967/10000000000 : ℝ), (1479480211/2500000000 : ℝ)] ![(1283805064083/12500000000000 : ℝ), (39178179493/100000000000 : ℝ), (50551379973761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-868714103/5000000000 : ℝ)|^4433 ≤ (1283805064083/12500000000000 : ℝ)^3409
        have hw : |(-868714103/5000000000 : ℝ)|=(868714103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4864619967/10000000000 : ℝ)|^4433 ≤ (39178179493/100000000000 : ℝ)^3409
        have hw : |(4864619967/10000000000 : ℝ)|=(4864619967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1479480211/2500000000 : ℝ)|^4433 ≤ (50551379973761/100000000000000 : ℝ)^3409
        have hw : |(1479480211/2500000000 : ℝ)|=(1479480211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s0_5 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296054247/2500000000 : ℝ)*x 0 + (-639136369/5000000000 : ℝ)*x 1 + (1479480241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296054247/2500000000 : ℝ)^4433 ≤ (21278907306361/50000000000000 : ℝ)^3409 := by
    have hnat : (1296054247 : ℕ)^4433*50000000000000^3409 ≤ 21278907306361^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296054247 2500000000 21278907306361 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639136369/5000000000 : ℝ)^4433 ≤ (1378160813597/20000000000000 : ℝ)^3409 := by
    have hnat : (639136369 : ℕ)^4433*20000000000000^3409 ≤ 1378160813597^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639136369 5000000000 1378160813597 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1479480241/2500000000 : ℝ)^4433 ≤ (50551381306717/100000000000000 : ℝ)^3409 := by
    have hnat : (1479480241 : ℕ)^4433*100000000000000^3409 ≤ 50551381306717^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479480241 2500000000 50551381306717 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296054247/2500000000 : ℝ), (-639136369/5000000000 : ℝ), (1479480241/2500000000 : ℝ)] ![(21278907306361/50000000000000 : ℝ), (1378160813597/20000000000000 : ℝ), (50551381306717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296054247/2500000000 : ℝ)|^4433 ≤ (21278907306361/50000000000000 : ℝ)^3409
        have hw : |(1296054247/2500000000 : ℝ)|=(1296054247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-639136369/5000000000 : ℝ)|^4433 ≤ (1378160813597/20000000000000 : ℝ)^3409
        have hw : |(-639136369/5000000000 : ℝ)|=(639136369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1479480241/2500000000 : ℝ)|^4433 ≤ (50551381306717/100000000000000 : ℝ)^3409
        have hw : |(1479480241/2500000000 : ℝ)|=(1479480241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s0_6 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324013557/625000000 : ℝ)*x 0 + (5917920843/10000000000 : ℝ)*x 1 + (-255654609/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324013557/625000000 : ℝ)^4433 ≤ (2659863362589/6250000000000 : ℝ)^3409 := by
    have hnat : (324013557 : ℕ)^4433*6250000000000^3409 ≤ 2659863362589^3409*625000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324013557 625000000 2659863362589 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5917920843/10000000000 : ℝ)^4433 ≤ (50551379962653/100000000000000 : ℝ)^3409 := by
    have hnat : (5917920843 : ℕ)^4433*100000000000000^3409 ≤ 50551379962653^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5917920843 10000000000 50551379962653 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255654609/2000000000 : ℝ)^4433 ≤ (6890806220051/100000000000000 : ℝ)^3409 := by
    have hnat : (255654609 : ℕ)^4433*100000000000000^3409 ≤ 6890806220051^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255654609 2000000000 6890806220051 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324013557/625000000 : ℝ), (5917920843/10000000000 : ℝ), (-255654609/2000000000 : ℝ)] ![(2659863362589/6250000000000 : ℝ), (50551379962653/100000000000000 : ℝ), (6890806220051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324013557/625000000 : ℝ)|^4433 ≤ (2659863362589/6250000000000 : ℝ)^3409
        have hw : |(324013557/625000000 : ℝ)|=(324013557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5917920843/10000000000 : ℝ)|^4433 ≤ (50551379962653/100000000000000 : ℝ)^3409
        have hw : |(5917920843/10000000000 : ℝ)|=(5917920843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255654609/2000000000 : ℝ)|^4433 ≤ (6890806220051/100000000000000 : ℝ)^3409
        have hw : |(-255654609/2000000000 : ℝ)|=(255654609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s0_7 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2082915393/5000000000 : ℝ)*x 0 + (1094288437/2000000000 : ℝ)*x 1 + (157842747/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082915393/5000000000 : ℝ)^4433 ≤ (32023374064467/100000000000000 : ℝ)^3409 := by
    have hnat : (2082915393 : ℕ)^4433*100000000000000^3409 ≤ 32023374064467^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082915393 5000000000 32023374064467 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094288437/2000000000 : ℝ)^4433 ≤ (2853070498421/6250000000000 : ℝ)^3409 := by
    have hnat : (1094288437 : ℕ)^4433*6250000000000^3409 ≤ 2853070498421^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094288437 2000000000 2853070498421 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157842747/500000000 : ℝ)^4433 ≤ (1395468621447/6250000000000 : ℝ)^3409 := by
    have hnat : (157842747 : ℕ)^4433*6250000000000^3409 ≤ 1395468621447^3409*500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157842747 500000000 1395468621447 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082915393/5000000000 : ℝ), (1094288437/2000000000 : ℝ), (157842747/500000000 : ℝ)] ![(32023374064467/100000000000000 : ℝ), (2853070498421/6250000000000 : ℝ), (1395468621447/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082915393/5000000000 : ℝ)|^4433 ≤ (32023374064467/100000000000000 : ℝ)^3409
        have hw : |(2082915393/5000000000 : ℝ)|=(2082915393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094288437/2000000000 : ℝ)|^4433 ≤ (2853070498421/6250000000000 : ℝ)^3409
        have hw : |(1094288437/2000000000 : ℝ)|=(1094288437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157842747/500000000 : ℝ)|^4433 ≤ (1395468621447/6250000000000 : ℝ)^3409
        have hw : |(157842747/500000000 : ℝ)|=(157842747/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1468_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13033/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4431/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4431 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4431*1^1024 ≤ 0^1024*1^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4431/1024 : ℝ) ≤ (379388802671340333/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4431 ≤ (379388802671340333/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4431*20000000000000000000^1024 ≤ 379388802671340333^1024*5^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 379388802671340333 20000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (379388802671340333/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4431 := by
      have hnat : (1 : ℕ)^1024*1^4431 ≤ 1^4431*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20379388802671340333/20000000000000000000 : ℝ) ≤ (5021761013276543/5000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (20379388802671340333/20000000000000000000 : ℝ)^1024 ≤ (5021761013276543/5000000000000000 : ℝ)^4431 := by
      have hnat : (20379388802671340333 : ℕ)^1024*5000000000000000^4431 ≤ 5021761013276543^4431*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20379388802671340333 20000000000000000000 5021761013276543 5000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5021761013276543/5000000000000000 : ℝ)) (X := (20379388802671340333/20000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10379388802671340333/10000000000000000000 : ℝ) ≤ (2521761013276543/2500000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (10379388802671340333/10000000000000000000 : ℝ)^1024 ≤ (2521761013276543/2500000000000000 : ℝ)^4431 := by
      have hnat : (10379388802671340333 : ℕ)^1024*2500000000000000^4431 ≤ 2521761013276543^4431*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10379388802671340333 10000000000000000000 2521761013276543 2500000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2521761013276543/2500000000000000 : ℝ)) (X := (10379388802671340333/10000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(21761013276543/2000000000000000 : ℝ)*(0 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21761013276543/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(379388802671340333/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(21761013276543/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4431/1024 : ℝ) := by
    rw [show (1 : ℝ)+(21761013276543/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5021761013276543/5000000000000000 : ℝ) by norm_num, show 1+(379388802671340333/20000000000000000000 : ℝ)+(0 : ℝ)=(20379388802671340333/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(379388802671340333/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(21761013276543/2000000000000000 : ℝ)*(2/5 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(21761013276543/2000000000000000 : ℝ)*(2/5 : ℝ)=(2521761013276543/2500000000000000 : ℝ) by norm_num, show 1+2*(379388802671340333/20000000000000000000 : ℝ)=(10379388802671340333/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(21761013276543/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21761013276543/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(21761013276543/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21761013276543/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(21761013276543/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (21761013276543/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1733514347/10000000000 : ℝ)*X 0 0+(297375971/500000000 : ℝ)*X 0 1+(1209012361/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2743806843/5000000000 : ℝ)*X 1 0+(-1180072533/5000000000 : ℝ)*X 1 1+(967209893/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2743807153/5000000000 : ℝ)*X 2 0+(193441983/400000000 : ℝ)*X 2 1+(-236014413/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2078613873/5000000000 : ℝ)*X 0 0+(3091811629/10000000000 : ℝ)*X 0 1+(1106845153/2000000000 : ℝ)*X 0 2+(2078613873/5000000000 : ℝ)*X 1 0+(3091811629/10000000000 : ℝ)*X 1 1+(1106845153/2000000000 : ℝ)*X 1 2+(2078613873/5000000000 : ℝ)*X 2 0+(3091811629/10000000000 : ℝ)*X 2 1+(1106845153/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-868714103/5000000000 : ℝ)*X 0 0+(4864619967/10000000000 : ℝ)*X 0 1+(1479480211/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1296054247/2500000000 : ℝ)*X 1 0+(-639136369/5000000000 : ℝ)*X 1 1+(1479480241/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((324013557/625000000 : ℝ)*X 2 0+(5917920843/10000000000 : ℝ)*X 2 1+(-255654609/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2082915393/5000000000 : ℝ)*X 0 0+(1094288437/2000000000 : ℝ)*X 0 1+(157842747/500000000 : ℝ)*X 0 2+(2082915393/5000000000 : ℝ)*X 1 0+(1094288437/2000000000 : ℝ)*X 1 1+(157842747/500000000 : ℝ)*X 1 2+(2082915393/5000000000 : ℝ)*X 2 0+(1094288437/2000000000 : ℝ)*X 2 1+(157842747/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (148662384201298836365709/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (588392861/100000000000000 : ℝ)*(base19) + (552302031/100000000000000 : ℝ)*(base23) + (114633/1000000000000 : ℝ)*(upper3) + (18896859/25000000000000 : ℝ)*(upper4) + (43361587/25000000000000 : ℝ)*(upper5) + (654573168801521/100000000000000 : ℝ)*(major0) + (654573168801521/100000000000000 : ℝ)*(major1) + (654573168801521/100000000000000 : ℝ)*(major2) + (179942090985887/20000000000000 : ℝ)*(sp0) + (899712586538797/100000000000000 : ℝ)*(sp1) + (899712622629627/100000000000000 : ℝ)*(sp2) + (409432196500953/100000000000000 : ℝ)*(sp3) + (2720002223/100000000000000 : ℝ)*(sp4) + (916616299/100000000000000 : ℝ)*(sp7) + (102358278279313/25000000000000 : ℝ)*(f.failure) + (449856587465829/50000000000000 : ℝ)*(f.sum) + (97541054878097/100000000000000000000000000000 : ℝ)*base66 + (903826633421903/200000000000000000000000000000 : ℝ)*base67 + (265547639378097/200000000000000000000000000000 : ℝ)*base70 + (286839086778097/200000000000000000000000000000 : ℝ)*base72 + (156217637021903/100000000000000000000000000000 : ℝ)*base73 + (1129537710021903/200000000000000000000000000000 : ℝ)*base75 + (22332710778097/200000000000000000000000000000 : ℝ)*base78 + (1033137796621903/200000000000000000000000000000 : ℝ)*base79 + (198697507478097/100000000000000000000000000000 : ℝ)*base82 + (8299167/2500000000000000000000 : ℝ)*base90 + (8299167/2500000000000000000000 : ℝ)*base92 + (8299167/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14078651217066177/3906250000000000000000 : ℝ) := by norm_num
    linear_combination (842060749/100000000000000 : ℝ)*(base19) + (411824479/50000000000000 : ℝ)*(base23) + (19126413/20000000000000 : ℝ)*(base32) + (126681383/100000000000000 : ℝ)*(upper3) + (14040413/20000000000000 : ℝ)*(upper5) + (4316994775763/625000000000 : ℝ)*(major0) + (4316994775763/625000000000 : ℝ)*(major1) + (4316994775763/625000000000 : ℝ)*(major2) + (263949117/12500000000000 : ℝ)*(sp1) + (2034802019/100000000000000 : ℝ)*(sp2) + (927144441079/97656250000 : ℝ)*(sp4) + (949392954011211/100000000000000 : ℝ)*(sp5) + (5933706557587/625000000000 : ℝ)*(sp6) + (432042204809371/100000000000000 : ℝ)*(sp7) + (108010575110359/25000000000000 : ℝ)*(f.failure) + (927144441079/97656250000 : ℝ)*(f.sum) + (252456566441/625000000000000000000000000 : ℝ)*base66 + (5665075243559/1250000000000000000000000000 : ℝ)*base67 + (5407774122309/1250000000000000000000000000 : ℝ)*base69 + (4618855114809/1250000000000000000000000000 : ℝ)*base71 + (64120610051/39062500000000000000000000 : ℝ)*base74 + (12279006097309/1250000000000000000000000000 : ℝ)*base75 + (442050247691/1250000000000000000000000000 : ℝ)*base78 + (6461484822691/1250000000000000000000000000 : ℝ)*base80 + (808031658559/625000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3931719/2500000000000000000000 : ℝ)*base89 + (3931719/2500000000000000000000 : ℝ)*base91 + (3931719/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1468_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1468_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1468_s1_0 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899236171/10000000000 : ℝ)*x 0 + (2800787893/5000000000 : ℝ)*x 1 + (5075667913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899236171/10000000000 : ℝ)^4433 ≤ (5765640501287/50000000000000 : ℝ)^3409 := by
    have hnat : (1899236171 : ℕ)^4433*50000000000000^3409 ≤ 5765640501287^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899236171 10000000000 5765640501287 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2800787893/5000000000 : ℝ)^4433 ≤ (5883250138001/12500000000000 : ℝ)^3409 := by
    have hnat : (2800787893 : ℕ)^4433*12500000000000^3409 ≤ 5883250138001^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800787893 5000000000 5883250138001 12500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5075667913/10000000000 : ℝ)^4433 ≤ (41402717879763/100000000000000 : ℝ)^3409 := by
    have hnat : (5075667913 : ℕ)^4433*100000000000000^3409 ≤ 41402717879763^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075667913 10000000000 41402717879763 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899236171/10000000000 : ℝ), (2800787893/5000000000 : ℝ), (5075667913/10000000000 : ℝ)] ![(5765640501287/50000000000000 : ℝ), (5883250138001/12500000000000 : ℝ), (41402717879763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899236171/10000000000 : ℝ)|^4433 ≤ (5765640501287/50000000000000 : ℝ)^3409
        have hw : |(-1899236171/10000000000 : ℝ)|=(1899236171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2800787893/5000000000 : ℝ)|^4433 ≤ (5883250138001/12500000000000 : ℝ)^3409
        have hw : |(2800787893/5000000000 : ℝ)|=(2800787893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5075667913/10000000000 : ℝ)|^4433 ≤ (41402717879763/100000000000000 : ℝ)^3409
        have hw : |(5075667913/10000000000 : ℝ)|=(5075667913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s1_1 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697424057/5000000000 : ℝ)*x 0 + (-2177783133/10000000000 : ℝ)*x 1 + (5075669293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697424057/5000000000 : ℝ)^4433 ≤ (2801243089097/6250000000000 : ℝ)^3409 := by
    have hnat : (2697424057 : ℕ)^4433*6250000000000^3409 ≤ 2801243089097^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697424057 5000000000 2801243089097 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177783133/10000000000 : ℝ)^4433 ≤ (13777378031789/100000000000000 : ℝ)^3409 := by
    have hnat : (2177783133 : ℕ)^4433*100000000000000^3409 ≤ 13777378031789^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177783133 10000000000 13777378031789 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5075669293/10000000000 : ℝ)^4433 ≤ (41402732517889/100000000000000 : ℝ)^3409 := by
    have hnat : (5075669293 : ℕ)^4433*100000000000000^3409 ≤ 41402732517889^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075669293 10000000000 41402732517889 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697424057/5000000000 : ℝ), (-2177783133/10000000000 : ℝ), (5075669293/10000000000 : ℝ)] ![(2801243089097/6250000000000 : ℝ), (13777378031789/100000000000000 : ℝ), (41402732517889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697424057/5000000000 : ℝ)|^4433 ≤ (2801243089097/6250000000000 : ℝ)^3409
        have hw : |(2697424057/5000000000 : ℝ)|=(2697424057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177783133/10000000000 : ℝ)|^4433 ≤ (13777378031789/100000000000000 : ℝ)^3409
        have hw : |(-2177783133/10000000000 : ℝ)|=(2177783133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5075669293/10000000000 : ℝ)|^4433 ≤ (41402732517889/100000000000000 : ℝ)^3409
        have hw : |(5075669293/10000000000 : ℝ)|=(5075669293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s1_2 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394849279/10000000000 : ℝ)*x 0 + (5075668037/10000000000 : ℝ)*x 1 + (-272222903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394849279/10000000000 : ℝ)^4433 ≤ (44819902011567/100000000000000 : ℝ)^3409 := by
    have hnat : (5394849279 : ℕ)^4433*100000000000000^3409 ≤ 44819902011567^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394849279 10000000000 44819902011567 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075668037/10000000000 : ℝ)^4433 ≤ (41402719195073/100000000000000 : ℝ)^3409 := by
    have hnat : (5075668037 : ℕ)^4433*100000000000000^3409 ≤ 41402719195073^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075668037 10000000000 41402719195073 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272222903/1250000000 : ℝ)^4433 ≤ (13777378780413/100000000000000 : ℝ)^3409 := by
    have hnat : (272222903 : ℕ)^4433*100000000000000^3409 ≤ 13777378780413^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272222903 1250000000 13777378780413 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394849279/10000000000 : ℝ), (5075668037/10000000000 : ℝ), (-272222903/1250000000 : ℝ)] ![(44819902011567/100000000000000 : ℝ), (41402719195073/100000000000000 : ℝ), (13777378780413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394849279/10000000000 : ℝ)|^4433 ≤ (44819902011567/100000000000000 : ℝ)^3409
        have hw : |(5394849279/10000000000 : ℝ)|=(5394849279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075668037/10000000000 : ℝ)|^4433 ≤ (41402719195073/100000000000000 : ℝ)^3409
        have hw : |(5075668037/10000000000 : ℝ)|=(5075668037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272222903/1250000000 : ℝ)|^4433 ≤ (13777378780413/100000000000000 : ℝ)^3409
        have hw : |(-272222903/1250000000 : ℝ)|=(272222903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s1_3 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213280967/500000000 : ℝ)*x 0 + (3722058357/10000000000 : ℝ)*x 1 + (4877717407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213280967/500000000 : ℝ)^4433 ≤ (16512226081639/50000000000000 : ℝ)^3409 := by
    have hnat : (213280967 : ℕ)^4433*50000000000000^3409 ≤ 16512226081639^3409*500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213280967 500000000 16512226081639 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3722058357/10000000000 : ℝ)^4433 ≤ (27660144996051/100000000000000 : ℝ)^3409 := by
    have hnat : (3722058357 : ℕ)^4433*100000000000000^3409 ≤ 27660144996051^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3722058357 10000000000 27660144996051 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4877717407/10000000000 : ℝ)^4433 ≤ (39315402822293/100000000000000 : ℝ)^3409 := by
    have hnat : (4877717407 : ℕ)^4433*100000000000000^3409 ≤ 39315402822293^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4877717407 10000000000 39315402822293 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213280967/500000000 : ℝ), (3722058357/10000000000 : ℝ), (4877717407/10000000000 : ℝ)] ![(16512226081639/50000000000000 : ℝ), (27660144996051/100000000000000 : ℝ), (39315402822293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213280967/500000000 : ℝ)|^4433 ≤ (16512226081639/50000000000000 : ℝ)^3409
        have hw : |(213280967/500000000 : ℝ)|=(213280967/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3722058357/10000000000 : ℝ)|^4433 ≤ (27660144996051/100000000000000 : ℝ)^3409
        have hw : |(3722058357/10000000000 : ℝ)|=(3722058357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4877717407/10000000000 : ℝ)|^4433 ≤ (39315402822293/100000000000000 : ℝ)^3409
        have hw : |(4877717407/10000000000 : ℝ)|=(4877717407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s1_4 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899635017/10000000000 : ℝ)*x 0 + (5081927651/10000000000 : ℝ)*x 1 + (5595208279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899635017/10000000000 : ℝ)^4433 ≤ (360450941113/3125000000000 : ℝ)^3409 := by
    have hnat : (1899635017 : ℕ)^4433*3125000000000^3409 ≤ 360450941113^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899635017 10000000000 360450941113 3125000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5081927651/10000000000 : ℝ)^4433 ≤ (20734564663983/50000000000000 : ℝ)^3409 := by
    have hnat : (5081927651 : ℕ)^4433*50000000000000^3409 ≤ 20734564663983^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081927651 10000000000 20734564663983 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5595208279/10000000000 : ℝ)^4433 ≤ (1879857621733/4000000000000 : ℝ)^3409 := by
    have hnat : (5595208279 : ℕ)^4433*4000000000000^3409 ≤ 1879857621733^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595208279 10000000000 1879857621733 4000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899635017/10000000000 : ℝ), (5081927651/10000000000 : ℝ), (5595208279/10000000000 : ℝ)] ![(360450941113/3125000000000 : ℝ), (20734564663983/50000000000000 : ℝ), (1879857621733/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899635017/10000000000 : ℝ)|^4433 ≤ (360450941113/3125000000000 : ℝ)^3409
        have hw : |(-1899635017/10000000000 : ℝ)|=(1899635017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5081927651/10000000000 : ℝ)|^4433 ≤ (20734564663983/50000000000000 : ℝ)^3409
        have hw : |(5081927651/10000000000 : ℝ)|=(5081927651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5595208279/10000000000 : ℝ)|^4433 ≤ (1879857621733/4000000000000 : ℝ)^3409
        have hw : |(5595208279/10000000000 : ℝ)|=(5595208279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s1_5 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628555373/5000000000 : ℝ)*x 0 + (-1658243871/10000000000 : ℝ)*x 1 + (1119041659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628555373/5000000000 : ℝ)^4433 ≤ (43337591584369/100000000000000 : ℝ)^3409 := by
    have hnat : (2628555373 : ℕ)^4433*100000000000000^3409 ≤ 43337591584369^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628555373 5000000000 43337591584369 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1658243871/10000000000 : ℝ)^4433 ≤ (4832983843913/50000000000000 : ℝ)^3409 := by
    have hnat : (1658243871 : ℕ)^4433*50000000000000^3409 ≤ 4832983843913^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1658243871 10000000000 4832983843913 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119041659/2000000000 : ℝ)^4433 ≤ (11749110179521/25000000000000 : ℝ)^3409 := by
    have hnat : (1119041659 : ℕ)^4433*25000000000000^3409 ≤ 11749110179521^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119041659 2000000000 11749110179521 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628555373/5000000000 : ℝ), (-1658243871/10000000000 : ℝ), (1119041659/2000000000 : ℝ)] ![(43337591584369/100000000000000 : ℝ), (4832983843913/50000000000000 : ℝ), (11749110179521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628555373/5000000000 : ℝ)|^4433 ≤ (43337591584369/100000000000000 : ℝ)^3409
        have hw : |(2628555373/5000000000 : ℝ)|=(2628555373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1658243871/10000000000 : ℝ)|^4433 ≤ (4832983843913/50000000000000 : ℝ)^3409
        have hw : |(-1658243871/10000000000 : ℝ)|=(1658243871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119041659/2000000000 : ℝ)|^4433 ≤ (11749110179521/25000000000000 : ℝ)^3409
        have hw : |(1119041659/2000000000 : ℝ)|=(1119041659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s1_6 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257110811/10000000000 : ℝ)*x 0 + (2797604127/5000000000 : ℝ)*x 1 + (-1658243837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257110811/10000000000 : ℝ)^4433 ≤ (43337592281159/100000000000000 : ℝ)^3409 := by
    have hnat : (5257110811 : ℕ)^4433*100000000000000^3409 ≤ 43337592281159^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257110811 10000000000 43337592281159 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2797604127/5000000000 : ℝ)^4433 ≤ (5874555033783/12500000000000 : ℝ)^3409 := by
    have hnat : (2797604127 : ℕ)^4433*12500000000000^3409 ≤ 5874555033783^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797604127 5000000000 5874555033783 12500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1658243837/10000000000 : ℝ)^4433 ≤ (9665967430107/100000000000000 : ℝ)^3409 := by
    have hnat : (1658243837 : ℕ)^4433*100000000000000^3409 ≤ 9665967430107^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1658243837 10000000000 9665967430107 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257110811/10000000000 : ℝ), (2797604127/5000000000 : ℝ), (-1658243837/10000000000 : ℝ)] ![(43337592281159/100000000000000 : ℝ), (5874555033783/12500000000000 : ℝ), (9665967430107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257110811/10000000000 : ℝ)|^4433 ≤ (43337592281159/100000000000000 : ℝ)^3409
        have hw : |(5257110811/10000000000 : ℝ)|=(5257110811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2797604127/5000000000 : ℝ)|^4433 ≤ (5874555033783/12500000000000 : ℝ)^3409
        have hw : |(2797604127/5000000000 : ℝ)|=(2797604127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1658243837/10000000000 : ℝ)|^4433 ≤ (9665967430107/100000000000000 : ℝ)^3409
        have hw : |(-1658243837/10000000000 : ℝ)|=(1658243837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s1_7 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213324817/500000000 : ℝ)*x 0 + (4863962997/10000000000 : ℝ)*x 1 + (1868024337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213324817/500000000 : ℝ)^4433 ≤ (33033281686603/100000000000000 : ℝ)^3409 := by
    have hnat : (213324817 : ℕ)^4433*100000000000000^3409 ≤ 33033281686603^3409*500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213324817 500000000 33033281686603 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4863962997/10000000000 : ℝ)^4433 ≤ (39171299265597/100000000000000 : ℝ)^3409 := by
    have hnat : (4863962997 : ℕ)^4433*100000000000000^3409 ≤ 39171299265597^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4863962997 10000000000 39171299265597 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1868024337/5000000000 : ℝ)^4433 ≤ (347442737903/1250000000000 : ℝ)^3409 := by
    have hnat : (1868024337 : ℕ)^4433*1250000000000^3409 ≤ 347442737903^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868024337 5000000000 347442737903 1250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213324817/500000000 : ℝ), (4863962997/10000000000 : ℝ), (1868024337/5000000000 : ℝ)] ![(33033281686603/100000000000000 : ℝ), (39171299265597/100000000000000 : ℝ), (347442737903/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213324817/500000000 : ℝ)|^4433 ≤ (33033281686603/100000000000000 : ℝ)^3409
        have hw : |(213324817/500000000 : ℝ)|=(213324817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4863962997/10000000000 : ℝ)|^4433 ≤ (39171299265597/100000000000000 : ℝ)^3409
        have hw : |(4863962997/10000000000 : ℝ)|=(4863962997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1868024337/5000000000 : ℝ)|^4433 ≤ (347442737903/1250000000000 : ℝ)^3409
        have hw : |(1868024337/5000000000 : ℝ)|=(1868024337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1468_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3863/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9421/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2243/100000 : ℝ) ^ (4431/1024 : ℝ) ≤ (730791467491/10000000000000000000 : ℝ) := by
    have hpowers : (2243/100000 : ℝ)^4431 ≤ (730791467491/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2243 : ℕ)^4431*10000000000000000000^1024 ≤ 730791467491^1024*100000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2243 100000 730791467491 10000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2243/100000 : ℝ)) (X := (730791467491/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13033/50000 : ℝ) ^ (4431/1024 : ℝ) ≤ (2973495003449509/1000000000000000000 : ℝ) := by
    have hpowers : (13033/50000 : ℝ)^4431 ≤ (2973495003449509/1000000000000000000 : ℝ)^1024 := by
      have hnat : (13033 : ℕ)^4431*1000000000000000000^1024 ≤ 2973495003449509^1024*50000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13033 50000 2973495003449509 1000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13033/50000 : ℝ)) (X := (2973495003449509/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000730791467491/5000000000000000000 : ℝ) ≤ (2000000067554089/2000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (5000000730791467491/5000000000000000000 : ℝ)^1024 ≤ (2000000067554089/2000000000000000 : ℝ)^4431 := by
      have hnat : (5000000730791467491 : ℕ)^1024*2000000000000000^4431 ≤ 2000000067554089^4431*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000730791467491 5000000000000000000 2000000067554089 2000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000067554089/2000000000000000 : ℝ)) (X := (5000000730791467491/5000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10029735680825962581/10000000000000000000 : ℝ) ≤ (5003432023099291/5000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (10029735680825962581/10000000000000000000 : ℝ)^1024 ≤ (5003432023099291/5000000000000000 : ℝ)^4431 := by
      have hnat : (10029735680825962581 : ℕ)^1024*5000000000000000^4431 ≤ 5003432023099291^4431*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10029735680825962581 10000000000000000000 5003432023099291 5000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003432023099291/5000000000000000 : ℝ)) (X := (10029735680825962581/10000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (502973495003449509/500000000000000000 : ℝ) ≤ (10013727754626719/10000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (502973495003449509/500000000000000000 : ℝ)^1024 ≤ (10013727754626719/10000000000000000 : ℝ)^4431 := by
      have hnat : (502973495003449509 : ℕ)^1024*10000000000000000^4431 ≤ 10013727754626719^4431*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        502973495003449509 500000000000000000 10013727754626719 10000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013727754626719/10000000000000000 : ℝ)) (X := (502973495003449509/500000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(730791467491/10000000000000000000 : ℝ) ≤ ((26466579716744076517/26470000000000000000 : ℝ)+2*(762634269793/264700000000000 : ℝ)*(2243/100000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (26466579716744076517/26470000000000000000 : ℝ)+2*(762634269793/264700000000000 : ℝ)*(2243/100000 : ℝ)=(2000000067554089/2000000000000000 : ℝ) by norm_num, show 1+2*(730791467491/10000000000000000000 : ℝ)=(5000000730791467491/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2973495003449509/1000000000000000000 : ℝ)+(730791467491/10000000000000000000 : ℝ) ≤ ((26466579716744076517/26470000000000000000 : ℝ)+(762634269793/264700000000000 : ℝ)*((13033/50000 : ℝ)+(2243/100000 : ℝ)))^(4431/1024 : ℝ) := by
    rw [show (26466579716744076517/26470000000000000000 : ℝ)+(762634269793/264700000000000 : ℝ)*((13033/50000 : ℝ)+(2243/100000 : ℝ))=(5003432023099291/5000000000000000 : ℝ) by norm_num, show 1+(2973495003449509/1000000000000000000 : ℝ)+(730791467491/10000000000000000000 : ℝ)=(10029735680825962581/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2973495003449509/1000000000000000000 : ℝ) ≤ ((26466579716744076517/26470000000000000000 : ℝ)+2*(762634269793/264700000000000 : ℝ)*(13033/50000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (26466579716744076517/26470000000000000000 : ℝ)+2*(762634269793/264700000000000 : ℝ)*(13033/50000 : ℝ)=(10013727754626719/10000000000000000 : ℝ) by norm_num, show 1+2*(2973495003449509/1000000000000000000 : ℝ)=(502973495003449509/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26466579716744076517/26470000000000000000 : ℝ)*(X 1 0+X 2 0)+(762634269793/264700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (2243/100000 : ℝ)) (hi := (13033/50000 : ℝ)) (c := (26466579716744076517/26470000000000000000 : ℝ)) (alpha := (762634269793/264700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26466579716744076517/26470000000000000000 : ℝ)*(X 0 1+X 2 1)+(762634269793/264700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (2243/100000 : ℝ)) (hi := (13033/50000 : ℝ)) (c := (26466579716744076517/26470000000000000000 : ℝ)) (alpha := (762634269793/264700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26466579716744076517/26470000000000000000 : ℝ)*(X 0 2+X 1 2)+(762634269793/264700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (2243/100000 : ℝ)) (hi := (13033/50000 : ℝ)) (c := (26466579716744076517/26470000000000000000 : ℝ)) (alpha := (762634269793/264700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1899236171/10000000000 : ℝ)*X 0 0+(2800787893/5000000000 : ℝ)*X 0 1+(5075667913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2697424057/5000000000 : ℝ)*X 1 0+(-2177783133/10000000000 : ℝ)*X 1 1+(5075669293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5394849279/10000000000 : ℝ)*X 2 0+(5075668037/10000000000 : ℝ)*X 2 1+(-272222903/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((213280967/500000000 : ℝ)*X 0 0+(3722058357/10000000000 : ℝ)*X 0 1+(4877717407/10000000000 : ℝ)*X 0 2+(213280967/500000000 : ℝ)*X 1 0+(3722058357/10000000000 : ℝ)*X 1 1+(4877717407/10000000000 : ℝ)*X 1 2+(213280967/500000000 : ℝ)*X 2 0+(3722058357/10000000000 : ℝ)*X 2 1+(4877717407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1899635017/10000000000 : ℝ)*X 0 0+(5081927651/10000000000 : ℝ)*X 0 1+(5595208279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628555373/5000000000 : ℝ)*X 1 0+(-1658243871/10000000000 : ℝ)*X 1 1+(1119041659/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257110811/10000000000 : ℝ)*X 2 0+(2797604127/5000000000 : ℝ)*X 2 1+(-1658243837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((213324817/500000000 : ℝ)*X 0 0+(4863962997/10000000000 : ℝ)*X 0 1+(1868024337/5000000000 : ℝ)*X 0 2+(213324817/500000000 : ℝ)*X 1 0+(4863962997/10000000000 : ℝ)*X 1 1+(1868024337/5000000000 : ℝ)*X 1 2+(213324817/500000000 : ℝ)*X 2 0+(4863962997/10000000000 : ℝ)*X 2 1+(1868024337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113300610297217392783031917/66175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38348751/20000000000000 : ℝ)*(base19) + (529029107/100000000000000 : ℝ)*(base23) + (1160599/50000000000000 : ℝ)*(upper2) + (20941967/50000000000000 : ℝ)*(upper4) + (6417727/100000000000000 : ℝ)*(lower5) + (69169916602067/5000000000000 : ℝ)*(major0) + (69169916602067/5000000000000 : ℝ)*(major1) + (69169916602067/5000000000000 : ℝ)*(major2) + (475369790710431/25000000000000 : ℝ)*(sp0) + (950742919603983/50000000000000 : ℝ)*(sp1) + (1901485501922613/100000000000000 : ℝ)*(sp2) + (865308551180383/100000000000000 : ℝ)*(sp3) + (6868109997/100000000000000 : ℝ)*(sp4) + (2024879367/100000000000000 : ℝ)*(sp7) + (3461242304239/400000000000 : ℝ)*(f.failure) + (47537150773793/2500000000000 : ℝ)*(f.sum) + (3569056765057/529400000000000000000000000 : ℝ)*base66 + (386752123619889361/132350000000000000000000000000000 : ℝ)*base68 + (56992587858560639/132350000000000000000000000000000 : ℝ)*base69 + (377088506709939361/132350000000000000000000000000000 : ℝ)*base72 + (267531944291/132350000000000000000000000 : ℝ)*base74 + (176700568359489361/132350000000000000000000000000000 : ℝ)*base76 + (274910323371989361/132350000000000000000000000000000 : ℝ)*base78 + (555725650640610639/132350000000000000000000000000000 : ℝ)*base79 + (808781936449/529400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (120799/40000000000000000000 : ℝ)*base89 + (120799/40000000000000000000 : ℝ)*base91 + (120799/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1780043552380529701065414963/165437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2047386213/100000000000000 : ℝ)*(base19) + (1109139593/50000000000000 : ℝ)*(base23) + (273779361/100000000000000 : ℝ)*(upper3) + (60731041/100000000000000 : ℝ)*(lower4) + (121221447/50000000000000 : ℝ)*(upper5) + (354355478446687/25000000000000 : ℝ)*(major0) + (354355478446687/25000000000000 : ℝ)*(major1) + (354355478446687/25000000000000 : ℝ)*(major2) + (1518579017/12500000000000 : ℝ)*(sp1) + (13342512959/100000000000000 : ℝ)*(sp2) + (1948251267432309/100000000000000 : ℝ)*(sp4) + (48705926785349/2500000000000 : ℝ)*(sp5) + (389647141328033/20000000000000 : ℝ)*(sp6) + (221648050371849/25000000000000 : ℝ)*(sp7) + (221648050371849/25000000000000 : ℝ)*(f.failure) + (1948251267432309/100000000000000 : ℝ)*(f.sum) + (28922956028781/13235000000000000000000000000 : ℝ)*base66 + (3997776939702999179/661750000000000000000000000000000 : ℝ)*base67 + (8605451434660999179/661750000000000000000000000000000 : ℝ)*base69 + (226613024840249179/661750000000000000000000000000000 : ℝ)*base71 + (4158468651/12924804687500000000000000 : ℝ)*base73 + (6864974926526249179/661750000000000000000000000000000 : ℝ)*base75 + (1743460021674249179/661750000000000000000000000000000 : ℝ)*base77 + (100200749896500821/661750000000000000000000000000000 : ℝ)*base80 + (60860192328159/13235000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (19577191/2500000000000000000000 : ℝ)*base90 + (19577191/2500000000000000000000 : ℝ)*base92 + (19577191/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1468_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3863/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9421/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1468_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1468_s2_0 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-964641069/5000000000 : ℝ)*x 0 + (1368366989/2500000000 : ℝ)*x 1 + (5184405569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (964641069/5000000000 : ℝ)^4433 ≤ (5884532437249/50000000000000 : ℝ)^3409 := by
    have hnat : (964641069 : ℕ)^4433*50000000000000^3409 ≤ 5884532437249^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964641069 5000000000 5884532437249 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368366989/2500000000 : ℝ)^4433 ≤ (11417776844511/25000000000000 : ℝ)^3409 := by
    have hnat : (1368366989 : ℕ)^4433*25000000000000^3409 ≤ 11417776844511^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368366989 2500000000 11417776844511 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184405569/10000000000 : ℝ)^4433 ≤ (2659989232577/6250000000000 : ℝ)^3409 := by
    have hnat : (5184405569 : ℕ)^4433*6250000000000^3409 ≤ 2659989232577^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184405569 10000000000 2659989232577 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-964641069/5000000000 : ℝ), (1368366989/2500000000 : ℝ), (5184405569/10000000000 : ℝ)] ![(5884532437249/50000000000000 : ℝ), (11417776844511/25000000000000 : ℝ), (2659989232577/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-964641069/5000000000 : ℝ)|^4433 ≤ (5884532437249/50000000000000 : ℝ)^3409
        have hw : |(-964641069/5000000000 : ℝ)|=(964641069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368366989/2500000000 : ℝ)|^4433 ≤ (11417776844511/25000000000000 : ℝ)^3409
        have hw : |(1368366989/2500000000 : ℝ)|=(1368366989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184405569/10000000000 : ℝ)|^4433 ≤ (2659989232577/6250000000000 : ℝ)^3409
        have hw : |(5184405569/10000000000 : ℝ)|=(5184405569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s2_1 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670346971/1250000000 : ℝ)*x 0 + (-415704603/2000000000 : ℝ)*x 1 + (5184406879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670346971/1250000000 : ℝ)^4433 ≤ (22236853693727/50000000000000 : ℝ)^3409 := by
    have hnat : (670346971 : ℕ)^4433*50000000000000^3409 ≤ 22236853693727^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670346971 1250000000 22236853693727 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415704603/2000000000 : ℝ)^4433 ≤ (6483225441379/50000000000000 : ℝ)^3409 := by
    have hnat : (415704603 : ℕ)^4433*50000000000000^3409 ≤ 6483225441379^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415704603 2000000000 6483225441379 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184406879/10000000000 : ℝ)^4433 ≤ (42559841705603/100000000000000 : ℝ)^3409 := by
    have hnat : (5184406879 : ℕ)^4433*100000000000000^3409 ≤ 42559841705603^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184406879 10000000000 42559841705603 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670346971/1250000000 : ℝ), (-415704603/2000000000 : ℝ), (5184406879/10000000000 : ℝ)] ![(22236853693727/50000000000000 : ℝ), (6483225441379/50000000000000 : ℝ), (42559841705603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670346971/1250000000 : ℝ)|^4433 ≤ (22236853693727/50000000000000 : ℝ)^3409
        have hw : |(670346971/1250000000 : ℝ)|=(670346971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415704603/2000000000 : ℝ)|^4433 ≤ (6483225441379/50000000000000 : ℝ)^3409
        have hw : |(-415704603/2000000000 : ℝ)|=(415704603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184406879/10000000000 : ℝ)|^4433 ≤ (42559841705603/100000000000000 : ℝ)^3409
        have hw : |(5184406879/10000000000 : ℝ)|=(5184406879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s2_2 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536277663/1000000000 : ℝ)*x 0 + (2592203081/5000000000 : ℝ)*x 1 + (-1039261407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536277663/1000000000 : ℝ)^4433 ≤ (277960729271/625000000000 : ℝ)^3409 := by
    have hnat : (536277663 : ℕ)^4433*625000000000^3409 ≤ 277960729271^3409*1000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536277663 1000000000 277960729271 625000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592203081/5000000000 : ℝ)^4433 ≤ (42559834051561/100000000000000 : ℝ)^3409 := by
    have hnat : (2592203081 : ℕ)^4433*100000000000000^3409 ≤ 42559834051561^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592203081 5000000000 42559834051561 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039261407/5000000000 : ℝ)^4433 ≤ (3241612313053/25000000000000 : ℝ)^3409 := by
    have hnat : (1039261407 : ℕ)^4433*25000000000000^3409 ≤ 3241612313053^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039261407 5000000000 3241612313053 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536277663/1000000000 : ℝ), (2592203081/5000000000 : ℝ), (-1039261407/5000000000 : ℝ)] ![(277960729271/625000000000 : ℝ), (42559834051561/100000000000000 : ℝ), (3241612313053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536277663/1000000000 : ℝ)|^4433 ≤ (277960729271/625000000000 : ℝ)^3409
        have hw : |(536277663/1000000000 : ℝ)|=(536277663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592203081/5000000000 : ℝ)|^4433 ≤ (42559834051561/100000000000000 : ℝ)^3409
        have hw : |(2592203081/5000000000 : ℝ)|=(2592203081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1039261407/5000000000 : ℝ)|^4433 ≤ (3241612313053/25000000000000 : ℝ)^3409
        have hw : |(-1039261407/5000000000 : ℝ)|=(1039261407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s2_3 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143506429/5000000000 : ℝ)*x 0 + (3979764119/10000000000 : ℝ)*x 1 + (4614966313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143506429/5000000000 : ℝ)^4433 ≤ (33239994751057/100000000000000 : ℝ)^3409 := by
    have hnat : (2143506429 : ℕ)^4433*100000000000000^3409 ≤ 33239994751057^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143506429 5000000000 33239994751057 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979764119/10000000000 : ℝ)^4433 ≤ (30176018687103/100000000000000 : ℝ)^3409 := by
    have hnat : (3979764119 : ℕ)^4433*100000000000000^3409 ≤ 30176018687103^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979764119 10000000000 30176018687103 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4614966313/10000000000 : ℝ)^4433 ≤ (18291993273069/50000000000000 : ℝ)^3409 := by
    have hnat : (4614966313 : ℕ)^4433*50000000000000^3409 ≤ 18291993273069^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4614966313 10000000000 18291993273069 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143506429/5000000000 : ℝ), (3979764119/10000000000 : ℝ), (4614966313/10000000000 : ℝ)] ![(33239994751057/100000000000000 : ℝ), (30176018687103/100000000000000 : ℝ), (18291993273069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143506429/5000000000 : ℝ)|^4433 ≤ (33239994751057/100000000000000 : ℝ)^3409
        have hw : |(2143506429/5000000000 : ℝ)|=(2143506429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979764119/10000000000 : ℝ)|^4433 ≤ (30176018687103/100000000000000 : ℝ)^3409
        have hw : |(3979764119/10000000000 : ℝ)|=(3979764119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4614966313/10000000000 : ℝ)|^4433 ≤ (18291993273069/50000000000000 : ℝ)^3409
        have hw : |(4614966313/10000000000 : ℝ)|=(4614966313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s2_4 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9646741/50000000 : ℝ)*x 0 + (259315333/500000000 : ℝ)*x 1 + (5471549097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9646741/50000000 : ℝ)^4433 ≤ (735599307643/6250000000000 : ℝ)^3409 := by
    have hnat : (9646741 : ℕ)^4433*6250000000000^3409 ≤ 735599307643^3409*50000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9646741 50000000 735599307643 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259315333/500000000 : ℝ)^4433 ≤ (21290061579991/50000000000000 : ℝ)^3409 := by
    have hnat : (259315333 : ℕ)^4433*50000000000000^3409 ≤ 21290061579991^3409*500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259315333 500000000 21290061579991 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471549097/10000000000 : ℝ)^4433 ≤ (9130057579531/20000000000000 : ℝ)^3409 := by
    have hnat : (5471549097 : ℕ)^4433*20000000000000^3409 ≤ 9130057579531^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471549097 10000000000 9130057579531 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9646741/50000000 : ℝ), (259315333/500000000 : ℝ), (5471549097/10000000000 : ℝ)] ![(735599307643/6250000000000 : ℝ), (21290061579991/50000000000000 : ℝ), (9130057579531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9646741/50000000 : ℝ)|^4433 ≤ (735599307643/6250000000000 : ℝ)^3409
        have hw : |(-9646741/50000000 : ℝ)|=(9646741/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259315333/500000000 : ℝ)|^4433 ≤ (21290061579991/50000000000000 : ℝ)^3409
        have hw : |(259315333/500000000 : ℝ)|=(259315333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471549097/10000000000 : ℝ)|^4433 ≤ (9130057579531/20000000000000 : ℝ)^3409
        have hw : |(5471549097/10000000000 : ℝ)|=(5471549097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s2_5 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643702591/5000000000 : ℝ)*x 0 + (-1791380443/10000000000 : ℝ)*x 1 + (5471549121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643702591/5000000000 : ℝ)^4433 ≤ (10915655959061/25000000000000 : ℝ)^3409 := by
    have hnat : (2643702591 : ℕ)^4433*25000000000000^3409 ≤ 10915655959061^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643702591 5000000000 10915655959061 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1791380443/10000000000 : ℝ)^4433 ≤ (2137417598573/20000000000000 : ℝ)^3409 := by
    have hnat : (1791380443 : ℕ)^4433*20000000000000^3409 ≤ 2137417598573^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791380443 10000000000 2137417598573 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471549121/10000000000 : ℝ)^4433 ≤ (45650288158039/100000000000000 : ℝ)^3409 := by
    have hnat : (5471549121 : ℕ)^4433*100000000000000^3409 ≤ 45650288158039^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471549121 10000000000 45650288158039 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643702591/5000000000 : ℝ), (-1791380443/10000000000 : ℝ), (5471549121/10000000000 : ℝ)] ![(10915655959061/25000000000000 : ℝ), (2137417598573/20000000000000 : ℝ), (45650288158039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643702591/5000000000 : ℝ)|^4433 ≤ (10915655959061/25000000000000 : ℝ)^3409
        have hw : |(2643702591/5000000000 : ℝ)|=(2643702591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1791380443/10000000000 : ℝ)|^4433 ≤ (2137417598573/20000000000000 : ℝ)^3409
        have hw : |(-1791380443/10000000000 : ℝ)|=(1791380443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471549121/10000000000 : ℝ)|^4433 ≤ (45650288158039/100000000000000 : ℝ)^3409
        have hw : |(5471549121/10000000000 : ℝ)|=(5471549121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s2_6 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287405323/10000000000 : ℝ)*x 0 + (2735774569/5000000000 : ℝ)*x 1 + (-6997579/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287405323/10000000000 : ℝ)^4433 ≤ (43662625350353/100000000000000 : ℝ)^3409 := by
    have hnat : (5287405323 : ℕ)^4433*100000000000000^3409 ≤ 43662625350353^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287405323 10000000000 43662625350353 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735774569/5000000000 : ℝ)^4433 ≤ (22825144171239/50000000000000 : ℝ)^3409 := by
    have hnat : (2735774569 : ℕ)^4433*50000000000000^3409 ≤ 22825144171239^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735774569 5000000000 22825144171239 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6997579/39062500 : ℝ)^4433 ≤ (2671771573473/25000000000000 : ℝ)^3409 := by
    have hnat : (6997579 : ℕ)^4433*25000000000000^3409 ≤ 2671771573473^3409*39062500^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6997579 39062500 2671771573473 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287405323/10000000000 : ℝ), (2735774569/5000000000 : ℝ), (-6997579/39062500 : ℝ)] ![(43662625350353/100000000000000 : ℝ), (22825144171239/50000000000000 : ℝ), (2671771573473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287405323/10000000000 : ℝ)|^4433 ≤ (43662625350353/100000000000000 : ℝ)^3409
        have hw : |(5287405323/10000000000 : ℝ)|=(5287405323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735774569/5000000000 : ℝ)|^4433 ≤ (22825144171239/50000000000000 : ℝ)^3409
        have hw : |(2735774569/5000000000 : ℝ)|=(2735774569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6997579/39062500 : ℝ)|^4433 ≤ (2671771573473/25000000000000 : ℝ)^3409
        have hw : |(-6997579/39062500 : ℝ)|=(6997579/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s2_7 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287159349/10000000000 : ℝ)*x 0 + (4610789139/10000000000 : ℝ)*x 1 + (1991990113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287159349/10000000000 : ℝ)^4433 ≤ (8310367945899/25000000000000 : ℝ)^3409 := by
    have hnat : (4287159349 : ℕ)^4433*25000000000000^3409 ≤ 8310367945899^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287159349 10000000000 8310367945899 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4610789139/10000000000 : ℝ)^4433 ≤ (36540932226189/100000000000000 : ℝ)^3409 := by
    have hnat : (4610789139 : ℕ)^4433*100000000000000^3409 ≤ 36540932226189^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610789139 10000000000 36540932226189 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991990113/5000000000 : ℝ)^4433 ≤ (30217595963841/100000000000000 : ℝ)^3409 := by
    have hnat : (1991990113 : ℕ)^4433*100000000000000^3409 ≤ 30217595963841^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991990113 5000000000 30217595963841 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287159349/10000000000 : ℝ), (4610789139/10000000000 : ℝ), (1991990113/5000000000 : ℝ)] ![(8310367945899/25000000000000 : ℝ), (36540932226189/100000000000000 : ℝ), (30217595963841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287159349/10000000000 : ℝ)|^4433 ≤ (8310367945899/25000000000000 : ℝ)^3409
        have hw : |(4287159349/10000000000 : ℝ)|=(4287159349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4610789139/10000000000 : ℝ)|^4433 ≤ (36540932226189/100000000000000 : ℝ)^3409
        have hw : |(4610789139/10000000000 : ℝ)|=(4610789139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1991990113/5000000000 : ℝ)|^4433 ≤ (30217595963841/100000000000000 : ℝ)^3409
        have hw : |(1991990113/5000000000 : ℝ)|=(1991990113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1468_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3863/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2519/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16189/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9421/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3863/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9421/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3863/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9421/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3863/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9421/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3863/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9421/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3863/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9421/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3863/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3863/50000 : ℝ) ^ (4431/1024 : ℝ) ≤ (1541753468572571/100000000000000000000 : ℝ) := by
    have hpowers : (3863/50000 : ℝ)^4431 ≤ (1541753468572571/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3863 : ℕ)^4431*100000000000000000000^1024 ≤ 1541753468572571^1024*50000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3863 50000 1541753468572571 100000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3863/50000 : ℝ)) (X := (1541753468572571/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9421/50000 : ℝ) ^ (4431/1024 : ℝ) ≤ (36503703871295907/50000000000000000000 : ℝ) := by
    have hpowers : (9421/50000 : ℝ)^4431 ≤ (36503703871295907/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9421 : ℕ)^4431*50000000000000000000^1024 ≤ 36503703871295907^1024*50000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9421 50000 36503703871295907 50000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9421/50000 : ℝ)) (X := (36503703871295907/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001541753468572571/50000000000000000000 : ℝ) ≤ (5000035629357633/5000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (50001541753468572571/50000000000000000000 : ℝ)^1024 ≤ (5000035629357633/5000000000000000 : ℝ)^4431 := by
      have hnat : (50001541753468572571 : ℕ)^1024*5000000000000000^4431 ≤ 5000035629357633^4431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001541753468572571 50000000000000000000 5000035629357633 5000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000035629357633/5000000000000000 : ℝ)) (X := (50001541753468572571/50000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20014909832242232877/20000000000000000000 : ℝ) ≤ (10001722330665159/10000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (20014909832242232877/20000000000000000000 : ℝ)^1024 ≤ (10001722330665159/10000000000000000 : ℝ)^4431 := by
      have hnat : (20014909832242232877 : ℕ)^1024*10000000000000000^4431 ≤ 10001722330665159^4431*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20014909832242232877 20000000000000000000 10001722330665159 10000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001722330665159/10000000000000000 : ℝ)) (X := (20014909832242232877/20000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25036503703871295907/25000000000000000000 : ℝ) ≤ (2500843350653763/2500000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (25036503703871295907/25000000000000000000 : ℝ)^1024 ≤ (2500843350653763/2500000000000000 : ℝ)^4431 := by
      have hnat : (25036503703871295907 : ℕ)^1024*2500000000000000^4431 ≤ 2500843350653763^4431*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25036503703871295907 25000000000000000000 2500843350653763 2500000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500843350653763/2500000000000000 : ℝ)) (X := (25036503703871295907/25000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1541753468572571/100000000000000000000 : ℝ) ≤ ((5556763987405457511/5558000000000000000 : ℝ)+2*(1651071949893/1111600000000000 : ℝ)*(3863/50000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (5556763987405457511/5558000000000000000 : ℝ)+2*(1651071949893/1111600000000000 : ℝ)*(3863/50000 : ℝ)=(5000035629357633/5000000000000000 : ℝ) by norm_num, show 1+2*(1541753468572571/100000000000000000000 : ℝ)=(50001541753468572571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36503703871295907/50000000000000000000 : ℝ)+(1541753468572571/100000000000000000000 : ℝ) ≤ ((5556763987405457511/5558000000000000000 : ℝ)+(1651071949893/1111600000000000 : ℝ)*((9421/50000 : ℝ)+(3863/50000 : ℝ)))^(4431/1024 : ℝ) := by
    rw [show (5556763987405457511/5558000000000000000 : ℝ)+(1651071949893/1111600000000000 : ℝ)*((9421/50000 : ℝ)+(3863/50000 : ℝ))=(10001722330665159/10000000000000000 : ℝ) by norm_num, show 1+(36503703871295907/50000000000000000000 : ℝ)+(1541753468572571/100000000000000000000 : ℝ)=(20014909832242232877/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36503703871295907/50000000000000000000 : ℝ) ≤ ((5556763987405457511/5558000000000000000 : ℝ)+2*(1651071949893/1111600000000000 : ℝ)*(9421/50000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (5556763987405457511/5558000000000000000 : ℝ)+2*(1651071949893/1111600000000000 : ℝ)*(9421/50000 : ℝ)=(2500843350653763/2500000000000000 : ℝ) by norm_num, show 1+2*(36503703871295907/50000000000000000000 : ℝ)=(25036503703871295907/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5556763987405457511/5558000000000000000 : ℝ)*(X 1 0+X 2 0)+(1651071949893/1111600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (3863/50000 : ℝ)) (hi := (9421/50000 : ℝ)) (c := (5556763987405457511/5558000000000000000 : ℝ)) (alpha := (1651071949893/1111600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5556763987405457511/5558000000000000000 : ℝ)*(X 0 1+X 2 1)+(1651071949893/1111600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (3863/50000 : ℝ)) (hi := (9421/50000 : ℝ)) (c := (5556763987405457511/5558000000000000000 : ℝ)) (alpha := (1651071949893/1111600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5556763987405457511/5558000000000000000 : ℝ)*(X 0 2+X 1 2)+(1651071949893/1111600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (3863/50000 : ℝ)) (hi := (9421/50000 : ℝ)) (c := (5556763987405457511/5558000000000000000 : ℝ)) (alpha := (1651071949893/1111600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-964641069/5000000000 : ℝ)*X 0 0+(1368366989/2500000000 : ℝ)*X 0 1+(5184405569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((670346971/1250000000 : ℝ)*X 1 0+(-415704603/2000000000 : ℝ)*X 1 1+(5184406879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536277663/1000000000 : ℝ)*X 2 0+(2592203081/5000000000 : ℝ)*X 2 1+(-1039261407/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2143506429/5000000000 : ℝ)*X 0 0+(3979764119/10000000000 : ℝ)*X 0 1+(4614966313/10000000000 : ℝ)*X 0 2+(2143506429/5000000000 : ℝ)*X 1 0+(3979764119/10000000000 : ℝ)*X 1 1+(4614966313/10000000000 : ℝ)*X 1 2+(2143506429/5000000000 : ℝ)*X 2 0+(3979764119/10000000000 : ℝ)*X 2 1+(4614966313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-9646741/50000000 : ℝ)*X 0 0+(259315333/500000000 : ℝ)*X 0 1+(5471549097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643702591/5000000000 : ℝ)*X 1 0+(-1791380443/10000000000 : ℝ)*X 1 1+(5471549121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287405323/10000000000 : ℝ)*X 2 0+(2735774569/5000000000 : ℝ)*X 2 1+(-6997579/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4287159349/10000000000 : ℝ)*X 0 0+(4610789139/10000000000 : ℝ)*X 0 1+(1991990113/5000000000 : ℝ)*X 0 2+(4287159349/10000000000 : ℝ)*X 1 0+(4610789139/10000000000 : ℝ)*X 1 1+(1991990113/5000000000 : ℝ)*X 1 2+(4287159349/10000000000 : ℝ)*X 2 0+(4610789139/10000000000 : ℝ)*X 2 1+(1991990113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (693297348318278924905620969/69475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (808210151/50000000000000 : ℝ)*(base19) + (1911875297/100000000000000 : ℝ)*(base23) + (94756597/50000000000000 : ℝ)*(upper3) + (139765179/100000000000000 : ℝ)*(upper4) + (252985881/100000000000000 : ℝ)*(upper5) + (1258464223148607/50000000000000 : ℝ)*(major0) + (1258464223148607/50000000000000 : ℝ)*(major1) + (1258464223148607/50000000000000 : ℝ)*(major2) + (1729745384449113/50000000000000 : ℝ)*(sp0) + (864881360995913/25000000000000 : ℝ)*(sp1) + (1729762574264329/50000000000000 : ℝ)*(sp2) + (196789382097297/12500000000000 : ℝ)*(sp3) + (567054777/1562500000000 : ℝ)*(sp4) + (361069393/2500000000000 : ℝ)*(sp7) + (314865899910819/20000000000000 : ℝ)*(f.failure) + (1729763530201977/50000000000000 : ℝ)*(f.sum) + (179340708549949/27790000000000000000000000000 : ℝ)*base66 + (3367700234478592177/277900000000000000000000000000000 : ℝ)*base67 + (2861833790580392177/277900000000000000000000000000000 : ℝ)*base69 + (1526468431012992177/277900000000000000000000000000000 : ℝ)*base71 + (36351625023709/27790000000000000000000000000 : ℝ)*base74 + (1495956986326192177/277900000000000000000000000000000 : ℝ)*base75 + (50313326718607823/277900000000000000000000000000000 : ℝ)*base78 + (3429395129404592177/277900000000000000000000000000000 : ℝ)*base79 + (9420662611789/27790000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (17669421/2000000000000000000000 : ℝ)*base90 + (17669421/2000000000000000000000 : ℝ)*base92 + (17669421/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1080910182243057501047407599/138950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (553313491/50000000000000 : ℝ)*(base19) + (271572469/20000000000000 : ℝ)*(base23) + (19403647/12500000000000 : ℝ)*(upper3) + (27177191/50000000000000 : ℝ)*(lower4) + (174891823/100000000000000 : ℝ)*(upper5) + (1275293187469997/50000000000000 : ℝ)*(major0) + (1275293187469997/50000000000000 : ℝ)*(major1) + (1275293187469997/50000000000000 : ℝ)*(major2) + (2467873137/20000000000000 : ℝ)*(sp1) + (3238761281/20000000000000 : ℝ)*(sp2) + (438223760033337/12500000000000 : ℝ)*(sp4) + (350577663427403/10000000000000 : ℝ)*(sp5) + (1752886264298973/50000000000000 : ℝ)*(sp6) + (199422801288617/12500000000000 : ℝ)*(sp7) + (199422801288617/12500000000000 : ℝ)*(f.failure) + (438223760033337/12500000000000 : ℝ)*(f.sum) + (4591201915761/27790000000000000000000000000 : ℝ)*base65 + (868395401826802467/277900000000000000000000000000000 : ℝ)*base67 + (906069864633202467/277900000000000000000000000000000 : ℝ)*base69 + (417045300680802467/277900000000000000000000000000000 : ℝ)*base71 + (68269039018489/27790000000000000000000000000 : ℝ)*base74 + (1626210858017497533/277900000000000000000000000000000 : ℝ)*base76 + (1571209251693602467/277900000000000000000000000000000 : ℝ)*base77 + (260140601737397533/277900000000000000000000000000000 : ℝ)*base80 + (75131652323659/27790000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6525703/1250000000000000000000 : ℝ)*base90 + (6525703/1250000000000000000000 : ℝ)*base92 + (6525703/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1468_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9421/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3863/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2519/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1468_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1468_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2519/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1468_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1468_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1468_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2519/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1468_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

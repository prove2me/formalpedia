-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1112_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:05:43.742703+00:00
-- url     : https://prove2.me/submissions/731e0d0c-0277-4807-98a4-515e9c448ed6

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
theorem support_rectangle_w1112_s6_0 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-218127887/1000000000 : ℝ)*x 0 + (5393988353/10000000000 : ℝ)*x 1 + (5264849603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218127887/1000000000 : ℝ)^8305 ≤ (13251422422801/100000000000000 : ℝ)^6257 := by
    have hnat : (218127887 : ℕ)^8305*100000000000000^6257 ≤ 13251422422801^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218127887 1000000000 13251422422801 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393988353/10000000000 : ℝ)^8305 ≤ (44071776199091/100000000000000 : ℝ)^6257 := by
    have hnat : (5393988353 : ℕ)^8305*100000000000000^6257 ≤ 44071776199091^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393988353 10000000000 44071776199091 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264849603/10000000000 : ℝ)^8305 ≤ (10669200339313/25000000000000 : ℝ)^6257 := by
    have hnat : (5264849603 : ℕ)^8305*25000000000000^6257 ≤ 10669200339313^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264849603 10000000000 10669200339313 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218127887/1000000000 : ℝ), (5393988353/10000000000 : ℝ), (5264849603/10000000000 : ℝ)] ![(13251422422801/100000000000000 : ℝ), (44071776199091/100000000000000 : ℝ), (10669200339313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218127887/1000000000 : ℝ)|^8305 ≤ (13251422422801/100000000000000 : ℝ)^6257
        have hw : |(-218127887/1000000000 : ℝ)|=(218127887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393988353/10000000000 : ℝ)|^8305 ≤ (44071776199091/100000000000000 : ℝ)^6257
        have hw : |(5393988353/10000000000 : ℝ)|=(5393988353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264849603/10000000000 : ℝ)|^8305 ≤ (10669200339313/25000000000000 : ℝ)^6257
        have hw : |(5264849603/10000000000 : ℝ)|=(5264849603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s6_1 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672482369/5000000000 : ℝ)*x 0 + (-224679389/1000000000 : ℝ)*x 1 + (20565819/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672482369/5000000000 : ℝ)^8305 ≤ (27213071413/62500000000 : ℝ)^6257 := by
    have hnat : (2672482369 : ℕ)^8305*62500000000^6257 ≤ 27213071413^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672482369 5000000000 27213071413 62500000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224679389/1000000000 : ℝ)^8305 ≤ (6891141857599/50000000000000 : ℝ)^6257 := by
    have hnat : (224679389 : ℕ)^8305*50000000000000^6257 ≤ 6891141857599^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224679389 1000000000 6891141857599 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20565819/39062500 : ℝ)^8305 ≤ (21338401006781/50000000000000 : ℝ)^6257 := by
    have hnat : (20565819 : ℕ)^8305*50000000000000^6257 ≤ 21338401006781^6257*39062500^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20565819 39062500 21338401006781 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672482369/5000000000 : ℝ), (-224679389/1000000000 : ℝ), (20565819/39062500 : ℝ)] ![(27213071413/62500000000 : ℝ), (6891141857599/50000000000000 : ℝ), (21338401006781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672482369/5000000000 : ℝ)|^8305 ≤ (27213071413/62500000000 : ℝ)^6257
        have hw : |(2672482369/5000000000 : ℝ)|=(2672482369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224679389/1000000000 : ℝ)|^8305 ≤ (6891141857599/50000000000000 : ℝ)^6257
        have hw : |(-224679389/1000000000 : ℝ)|=(224679389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20565819/39062500 : ℝ)|^8305 ≤ (21338401006781/50000000000000 : ℝ)^6257
        have hw : |(20565819/39062500 : ℝ)|=(20565819/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s6_2 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267248231/500000000 : ℝ)*x 0 + (5264849649/10000000000 : ℝ)*x 1 + (-1123397033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267248231/500000000 : ℝ)^8305 ≤ (1741636519397/4000000000000 : ℝ)^6257 := by
    have hnat : (267248231 : ℕ)^8305*4000000000000^6257 ≤ 1741636519397^6257*500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267248231 500000000 1741636519397 4000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264849649/10000000000 : ℝ)^8305 ≤ (21338400926087/50000000000000 : ℝ)^6257 := by
    have hnat : (5264849649 : ℕ)^8305*50000000000000^6257 ≤ 21338400926087^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264849649 10000000000 21338400926087 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123397033/5000000000 : ℝ)^8305 ≤ (430696410881/3125000000000 : ℝ)^6257 := by
    have hnat : (1123397033 : ℕ)^8305*3125000000000^6257 ≤ 430696410881^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123397033 5000000000 430696410881 3125000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267248231/500000000 : ℝ), (5264849649/10000000000 : ℝ), (-1123397033/5000000000 : ℝ)] ![(1741636519397/4000000000000 : ℝ), (21338400926087/50000000000000 : ℝ), (430696410881/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267248231/500000000 : ℝ)|^8305 ≤ (1741636519397/4000000000000 : ℝ)^6257
        have hw : |(267248231/500000000 : ℝ)|=(267248231/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264849649/10000000000 : ℝ)|^8305 ≤ (21338400926087/50000000000000 : ℝ)^6257
        have hw : |(5264849649/10000000000 : ℝ)|=(5264849649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123397033/5000000000 : ℝ)|^8305 ≤ (430696410881/3125000000000 : ℝ)^6257
        have hw : |(-1123397033/5000000000 : ℝ)|=(1123397033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s6_3 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368895773/10000000000 : ℝ)*x 0 + (212153149/500000000 : ℝ)*x 1 + (2249234979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368895773/10000000000 : ℝ)^8305 ≤ (16658293834893/50000000000000 : ℝ)^6257 := by
    have hnat : (4368895773 : ℕ)^8305*50000000000000^6257 ≤ 16658293834893^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368895773 10000000000 16658293834893 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212153149/500000000 : ℝ)^8305 ≤ (8012240696029/25000000000000 : ℝ)^6257 := by
    have hnat : (212153149 : ℕ)^8305*25000000000000^6257 ≤ 8012240696029^6257*500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212153149 500000000 8012240696029 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249234979/5000000000 : ℝ)^8305 ≤ (34634449531643/100000000000000 : ℝ)^6257 := by
    have hnat : (2249234979 : ℕ)^8305*100000000000000^6257 ≤ 34634449531643^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249234979 5000000000 34634449531643 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368895773/10000000000 : ℝ), (212153149/500000000 : ℝ), (2249234979/5000000000 : ℝ)] ![(16658293834893/50000000000000 : ℝ), (8012240696029/25000000000000 : ℝ), (34634449531643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368895773/10000000000 : ℝ)|^8305 ≤ (16658293834893/50000000000000 : ℝ)^6257
        have hw : |(4368895773/10000000000 : ℝ)|=(4368895773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212153149/500000000 : ℝ)|^8305 ≤ (8012240696029/25000000000000 : ℝ)^6257
        have hw : |(212153149/500000000 : ℝ)|=(212153149/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249234979/5000000000 : ℝ)|^8305 ≤ (34634449531643/100000000000000 : ℝ)^6257
        have hw : |(2249234979/5000000000 : ℝ)|=(2249234979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s6_4 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2181284027/10000000000 : ℝ)*x 0 + (2632587871/5000000000 : ℝ)*x 1 + (107873219/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181284027/10000000000 : ℝ)^8305 ≤ (13251464006401/100000000000000 : ℝ)^6257 := by
    have hnat : (2181284027 : ℕ)^8305*100000000000000^6257 ≤ 13251464006401^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181284027 10000000000 13251464006401 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632587871/5000000000 : ℝ)^8305 ≤ (853606207653/2000000000000 : ℝ)^6257 := by
    have hnat : (2632587871 : ℕ)^8305*2000000000000^6257 ≤ 853606207653^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632587871 5000000000 853606207653 2000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107873219/200000000 : ℝ)^8305 ≤ (44068225593997/100000000000000 : ℝ)^6257 := by
    have hnat : (107873219 : ℕ)^8305*100000000000000^6257 ≤ 44068225593997^6257*200000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107873219 200000000 44068225593997 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2181284027/10000000000 : ℝ), (2632587871/5000000000 : ℝ), (107873219/200000000 : ℝ)] ![(13251464006401/100000000000000 : ℝ), (853606207653/2000000000000 : ℝ), (44068225593997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2181284027/10000000000 : ℝ)|^8305 ≤ (13251464006401/100000000000000 : ℝ)^6257
        have hw : |(-2181284027/10000000000 : ℝ)|=(2181284027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632587871/5000000000 : ℝ)|^8305 ≤ (853606207653/2000000000000 : ℝ)^6257
        have hw : |(2632587871/5000000000 : ℝ)|=(2632587871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107873219/200000000 : ℝ)|^8305 ≤ (44068225593997/100000000000000 : ℝ)^6257
        have hw : |(107873219/200000000 : ℝ)|=(107873219/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s6_5 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656160311/5000000000 : ℝ)*x 0 + (-529495659/2500000000 : ℝ)*x 1 + (5267247/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656160311/5000000000 : ℝ)^8305 ≤ (43188302988477/100000000000000 : ℝ)^6257 := by
    have hnat : (2656160311 : ℕ)^8305*100000000000000^6257 ≤ 43188302988477^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656160311 5000000000 43188302988477 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529495659/2500000000 : ℝ)^8305 ≤ (12743471633483/100000000000000 : ℝ)^6257 := by
    have hnat : (529495659 : ℕ)^8305*100000000000000^6257 ≤ 12743471633483^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529495659 2500000000 12743471633483 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267247/9765625 : ℝ)^8305 ≤ (8813645071083/20000000000000 : ℝ)^6257 := by
    have hnat : (5267247 : ℕ)^8305*20000000000000^6257 ≤ 8813645071083^6257*9765625^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267247 9765625 8813645071083 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656160311/5000000000 : ℝ), (-529495659/2500000000 : ℝ), (5267247/9765625 : ℝ)] ![(43188302988477/100000000000000 : ℝ), (12743471633483/100000000000000 : ℝ), (8813645071083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656160311/5000000000 : ℝ)|^8305 ≤ (43188302988477/100000000000000 : ℝ)^6257
        have hw : |(2656160311/5000000000 : ℝ)|=(2656160311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529495659/2500000000 : ℝ)|^8305 ≤ (12743471633483/100000000000000 : ℝ)^6257
        have hw : |(-529495659/2500000000 : ℝ)|=(529495659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267247/9765625 : ℝ)|^8305 ≤ (8813645071083/20000000000000 : ℝ)^6257
        have hw : |(5267247/9765625 : ℝ)|=(5267247/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s6_6 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312320637/10000000000 : ℝ)*x 0 + (674207613/1250000000 : ℝ)*x 1 + (-2117982649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312320637/10000000000 : ℝ)^8305 ≤ (2159415157517/5000000000000 : ℝ)^6257 := by
    have hnat : (5312320637 : ℕ)^8305*5000000000000^6257 ≤ 2159415157517^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312320637 10000000000 2159415157517 5000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674207613/1250000000 : ℝ)^8305 ≤ (44068225095143/100000000000000 : ℝ)^6257 := by
    have hnat : (674207613 : ℕ)^8305*100000000000000^6257 ≤ 44068225095143^6257*1250000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674207613 1250000000 44068225095143 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117982649/10000000000 : ℝ)^8305 ≤ (12743471737303/100000000000000 : ℝ)^6257 := by
    have hnat : (2117982649 : ℕ)^8305*100000000000000^6257 ≤ 12743471737303^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117982649 10000000000 12743471737303 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312320637/10000000000 : ℝ), (674207613/1250000000 : ℝ), (-2117982649/10000000000 : ℝ)] ![(2159415157517/5000000000000 : ℝ), (44068225095143/100000000000000 : ℝ), (12743471737303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312320637/10000000000 : ℝ)|^8305 ≤ (2159415157517/5000000000000 : ℝ)^6257
        have hw : |(5312320637/10000000000 : ℝ)|=(5312320637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674207613/1250000000 : ℝ)|^8305 ≤ (44068225095143/100000000000000 : ℝ)^6257
        have hw : |(674207613/1250000000 : ℝ)|=(674207613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117982649/10000000000 : ℝ)|^8305 ≤ (12743471737303/100000000000000 : ℝ)^6257
        have hw : |(-2117982649/10000000000 : ℝ)|=(2117982649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s6_7 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873781199/2000000000 : ℝ)*x 0 + (4497824843/10000000000 : ℝ)*x 1 + (1060927551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873781199/2000000000 : ℝ)^8305 ≤ (33316691135951/100000000000000 : ℝ)^6257 := by
    have hnat : (873781199 : ℕ)^8305*100000000000000^6257 ≤ 33316691135951^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873781199 2000000000 33316691135951 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497824843/10000000000 : ℝ)^8305 ≤ (34627857126437/100000000000000 : ℝ)^6257 := by
    have hnat : (4497824843 : ℕ)^8305*100000000000000^6257 ≤ 34627857126437^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497824843 10000000000 34627857126437 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060927551/2500000000 : ℝ)^8305 ≤ (3205545171931/10000000000000 : ℝ)^6257 := by
    have hnat : (1060927551 : ℕ)^8305*10000000000000^6257 ≤ 3205545171931^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060927551 2500000000 3205545171931 10000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873781199/2000000000 : ℝ), (4497824843/10000000000 : ℝ), (1060927551/2500000000 : ℝ)] ![(33316691135951/100000000000000 : ℝ), (34627857126437/100000000000000 : ℝ), (3205545171931/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873781199/2000000000 : ℝ)|^8305 ≤ (33316691135951/100000000000000 : ℝ)^6257
        have hw : |(873781199/2000000000 : ℝ)|=(873781199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497824843/10000000000 : ℝ)|^8305 ≤ (34627857126437/100000000000000 : ℝ)^6257
        have hw : |(4497824843/10000000000 : ℝ)|=(4497824843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060927551/2500000000 : ℝ)|^8305 ≤ (3205545171931/10000000000000 : ℝ)^6257
        have hw : |(1060927551/2500000000 : ℝ)|=(1060927551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1112_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2261/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (351/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1127/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1127/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1127/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1127/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1127/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1127/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1127/10000 : ℝ) ^ (519/128 : ℝ) ≤ (715842959106199/5000000000000000000 : ℝ) := by
    have hpowers : (1127/10000 : ℝ)^519 ≤ (715842959106199/5000000000000000000 : ℝ)^128 := by
      have hnat : (1127 : ℕ)^519*5000000000000000000^128 ≤ 715842959106199^128*10000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1127 10000 715842959106199 5000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1127/10000 : ℝ)) (X := (715842959106199/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14077/100000 : ℝ) ^ (519/128 : ℝ) ≤ (35275614599964461/100000000000000000000 : ℝ) := by
    have hpowers : (14077/100000 : ℝ)^519 ≤ (35275614599964461/100000000000000000000 : ℝ)^128 := by
      have hnat : (14077 : ℕ)^519*100000000000000000000^128 ≤ 35275614599964461^128*100000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14077 100000 35275614599964461 100000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14077/100000 : ℝ)) (X := (35275614599964461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500715842959106199/2500000000000000000 : ℝ) ≤ (10000706111888311/10000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (2500715842959106199/2500000000000000000 : ℝ)^128 ≤ (10000706111888311/10000000000000000 : ℝ)^519 := by
      have hnat : (2500715842959106199 : ℕ)^128*10000000000000000^519 ≤ 10000706111888311^519*2500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500715842959106199 2500000000000000000 10000706111888311 10000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706111888311/10000000000000000 : ℝ)) (X := (2500715842959106199/2500000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049592473782088441/100000000000000000000 : ℝ) ≤ (10001222861495537/10000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (100049592473782088441/100000000000000000000 : ℝ)^128 ≤ (10001222861495537/10000000000000000 : ℝ)^519 := by
      have hnat : (100049592473782088441 : ℕ)^128*10000000000000000^519 ≤ 10001222861495537^519*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049592473782088441 100000000000000000000 10001222861495537 10000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001222861495537/10000000000000000 : ℝ)) (X := (100049592473782088441/100000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035275614599964461/50000000000000000000 : ℝ) ≤ (10001739611102763/10000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (50035275614599964461/50000000000000000000 : ℝ)^128 ≤ (10001739611102763/10000000000000000 : ℝ)^519 := by
      have hnat : (50035275614599964461 : ℕ)^128*10000000000000000^519 ≤ 10001739611102763^519*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035275614599964461 50000000000000000000 10001739611102763 10000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001739611102763/10000000000000000 : ℝ)) (X := (50035275614599964461/50000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(715842959106199/5000000000000000000 : ℝ) ≤ ((4008619217131944991/4010000000000000000 : ℝ)+2*(258374803613/140350000000000 : ℝ)*(1127/10000 : ℝ))^(519/128 : ℝ) := by
    rw [show (4008619217131944991/4010000000000000000 : ℝ)+2*(258374803613/140350000000000 : ℝ)*(1127/10000 : ℝ)=(10000706111888311/10000000000000000 : ℝ) by norm_num, show 1+2*(715842959106199/5000000000000000000 : ℝ)=(2500715842959106199/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35275614599964461/100000000000000000000 : ℝ)+(715842959106199/5000000000000000000 : ℝ) ≤ ((4008619217131944991/4010000000000000000 : ℝ)+(258374803613/140350000000000 : ℝ)*((14077/100000 : ℝ)+(1127/10000 : ℝ)))^(519/128 : ℝ) := by
    rw [show (4008619217131944991/4010000000000000000 : ℝ)+(258374803613/140350000000000 : ℝ)*((14077/100000 : ℝ)+(1127/10000 : ℝ))=(10001222861495537/10000000000000000 : ℝ) by norm_num, show 1+(35275614599964461/100000000000000000000 : ℝ)+(715842959106199/5000000000000000000 : ℝ)=(100049592473782088441/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35275614599964461/100000000000000000000 : ℝ) ≤ ((4008619217131944991/4010000000000000000 : ℝ)+2*(258374803613/140350000000000 : ℝ)*(14077/100000 : ℝ))^(519/128 : ℝ) := by
    rw [show (4008619217131944991/4010000000000000000 : ℝ)+2*(258374803613/140350000000000 : ℝ)*(14077/100000 : ℝ)=(10001739611102763/10000000000000000 : ℝ) by norm_num, show 1+2*(35275614599964461/100000000000000000000 : ℝ)=(50035275614599964461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4008619217131944991/4010000000000000000 : ℝ)*(X 1 0+X 2 0)+(258374803613/140350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (4008619217131944991/4010000000000000000 : ℝ)) (alpha := (258374803613/140350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4008619217131944991/4010000000000000000 : ℝ)*(X 0 1+X 2 1)+(258374803613/140350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (4008619217131944991/4010000000000000000 : ℝ)) (alpha := (258374803613/140350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4008619217131944991/4010000000000000000 : ℝ)*(X 0 2+X 1 2)+(258374803613/140350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (1127/10000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (4008619217131944991/4010000000000000000 : ℝ)) (alpha := (258374803613/140350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-218127887/1000000000 : ℝ)*X 0 0+(5393988353/10000000000 : ℝ)*X 0 1+(5264849603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672482369/5000000000 : ℝ)*X 1 0+(-224679389/1000000000 : ℝ)*X 1 1+(20565819/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267248231/500000000 : ℝ)*X 2 0+(5264849649/10000000000 : ℝ)*X 2 1+(-1123397033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368895773/10000000000 : ℝ)*X 0 0+(212153149/500000000 : ℝ)*X 0 1+(2249234979/5000000000 : ℝ)*X 0 2+(4368895773/10000000000 : ℝ)*X 1 0+(212153149/500000000 : ℝ)*X 1 1+(2249234979/5000000000 : ℝ)*X 1 2+(4368895773/10000000000 : ℝ)*X 2 0+(212153149/500000000 : ℝ)*X 2 1+(2249234979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2181284027/10000000000 : ℝ)*X 0 0+(2632587871/5000000000 : ℝ)*X 0 1+(107873219/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656160311/5000000000 : ℝ)*X 1 0+(-529495659/2500000000 : ℝ)*X 1 1+(5267247/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312320637/10000000000 : ℝ)*X 2 0+(674207613/1250000000 : ℝ)*X 2 1+(-2117982649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873781199/2000000000 : ℝ)*X 0 0+(4497824843/10000000000 : ℝ)*X 0 1+(1060927551/2500000000 : ℝ)*X 0 2+(873781199/2000000000 : ℝ)*X 1 0+(4497824843/10000000000 : ℝ)*X 1 1+(1060927551/2500000000 : ℝ)*X 1 2+(873781199/2000000000 : ℝ)*X 2 0+(4497824843/10000000000 : ℝ)*X 2 1+(1060927551/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2811533061213670748401827717/350875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1102697927/100000000000000 : ℝ)*(base19) + (39170987/4000000000000 : ℝ)*(base23) + (165041353/100000000000000 : ℝ)*(upper3) + (37635261/100000000000000 : ℝ)*(lower4) + (2914758896014353/50000000000000 : ℝ)*(major0) + (2914758896014353/50000000000000 : ℝ)*(major1) + (2914758896014353/50000000000000 : ℝ)*(major2) + (7743651425604173/100000000000000 : ℝ)*(sp0) + (7743681712932663/100000000000000 : ℝ)*(sp1) + (1935919522537463/25000000000000 : ℝ)*(sp2) + (978833786486859/25000000000000 : ℝ)*(sp3) + (1961876651/6250000000000 : ℝ)*(sp4) + (1873103031/50000000000000 : ℝ)*(sp6) + (17355382067/100000000000000 : ℝ)*(sp7) + (122354765666547/3125000000000 : ℝ)*(f.failure) + (7743682815630589/100000000000000 : ℝ)*(f.sum) + (30466072212729/14035000000000000000000000000 : ℝ)*base66 + (2745819465617990761/1403500000000000000000000000000000 : ℝ)*base67 + (18230381812112490761/1403500000000000000000000000000000 : ℝ)*base69 + (10355164596579509239/1403500000000000000000000000000000 : ℝ)*base72 + (98063893031371/14035000000000000000000000000 : ℝ)*base73 + (16057305270416990761/1403500000000000000000000000000000 : ℝ)*base75 + (2624543135880490761/1403500000000000000000000000000000 : ℝ)*base77 + (27750288793725490761/1403500000000000000000000000000000 : ℝ)*base79 + (1988997062273/7017500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1067823/312500000000000000000 : ℝ)*base89 + (1067823/312500000000000000000 : ℝ)*base91 + (1067823/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (749911442800975854559624269/350875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (546801043/100000000000000 : ℝ)*(base19) + (141423719/25000000000000 : ℝ)*(base23) + (37430127/100000000000000 : ℝ)*(upper3) + (1854221/50000000000000 : ℝ)*(lower4) + (1682859/2500000000000 : ℝ)*(upper5) + (2929557450752279/50000000000000 : ℝ)*(major0) + (2929557450752279/50000000000000 : ℝ)*(major1) + (2929557450752279/50000000000000 : ℝ)*(major2) + (7659360251/50000000000000 : ℝ)*(sp1) + (27362273/200000000000 : ℝ)*(sp2) + (3891499275400931/50000000000000 : ℝ)*(sp4) + (3891491342640159/50000000000000 : ℝ)*(sp5) + (7782984303970487/100000000000000 : ℝ)*(sp6) + (983807795241303/25000000000000 : ℝ)*(sp7) + (983807795241303/25000000000000 : ℝ)*(f.failure) + (3891499275400931/50000000000000 : ℝ)*(f.sum) + (33346028078101/7017500000000000000000000000 : ℝ)*base66 + (6459931509956591423/1403500000000000000000000000000000 : ℝ)*base67 + (2840808715141408577/1403500000000000000000000000000000 : ℝ)*base70 + (22027930989965408577/1403500000000000000000000000000000 : ℝ)*base72 + (13313875657507/3508750000000000000000000000 : ℝ)*base73 + (38674883041303408577/1403500000000000000000000000000000 : ℝ)*base76 + (7136647144579908577/1403500000000000000000000000000000 : ℝ)*base78 + (6448053981647408577/1403500000000000000000000000000000 : ℝ)*base80 + (40763046550367/14035000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2852173/2500000000000000000000 : ℝ)*base90 + (2852173/2500000000000000000000 : ℝ)*base92 + (2852173/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1112_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1112_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1112_s7_0 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2181312739/10000000000 : ℝ)*x 0 + (5393611283/10000000000 : ℝ)*x 1 + (1316301071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181312739/10000000000 : ℝ)^8305 ≤ (13251695526929/100000000000000 : ℝ)^6257 := by
    have hnat : (2181312739 : ℕ)^8305*100000000000000^6257 ≤ 13251695526929^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181312739 10000000000 13251695526929 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393611283/10000000000 : ℝ)^8305 ≤ (44067686973747/100000000000000 : ℝ)^6257 := by
    have hnat : (5393611283 : ℕ)^8305*100000000000000^6257 ≤ 44067686973747^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393611283 10000000000 44067686973747 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316301071/2500000000 : ℝ)^8305 ≤ (42680617477807/100000000000000 : ℝ)^6257 := by
    have hnat : (1316301071 : ℕ)^8305*100000000000000^6257 ≤ 42680617477807^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316301071 2500000000 42680617477807 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2181312739/10000000000 : ℝ), (5393611283/10000000000 : ℝ), (1316301071/2500000000 : ℝ)] ![(13251695526929/100000000000000 : ℝ), (44067686973747/100000000000000 : ℝ), (42680617477807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2181312739/10000000000 : ℝ)|^8305 ≤ (13251695526929/100000000000000 : ℝ)^6257
        have hw : |(-2181312739/10000000000 : ℝ)|=(2181312739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393611283/10000000000 : ℝ)|^8305 ≤ (44067686973747/100000000000000 : ℝ)^6257
        have hw : |(5393611283/10000000000 : ℝ)|=(5393611283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316301071/2500000000 : ℝ)|^8305 ≤ (42680617477807/100000000000000 : ℝ)^6257
        have hw : |(1316301071/2500000000 : ℝ)|=(1316301071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s7_1 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344869793/10000000000 : ℝ)*x 0 + (-2246451239/10000000000 : ℝ)*x 1 + (5265204369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344869793/10000000000 : ℝ)^8305 ≤ (10884971917707/25000000000000 : ℝ)^6257 := by
    have hnat : (5344869793 : ℕ)^8305*25000000000000^6257 ≤ 10884971917707^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344869793 10000000000 10884971917707 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246451239/10000000000 : ℝ)^8305 ≤ (3444873479559/25000000000000 : ℝ)^6257 := by
    have hnat : (2246451239 : ℕ)^8305*25000000000000^6257 ≤ 3444873479559^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246451239 10000000000 3444873479559 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265204369/10000000000 : ℝ)^8305 ≤ (42680618392357/100000000000000 : ℝ)^6257 := by
    have hnat : (5265204369 : ℕ)^8305*100000000000000^6257 ≤ 42680618392357^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265204369 10000000000 42680618392357 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344869793/10000000000 : ℝ), (-2246451239/10000000000 : ℝ), (5265204369/10000000000 : ℝ)] ![(10884971917707/25000000000000 : ℝ), (3444873479559/25000000000000 : ℝ), (42680618392357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344869793/10000000000 : ℝ)|^8305 ≤ (10884971917707/25000000000000 : ℝ)^6257
        have hw : |(5344869793/10000000000 : ℝ)|=(5344869793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2246451239/10000000000 : ℝ)|^8305 ≤ (3444873479559/25000000000000 : ℝ)^6257
        have hw : |(-2246451239/10000000000 : ℝ)|=(2246451239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265204369/10000000000 : ℝ)|^8305 ≤ (42680618392357/100000000000000 : ℝ)^6257
        have hw : |(5265204369/10000000000 : ℝ)|=(5265204369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s7_2 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344869991/10000000000 : ℝ)*x 0 + (526520423/1000000000 : ℝ)*x 1 + (-56161279/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344869991/10000000000 : ℝ)^8305 ≤ (43539889811691/100000000000000 : ℝ)^6257 := by
    have hnat : (5344869991 : ℕ)^8305*100000000000000^6257 ≤ 43539889811691^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344869991 10000000000 43539889811691 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526520423/1000000000 : ℝ)^8305 ≤ (21340308448399/50000000000000 : ℝ)^6257 := by
    have hnat : (526520423 : ℕ)^8305*50000000000000^6257 ≤ 21340308448399^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526520423 1000000000 21340308448399 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56161279/250000000 : ℝ)^8305 ≤ (13779493275049/100000000000000 : ℝ)^6257 := by
    have hnat : (56161279 : ℕ)^8305*100000000000000^6257 ≤ 13779493275049^6257*250000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56161279 250000000 13779493275049 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344869991/10000000000 : ℝ), (526520423/1000000000 : ℝ), (-56161279/250000000 : ℝ)] ![(43539889811691/100000000000000 : ℝ), (21340308448399/50000000000000 : ℝ), (13779493275049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344869991/10000000000 : ℝ)|^8305 ≤ (43539889811691/100000000000000 : ℝ)^6257
        have hw : |(5344869991/10000000000 : ℝ)|=(5344869991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526520423/1000000000 : ℝ)|^8305 ≤ (21340308448399/50000000000000 : ℝ)^6257
        have hw : |(526520423/1000000000 : ℝ)|=(526520423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56161279/250000000 : ℝ)|^8305 ≤ (13779493275049/100000000000000 : ℝ)^6257
        have hw : |(-56161279/250000000 : ℝ)|=(56161279/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s7_3 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184457373/5000000000 : ℝ)*x 0 + (4243784019/10000000000 : ℝ)*x 1 + (4497743751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184457373/5000000000 : ℝ)^8305 ≤ (666335594257/2000000000000 : ℝ)^6257 := by
    have hnat : (2184457373 : ℕ)^8305*2000000000000^6257 ≤ 666335594257^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184457373 5000000000 666335594257 2000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243784019/10000000000 : ℝ)^8305 ≤ (32056191793953/100000000000000 : ℝ)^6257 := by
    have hnat : (4243784019 : ℕ)^8305*100000000000000^6257 ≤ 32056191793953^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243784019 10000000000 32056191793953 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497743751/10000000000 : ℝ)^8305 ≤ (8656757118081/25000000000000 : ℝ)^6257 := by
    have hnat : (4497743751 : ℕ)^8305*25000000000000^6257 ≤ 8656757118081^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497743751 10000000000 8656757118081 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184457373/5000000000 : ℝ), (4243784019/10000000000 : ℝ), (4497743751/10000000000 : ℝ)] ![(666335594257/2000000000000 : ℝ), (32056191793953/100000000000000 : ℝ), (8656757118081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184457373/5000000000 : ℝ)|^8305 ≤ (666335594257/2000000000000 : ℝ)^6257
        have hw : |(2184457373/5000000000 : ℝ)|=(2184457373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243784019/10000000000 : ℝ)|^8305 ≤ (32056191793953/100000000000000 : ℝ)^6257
        have hw : |(4243784019/10000000000 : ℝ)|=(4243784019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497743751/10000000000 : ℝ)|^8305 ≤ (8656757118081/25000000000000 : ℝ)^6257
        have hw : |(4497743751/10000000000 : ℝ)|=(4497743751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s7_4 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2181317791/10000000000 : ℝ)*x 0 + (1316381687/2500000000 : ℝ)*x 1 + (539328759/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181317791/10000000000 : ℝ)^8305 ≤ (6625868132033/50000000000000 : ℝ)^6257 := by
    have hnat : (2181317791 : ℕ)^8305*50000000000000^6257 ≤ 6625868132033^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181317791 10000000000 6625868132033 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316381687/2500000000 : ℝ)^8305 ≤ (42684087038903/100000000000000 : ℝ)^6257 := by
    have hnat : (1316381687 : ℕ)^8305*100000000000000^6257 ≤ 42684087038903^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316381687 2500000000 42684087038903 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539328759/1000000000 : ℝ)^8305 ≤ (22032088341311/50000000000000 : ℝ)^6257 := by
    have hnat : (539328759 : ℕ)^8305*50000000000000^6257 ≤ 22032088341311^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539328759 1000000000 22032088341311 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2181317791/10000000000 : ℝ), (1316381687/2500000000 : ℝ), (539328759/1000000000 : ℝ)] ![(6625868132033/50000000000000 : ℝ), (42684087038903/100000000000000 : ℝ), (22032088341311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2181317791/10000000000 : ℝ)|^8305 ≤ (6625868132033/50000000000000 : ℝ)^6257
        have hw : |(-2181317791/10000000000 : ℝ)|=(2181317791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316381687/2500000000 : ℝ)|^8305 ≤ (42684087038903/100000000000000 : ℝ)^6257
        have hw : |(1316381687/2500000000 : ℝ)|=(1316381687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539328759/1000000000 : ℝ)|^8305 ≤ (22032088341311/50000000000000 : ℝ)^6257
        have hw : |(539328759/1000000000 : ℝ)|=(539328759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s7_5 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312410609/10000000000 : ℝ)*x 0 + (-2118367991/10000000000 : ℝ)*x 1 + (5393287593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312410609/10000000000 : ℝ)^8305 ≤ (674832406667/1562500000000 : ℝ)^6257 := by
    have hnat : (5312410609 : ℕ)^8305*1562500000000^6257 ≤ 674832406667^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312410609 10000000000 674832406667 1562500000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118367991/10000000000 : ℝ)^8305 ≤ (398329663679/3125000000000 : ℝ)^6257 := by
    have hnat : (2118367991 : ℕ)^8305*3125000000000^6257 ≤ 398329663679^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118367991 10000000000 398329663679 3125000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393287593/10000000000 : ℝ)^8305 ≤ (11016044178789/25000000000000 : ℝ)^6257 := by
    have hnat : (5393287593 : ℕ)^8305*25000000000000^6257 ≤ 11016044178789^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393287593 10000000000 11016044178789 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312410609/10000000000 : ℝ), (-2118367991/10000000000 : ℝ), (5393287593/10000000000 : ℝ)] ![(674832406667/1562500000000 : ℝ), (398329663679/3125000000000 : ℝ), (11016044178789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312410609/10000000000 : ℝ)|^8305 ≤ (674832406667/1562500000000 : ℝ)^6257
        have hw : |(5312410609/10000000000 : ℝ)|=(5312410609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2118367991/10000000000 : ℝ)|^8305 ≤ (398329663679/3125000000000 : ℝ)^6257
        have hw : |(-2118367991/10000000000 : ℝ)|=(2118367991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393287593/10000000000 : ℝ)|^8305 ≤ (11016044178789/25000000000000 : ℝ)^6257
        have hw : |(5393287593/10000000000 : ℝ)|=(5393287593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s7_6 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312410609/10000000000 : ℝ)*x 0 + (539328759/1000000000 : ℝ)*x 1 + (-423673599/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312410609/10000000000 : ℝ)^8305 ≤ (674832406667/1562500000000 : ℝ)^6257 := by
    have hnat : (5312410609 : ℕ)^8305*1562500000000^6257 ≤ 674832406667^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312410609 10000000000 674832406667 1562500000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539328759/1000000000 : ℝ)^8305 ≤ (22032088341311/50000000000000 : ℝ)^6257 := by
    have hnat : (539328759 : ℕ)^8305*50000000000000^6257 ≤ 22032088341311^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539328759 1000000000 22032088341311 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423673599/2000000000 : ℝ)^8305 ≤ (509861970787/4000000000000 : ℝ)^6257 := by
    have hnat : (423673599 : ℕ)^8305*4000000000000^6257 ≤ 509861970787^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423673599 2000000000 509861970787 4000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312410609/10000000000 : ℝ), (539328759/1000000000 : ℝ), (-423673599/2000000000 : ℝ)] ![(674832406667/1562500000000 : ℝ), (22032088341311/50000000000000 : ℝ), (509861970787/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312410609/10000000000 : ℝ)|^8305 ≤ (674832406667/1562500000000 : ℝ)^6257
        have hw : |(5312410609/10000000000 : ℝ)|=(5312410609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539328759/1000000000 : ℝ)|^8305 ≤ (22032088341311/50000000000000 : ℝ)^6257
        have hw : |(539328759/1000000000 : ℝ)|=(539328759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423673599/2000000000 : ℝ)|^8305 ≤ (509861970787/4000000000000 : ℝ)^6257
        have hw : |(-423673599/2000000000 : ℝ)|=(423673599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s7_7 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184462253/5000000000 : ℝ)*x 0 + (1124276527/2500000000 : ℝ)*x 1 + (530553003/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184462253/5000000000 : ℝ)^8305 ≤ (2082304906427/6250000000000 : ℝ)^6257 := by
    have hnat : (2184462253 : ℕ)^8305*6250000000000^6257 ≤ 2082304906427^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184462253 5000000000 2082304906427 6250000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124276527/2500000000 : ℝ)^8305 ≤ (34620512765773/100000000000000 : ℝ)^6257 := by
    have hnat : (1124276527 : ℕ)^8305*100000000000000^6257 ≤ 34620512765773^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124276527 2500000000 34620512765773 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530553003/1250000000 : ℝ)^8305 ≤ (32062608707997/100000000000000 : ℝ)^6257 := by
    have hnat : (530553003 : ℕ)^8305*100000000000000^6257 ≤ 32062608707997^6257*1250000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530553003 1250000000 32062608707997 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184462253/5000000000 : ℝ), (1124276527/2500000000 : ℝ), (530553003/1250000000 : ℝ)] ![(2082304906427/6250000000000 : ℝ), (34620512765773/100000000000000 : ℝ), (32062608707997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184462253/5000000000 : ℝ)|^8305 ≤ (2082304906427/6250000000000 : ℝ)^6257
        have hw : |(2184462253/5000000000 : ℝ)|=(2184462253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124276527/2500000000 : ℝ)|^8305 ≤ (34620512765773/100000000000000 : ℝ)^6257
        have hw : |(1124276527/2500000000 : ℝ)|=(1124276527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530553003/1250000000 : ℝ)|^8305 ≤ (32062608707997/100000000000000 : ℝ)^6257
        have hw : |(530553003/1250000000 : ℝ)|=(530553003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1112_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11313/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14033/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2261/20000 : ℝ) ^ (519/128 : ℝ) ≤ (14497996842804107/100000000000000000000 : ℝ) := by
    have hpowers : (2261/20000 : ℝ)^519 ≤ (14497996842804107/100000000000000000000 : ℝ)^128 := by
      have hnat : (2261 : ℕ)^519*100000000000000000000^128 ≤ 14497996842804107^128*20000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2261 20000 14497996842804107 100000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2261/20000 : ℝ)) (X := (14497996842804107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hpowhi : (351/2500 : ℝ) ^ (519/128 : ℝ) ≤ (6980235345676553/20000000000000000000 : ℝ) := by
    have hpowers : (351/2500 : ℝ)^519 ≤ (6980235345676553/20000000000000000000 : ℝ)^128 := by
      have hnat : (351 : ℕ)^519*20000000000000000000^128 ≤ 6980235345676553^128*2500^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 2500 6980235345676553 20000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/2500 : ℝ)) (X := (6980235345676553/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014497996842804107/50000000000000000000 : ℝ) ≤ (2000143008935553/2000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (50014497996842804107/50000000000000000000 : ℝ)^128 ≤ (2000143008935553/2000000000000000 : ℝ)^519 := by
      have hnat : (50014497996842804107 : ℕ)^128*2000000000000000^519 ≤ 2000143008935553^519*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014497996842804107 50000000000000000000 2000143008935553 2000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000143008935553/2000000000000000 : ℝ)) (X := (50014497996842804107/50000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506174896696398359/12500000000000000000 : ℝ) ≤ (10001218095945469/10000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (12506174896696398359/12500000000000000000 : ℝ)^128 ≤ (10001218095945469/10000000000000000 : ℝ)^519 := by
      have hnat : (12506174896696398359 : ℕ)^128*10000000000000000^519 ≤ 10001218095945469^519*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506174896696398359 12500000000000000000 10001218095945469 10000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001218095945469/10000000000000000 : ℝ)) (X := (12506174896696398359/12500000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006980235345676553/10000000000000000000 : ℝ) ≤ (10001721147213173/10000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (10006980235345676553/10000000000000000000 : ℝ)^128 ≤ (10001721147213173/10000000000000000 : ℝ)^519 := by
      have hnat : (10006980235345676553 : ℕ)^128*10000000000000000^519 ≤ 10001721147213173^519*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006980235345676553 10000000000000000000 10001721147213173 10000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001721147213173/10000000000000000 : ℝ)) (X := (10006980235345676553/10000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14497996842804107/100000000000000000000 : ℝ) ≤ ((5468116331606179967/5470000000000000000 : ℝ)+2*(62881408463/34187500000000 : ℝ)*(2261/20000 : ℝ))^(519/128 : ℝ) := by
    rw [show (5468116331606179967/5470000000000000000 : ℝ)+2*(62881408463/34187500000000 : ℝ)*(2261/20000 : ℝ)=(2000143008935553/2000000000000000 : ℝ) by norm_num, show 1+2*(14497996842804107/100000000000000000000 : ℝ)=(50014497996842804107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6980235345676553/20000000000000000000 : ℝ)+(14497996842804107/100000000000000000000 : ℝ) ≤ ((5468116331606179967/5470000000000000000 : ℝ)+(62881408463/34187500000000 : ℝ)*((351/2500 : ℝ)+(2261/20000 : ℝ)))^(519/128 : ℝ) := by
    rw [show (5468116331606179967/5470000000000000000 : ℝ)+(62881408463/34187500000000 : ℝ)*((351/2500 : ℝ)+(2261/20000 : ℝ))=(10001218095945469/10000000000000000 : ℝ) by norm_num, show 1+(6980235345676553/20000000000000000000 : ℝ)+(14497996842804107/100000000000000000000 : ℝ)=(12506174896696398359/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6980235345676553/20000000000000000000 : ℝ) ≤ ((5468116331606179967/5470000000000000000 : ℝ)+2*(62881408463/34187500000000 : ℝ)*(351/2500 : ℝ))^(519/128 : ℝ) := by
    rw [show (5468116331606179967/5470000000000000000 : ℝ)+2*(62881408463/34187500000000 : ℝ)*(351/2500 : ℝ)=(10001721147213173/10000000000000000 : ℝ) by norm_num, show 1+2*(6980235345676553/20000000000000000000 : ℝ)=(10006980235345676553/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5468116331606179967/5470000000000000000 : ℝ)*(X 1 0+X 2 0)+(62881408463/34187500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (5468116331606179967/5470000000000000000 : ℝ)) (alpha := (62881408463/34187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5468116331606179967/5470000000000000000 : ℝ)*(X 0 1+X 2 1)+(62881408463/34187500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (5468116331606179967/5470000000000000000 : ℝ)) (alpha := (62881408463/34187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5468116331606179967/5470000000000000000 : ℝ)*(X 0 2+X 1 2)+(62881408463/34187500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (5468116331606179967/5470000000000000000 : ℝ)) (alpha := (62881408463/34187500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2181312739/10000000000 : ℝ)*X 0 0+(5393611283/10000000000 : ℝ)*X 0 1+(1316301071/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344869793/10000000000 : ℝ)*X 1 0+(-2246451239/10000000000 : ℝ)*X 1 1+(5265204369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344869991/10000000000 : ℝ)*X 2 0+(526520423/1000000000 : ℝ)*X 2 1+(-56161279/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184457373/5000000000 : ℝ)*X 0 0+(4243784019/10000000000 : ℝ)*X 0 1+(4497743751/10000000000 : ℝ)*X 0 2+(2184457373/5000000000 : ℝ)*X 1 0+(4243784019/10000000000 : ℝ)*X 1 1+(4497743751/10000000000 : ℝ)*X 1 2+(2184457373/5000000000 : ℝ)*X 2 0+(4243784019/10000000000 : ℝ)*X 2 1+(4497743751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2181317791/10000000000 : ℝ)*X 0 0+(1316381687/2500000000 : ℝ)*X 0 1+(539328759/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312410609/10000000000 : ℝ)*X 1 0+(-2118367991/10000000000 : ℝ)*X 1 1+(5393287593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312410609/10000000000 : ℝ)*X 2 0+(539328759/1000000000 : ℝ)*X 2 1+(-423673599/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184462253/5000000000 : ℝ)*X 0 0+(1124276527/2500000000 : ℝ)*X 0 1+(530553003/1250000000 : ℝ)*X 0 2+(2184462253/5000000000 : ℝ)*X 1 0+(1124276527/2500000000 : ℝ)*X 1 1+(530553003/1250000000 : ℝ)*X 1 2+(2184462253/5000000000 : ℝ)*X 2 0+(1124276527/2500000000 : ℝ)*X 2 1+(530553003/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (336193962474208908201258759/136750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (592827779/100000000000000 : ℝ)*(base19) + (168521499/25000000000000 : ℝ)*(base23) + (110766599/100000000000000 : ℝ)*(lower2) + (1689499/10000000000000 : ℝ)*(upper3) + (43097699/100000000000000 : ℝ)*(upper5) + (5862715493375341/100000000000000 : ℝ)*(major0) + (5862715493375341/100000000000000 : ℝ)*(major1) + (5862715493375341/100000000000000 : ℝ)*(major2) + (3893877824503913/50000000000000 : ℝ)*(sp0) + (3893890410057193/50000000000000 : ℝ)*(sp1) + (7787780738856169/100000000000000 : ℝ)*(sp2) + (1968819865348921/50000000000000 : ℝ)*(sp3) + (25763934339/100000000000000 : ℝ)*(sp4) + (9761162109/100000000000000 : ℝ)*(sp7) + (3937649491859951/100000000000000 : ℝ)*(f.failure) + (1557556282588433/20000000000000 : ℝ)*(f.sum) + (13925799099961/13675000000000000000000000000 : ℝ)*base66 + (8519724531967273747/547000000000000000000000000000000 : ℝ)*base67 + (2679393250723273747/547000000000000000000000000000000 : ℝ)*base69 + (8951299718619273747/547000000000000000000000000000000 : ℝ)*base71 + (9659802007691/3418750000000000000000000000 : ℝ)*base73 + (4069860792756726253/547000000000000000000000000000000 : ℝ)*base76 + (5222300956212273747/547000000000000000000000000000000 : ℝ)*base77 + (7102286418587273747/547000000000000000000000000000000 : ℝ)*base79 + (232302929207/6837500000000000000000000000 : ℝ)*base81 + (13193259/10000000000000000000000 : ℝ)*base89 + (13193259/10000000000000000000000 : ℝ)*base91 + (13193259/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (750734943413696328006337851/68375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202968651/10000000000000 : ℝ)*(base19) + (2206366121/100000000000000 : ℝ)*(base23) + (13746841/6250000000000 : ℝ)*(upper3) + (40747711/50000000000000 : ℝ)*(lower4) + (113789853/50000000000000 : ℝ)*(upper5) + (2946166061982951/50000000000000 : ℝ)*(major0) + (2946166061982951/50000000000000 : ℝ)*(major1) + (2946166061982951/50000000000000 : ℝ)*(major2) + (14002943927/25000000000000 : ℝ)*(sp1) + (29910257669/50000000000000 : ℝ)*(sp2) + (3913561299617423/50000000000000 : ℝ)*(sp4) + (1956766139443157/25000000000000 : ℝ)*(sp5) + (1956765143088347/25000000000000 : ℝ)*(sp6) + (3957541282707947/100000000000000 : ℝ)*(sp7) + (3957541282707947/100000000000000 : ℝ)*(f.failure) + (3913561299617423/50000000000000 : ℝ)*(f.sum) + (6820915670927/3418750000000000000000000000 : ℝ)*base65 + (931889221992177383/273500000000000000000000000000000 : ℝ)*base68 + (614732819416177383/273500000000000000000000000000000 : ℝ)*base70 + (2593485575148822617/273500000000000000000000000000000 : ℝ)*base71 + (23515990546823/3418750000000000000000000000 : ℝ)*base74 + (6382768919042177383/273500000000000000000000000000000 : ℝ)*base76 + (240607947670177383/273500000000000000000000000000000 : ℝ)*base78 + (2864351020514177383/273500000000000000000000000000000 : ℝ)*base80 + (3720135321723/3418750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (52870423/10000000000000000000000 : ℝ)*base89 + (52870423/10000000000000000000000 : ℝ)*base91 + (52870423/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1112_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1112_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1112_s8_0 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2181315091/10000000000 : ℝ)*x 0 + (2696767927/5000000000 : ℝ)*x 1 + (5265278547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181315091/10000000000 : ℝ)^8305 ≤ (13251714492433/100000000000000 : ℝ)^6257 := by
    have hnat : (2181315091 : ℕ)^8305*100000000000000^6257 ≤ 13251714492433^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181315091 10000000000 13251714492433 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696767927/5000000000 : ℝ)^8305 ≤ (44066868977239/100000000000000 : ℝ)^6257 := by
    have hnat : (2696767927 : ℕ)^8305*100000000000000^6257 ≤ 44066868977239^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696767927 5000000000 44066868977239 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265278547/10000000000 : ℝ)^8305 ≤ (21340708253311/50000000000000 : ℝ)^6257 := by
    have hnat : (5265278547 : ℕ)^8305*50000000000000^6257 ≤ 21340708253311^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265278547 10000000000 21340708253311 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2181315091/10000000000 : ℝ), (2696767927/5000000000 : ℝ), (5265278547/10000000000 : ℝ)] ![(13251714492433/100000000000000 : ℝ), (44066868977239/100000000000000 : ℝ), (21340708253311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2181315091/10000000000 : ℝ)|^8305 ≤ (13251714492433/100000000000000 : ℝ)^6257
        have hw : |(-2181315091/10000000000 : ℝ)|=(2181315091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696767927/5000000000 : ℝ)|^8305 ≤ (44066868977239/100000000000000 : ℝ)^6257
        have hw : |(2696767927/5000000000 : ℝ)|=(2696767927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265278547/10000000000 : ℝ)|^8305 ≤ (21340708253311/50000000000000 : ℝ)^6257
        have hw : |(5265278547/10000000000 : ℝ)|=(5265278547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s8_1 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068970439/2000000000 : ℝ)*x 0 + (-561594143/2500000000 : ℝ)*x 1 + (5265278553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068970439/2000000000 : ℝ)^8305 ≤ (8707939478727/20000000000000 : ℝ)^6257 := by
    have hnat : (1068970439 : ℕ)^8305*20000000000000^6257 ≤ 8707939478727^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068970439 2000000000 8707939478727 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561594143/2500000000 : ℝ)^8305 ≤ (13778886012707/100000000000000 : ℝ)^6257 := by
    have hnat : (561594143 : ℕ)^8305*100000000000000^6257 ≤ 13778886012707^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561594143 2500000000 13778886012707 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265278553/10000000000 : ℝ)^8305 ≤ (42681416571179/100000000000000 : ℝ)^6257 := by
    have hnat : (5265278553 : ℕ)^8305*100000000000000^6257 ≤ 42681416571179^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265278553 10000000000 42681416571179 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068970439/2000000000 : ℝ), (-561594143/2500000000 : ℝ), (5265278553/10000000000 : ℝ)] ![(8707939478727/20000000000000 : ℝ), (13778886012707/100000000000000 : ℝ), (42681416571179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068970439/2000000000 : ℝ)|^8305 ≤ (8707939478727/20000000000000 : ℝ)^6257
        have hw : |(1068970439/2000000000 : ℝ)|=(1068970439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561594143/2500000000 : ℝ)|^8305 ≤ (13778886012707/100000000000000 : ℝ)^6257
        have hw : |(-561594143/2500000000 : ℝ)|=(561594143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265278553/10000000000 : ℝ)|^8305 ≤ (42681416571179/100000000000000 : ℝ)^6257
        have hw : |(5265278553/10000000000 : ℝ)|=(5265278553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s8_2 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344852197/10000000000 : ℝ)*x 0 + (1316319637/2500000000 : ℝ)*x 1 + (-2246376577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344852197/10000000000 : ℝ)^8305 ≤ (2176984870763/5000000000000 : ℝ)^6257 := by
    have hnat : (5344852197 : ℕ)^8305*5000000000000^6257 ≤ 2176984870763^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344852197 10000000000 2176984870763 5000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316319637/2500000000 : ℝ)^8305 ≤ (21340708258691/50000000000000 : ℝ)^6257 := by
    have hnat : (1316319637 : ℕ)^8305*50000000000000^6257 ≤ 21340708258691^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316319637 2500000000 21340708258691 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246376577/10000000000 : ℝ)^8305 ≤ (2755777210683/20000000000000 : ℝ)^6257 := by
    have hnat : (2246376577 : ℕ)^8305*20000000000000^6257 ≤ 2755777210683^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246376577 10000000000 2755777210683 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344852197/10000000000 : ℝ), (1316319637/2500000000 : ℝ), (-2246376577/10000000000 : ℝ)] ![(2176984870763/5000000000000 : ℝ), (21340708258691/50000000000000 : ℝ), (2755777210683/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344852197/10000000000 : ℝ)|^8305 ≤ (2176984870763/5000000000000 : ℝ)^6257
        have hw : |(5344852197/10000000000 : ℝ)|=(5344852197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316319637/2500000000 : ℝ)|^8305 ≤ (21340708258691/50000000000000 : ℝ)^6257
        have hw : |(1316319637/2500000000 : ℝ)|=(1316319637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2246376577/10000000000 : ℝ)|^8305 ≤ (2755777210683/20000000000000 : ℝ)^6257
        have hw : |(-2246376577/10000000000 : ℝ)|=(2246376577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s8_3 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368918487/10000000000 : ℝ)*x 0 + (1060982857/2500000000 : ℝ)*x 1 + (1124398853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368918487/10000000000 : ℝ)^8305 ≤ (33316817578961/100000000000000 : ℝ)^6257 := by
    have hnat : (4368918487 : ℕ)^8305*100000000000000^6257 ≤ 33316817578961^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368918487 10000000000 33316817578961 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060982857/2500000000 : ℝ)^8305 ≤ (16028834870043/50000000000000 : ℝ)^6257 := by
    have hnat : (1060982857 : ℕ)^8305*50000000000000^6257 ≤ 16028834870043^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060982857 2500000000 16028834870043 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124398853/2500000000 : ℝ)^8305 ≤ (34625512654533/100000000000000 : ℝ)^6257 := by
    have hnat : (1124398853 : ℕ)^8305*100000000000000^6257 ≤ 34625512654533^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124398853 2500000000 34625512654533 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368918487/10000000000 : ℝ), (1060982857/2500000000 : ℝ), (1124398853/2500000000 : ℝ)] ![(33316817578961/100000000000000 : ℝ), (16028834870043/50000000000000 : ℝ), (34625512654533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368918487/10000000000 : ℝ)|^8305 ≤ (33316817578961/100000000000000 : ℝ)^6257
        have hw : |(4368918487/10000000000 : ℝ)|=(4368918487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060982857/2500000000 : ℝ)|^8305 ≤ (16028834870043/50000000000000 : ℝ)^6257
        have hw : |(1060982857/2500000000 : ℝ)|=(1060982857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124398853/2500000000 : ℝ)|^8305 ≤ (34625512654533/100000000000000 : ℝ)^6257
        have hw : |(1124398853/2500000000 : ℝ)|=(1124398853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s8_4 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2181320031/10000000000 : ℝ)*x 0 + (1053120051/2000000000 : ℝ)*x 1 + (84268953/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181320031/10000000000 : ℝ)^8305 ≤ (2650350865293/20000000000000 : ℝ)^6257 := by
    have hnat : (2181320031 : ℕ)^8305*20000000000000^6257 ≤ 2650350865293^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181320031 10000000000 2650350865293 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053120051/2000000000 : ℝ)^8305 ≤ (10671219487353/25000000000000 : ℝ)^6257 := by
    have hnat : (1053120051 : ℕ)^8305*25000000000000^6257 ≤ 10671219487353^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053120051 2000000000 10671219487353 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84268953/156250000 : ℝ)^8305 ≤ (22031683856919/50000000000000 : ℝ)^6257 := by
    have hnat : (84268953 : ℕ)^8305*50000000000000^6257 ≤ 22031683856919^6257*156250000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84268953 156250000 22031683856919 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2181320031/10000000000 : ℝ), (1053120051/2000000000 : ℝ), (84268953/156250000 : ℝ)] ![(2650350865293/20000000000000 : ℝ), (10671219487353/25000000000000 : ℝ), (22031683856919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2181320031/10000000000 : ℝ)|^8305 ≤ (2650350865293/20000000000000 : ℝ)^6257
        have hw : |(-2181320031/10000000000 : ℝ)|=(2181320031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053120051/2000000000 : ℝ)|^8305 ≤ (10671219487353/25000000000000 : ℝ)^6257
        have hw : |(1053120051/2000000000 : ℝ)|=(1053120051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84268953/156250000 : ℝ)|^8305 ≤ (22031683856919/50000000000000 : ℝ)^6257
        have hw : |(84268953/156250000 : ℝ)|=(84268953/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s8_5 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531243069/1000000000 : ℝ)*x 0 + (-33100659/156250000 : ℝ)*x 1 + (215728519/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531243069/1000000000 : ℝ)^8305 ≤ (43189490718927/100000000000000 : ℝ)^6257 := by
    have hnat : (531243069 : ℕ)^8305*100000000000000^6257 ≤ 43189490718927^6257*1000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531243069 1000000000 43189490718927 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33100659/156250000 : ℝ)^8305 ≤ (509885669233/4000000000000 : ℝ)^6257 := by
    have hnat : (33100659 : ℕ)^8305*4000000000000^6257 ≤ 509885669233^6257*156250000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33100659 156250000 509885669233 4000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215728519/400000000 : ℝ)^8305 ≤ (11015841882371/25000000000000 : ℝ)^6257 := by
    have hnat : (215728519 : ℕ)^8305*25000000000000^6257 ≤ 11015841882371^6257*400000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215728519 400000000 11015841882371 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531243069/1000000000 : ℝ), (-33100659/156250000 : ℝ), (215728519/400000000 : ℝ)] ![(43189490718927/100000000000000 : ℝ), (509885669233/4000000000000 : ℝ), (11015841882371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531243069/1000000000 : ℝ)|^8305 ≤ (43189490718927/100000000000000 : ℝ)^6257
        have hw : |(531243069/1000000000 : ℝ)|=(531243069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33100659/156250000 : ℝ)|^8305 ≤ (509885669233/4000000000000 : ℝ)^6257
        have hw : |(-33100659/156250000 : ℝ)|=(33100659/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215728519/400000000 : ℝ)|^8305 ≤ (11015841882371/25000000000000 : ℝ)^6257
        have hw : |(215728519/400000000 : ℝ)|=(215728519/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s8_6 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312430723/10000000000 : ℝ)*x 0 + (5393212969/10000000000 : ℝ)*x 1 + (-105922107/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312430723/10000000000 : ℝ)^8305 ≤ (43189491075027/100000000000000 : ℝ)^6257 := by
    have hnat : (5312430723 : ℕ)^8305*100000000000000^6257 ≤ 43189491075027^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312430723 10000000000 43189491075027 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393212969/10000000000 : ℝ)^8305 ≤ (22031683732209/50000000000000 : ℝ)^6257 := by
    have hnat : (5393212969 : ℕ)^8305*50000000000000^6257 ≤ 22031683732209^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393212969 10000000000 22031683732209 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105922107/500000000 : ℝ)^8305 ≤ (6373570721651/50000000000000 : ℝ)^6257 := by
    have hnat : (105922107 : ℕ)^8305*50000000000000^6257 ≤ 6373570721651^6257*500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105922107 500000000 6373570721651 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312430723/10000000000 : ℝ), (5393212969/10000000000 : ℝ), (-105922107/500000000 : ℝ)] ![(43189491075027/100000000000000 : ℝ), (22031683732209/50000000000000 : ℝ), (6373570721651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312430723/10000000000 : ℝ)|^8305 ≤ (43189491075027/100000000000000 : ℝ)^6257
        have hw : |(5312430723/10000000000 : ℝ)|=(5312430723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393212969/10000000000 : ℝ)|^8305 ≤ (22031683732209/50000000000000 : ℝ)^6257
        have hw : |(5393212969/10000000000 : ℝ)|=(5393212969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105922107/500000000 : ℝ)|^8305 ≤ (6373570721651/50000000000000 : ℝ)^6257
        have hw : |(-105922107/500000000 : ℝ)|=(105922107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_s8_7 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368928267/10000000000 : ℝ)*x 0 + (899391833/2000000000 : ℝ)*x 1 + (2122284989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368928267/10000000000 : ℝ)^8305 ≤ (33316916571409/100000000000000 : ℝ)^6257 := by
    have hnat : (4368928267 : ℕ)^8305*100000000000000^6257 ≤ 33316916571409^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368928267 10000000000 33316916571409 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899391833/2000000000 : ℝ)^8305 ≤ (34619011282761/100000000000000 : ℝ)^6257 := by
    have hnat : (899391833 : ℕ)^8305*100000000000000^6257 ≤ 34619011282761^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899391833 2000000000 34619011282761 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122284989/5000000000 : ℝ)^8305 ≤ (4008009017277/12500000000000 : ℝ)^6257 := by
    have hnat : (2122284989 : ℕ)^8305*12500000000000^6257 ≤ 4008009017277^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122284989 5000000000 4008009017277 12500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368928267/10000000000 : ℝ), (899391833/2000000000 : ℝ), (2122284989/5000000000 : ℝ)] ![(33316916571409/100000000000000 : ℝ), (34619011282761/100000000000000 : ℝ), (4008009017277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368928267/10000000000 : ℝ)|^8305 ≤ (33316916571409/100000000000000 : ℝ)^6257
        have hw : |(4368928267/10000000000 : ℝ)|=(4368928267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899391833/2000000000 : ℝ)|^8305 ≤ (34619011282761/100000000000000 : ℝ)^6257
        have hw : |(899391833/2000000000 : ℝ)|=(899391833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122284989/5000000000 : ℝ)|^8305 ≤ (4008009017277/12500000000000 : ℝ)^6257
        have hw : |(2122284989/5000000000 : ℝ)|=(2122284989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1112_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5657/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14031/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11313/100000 : ℝ) ^ (519/128 : ℝ) ≤ (3634910252474863/25000000000000000000 : ℝ) := by
    have hpowers : (11313/100000 : ℝ)^519 ≤ (3634910252474863/25000000000000000000 : ℝ)^128 := by
      have hnat : (11313 : ℕ)^519*25000000000000000000^128 ≤ 3634910252474863^128*100000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11313 100000 3634910252474863 25000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11313/100000 : ℝ)) (X := (3634910252474863/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14033/100000 : ℝ) ^ (519/128 : ℝ) ≤ (6966135068191351/20000000000000000000 : ℝ) := by
    have hpowers : (14033/100000 : ℝ)^519 ≤ (6966135068191351/20000000000000000000 : ℝ)^128 := by
      have hnat : (14033 : ℕ)^519*20000000000000000000^128 ≤ 6966135068191351^128*100000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14033 100000 6966135068191351 20000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14033/100000 : ℝ)) (X := (6966135068191351/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503634910252474863/12500000000000000000 : ℝ) ≤ (625044818647071/625000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (12503634910252474863/12500000000000000000 : ℝ)^128 ≤ (625044818647071/625000000000000 : ℝ)^519 := by
      have hnat : (12503634910252474863 : ℕ)^128*625000000000000^519 ≤ 625044818647071^519*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503634910252474863 12500000000000000000 625044818647071 625000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625044818647071/625000000000000 : ℝ)) (X := (12503634910252474863/12500000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049370316350856207/100000000000000000000 : ℝ) ≤ (10001217384509911/10000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (100049370316350856207/100000000000000000000 : ℝ)^128 ≤ (10001217384509911/10000000000000000 : ℝ)^519 := by
      have hnat : (100049370316350856207 : ℕ)^128*10000000000000000^519 ≤ 10001217384509911^519*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049370316350856207 100000000000000000000 10001217384509911 10000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001217384509911/10000000000000000 : ℝ)) (X := (100049370316350856207/100000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006966135068191351/10000000000000000000 : ℝ) ≤ (5000858835333343/5000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (10006966135068191351/10000000000000000000 : ℝ)^128 ≤ (5000858835333343/5000000000000000 : ℝ)^519 := by
      have hnat : (10006966135068191351 : ℕ)^128*5000000000000000^519 ≤ 5000858835333343^519*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006966135068191351 10000000000000000000 5000858835333343 5000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000858835333343/5000000000000000 : ℝ)) (X := (10006966135068191351/10000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3634910252474863/25000000000000000000 : ℝ) ≤ ((2719063103293733877/2720000000000000000 : ℝ)+2*(20011446271/10880000000000 : ℝ)*(11313/100000 : ℝ))^(519/128 : ℝ) := by
    rw [show (2719063103293733877/2720000000000000000 : ℝ)+2*(20011446271/10880000000000 : ℝ)*(11313/100000 : ℝ)=(625044818647071/625000000000000 : ℝ) by norm_num, show 1+2*(3634910252474863/25000000000000000000 : ℝ)=(12503634910252474863/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6966135068191351/20000000000000000000 : ℝ)+(3634910252474863/25000000000000000000 : ℝ) ≤ ((2719063103293733877/2720000000000000000 : ℝ)+(20011446271/10880000000000 : ℝ)*((14033/100000 : ℝ)+(11313/100000 : ℝ)))^(519/128 : ℝ) := by
    rw [show (2719063103293733877/2720000000000000000 : ℝ)+(20011446271/10880000000000 : ℝ)*((14033/100000 : ℝ)+(11313/100000 : ℝ))=(10001217384509911/10000000000000000 : ℝ) by norm_num, show 1+(6966135068191351/20000000000000000000 : ℝ)+(3634910252474863/25000000000000000000 : ℝ)=(100049370316350856207/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6966135068191351/20000000000000000000 : ℝ) ≤ ((2719063103293733877/2720000000000000000 : ℝ)+2*(20011446271/10880000000000 : ℝ)*(14033/100000 : ℝ))^(519/128 : ℝ) := by
    rw [show (2719063103293733877/2720000000000000000 : ℝ)+2*(20011446271/10880000000000 : ℝ)*(14033/100000 : ℝ)=(5000858835333343/5000000000000000 : ℝ) by norm_num, show 1+2*(6966135068191351/20000000000000000000 : ℝ)=(10006966135068191351/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2719063103293733877/2720000000000000000 : ℝ)*(X 1 0+X 2 0)+(20011446271/10880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (2719063103293733877/2720000000000000000 : ℝ)) (alpha := (20011446271/10880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2719063103293733877/2720000000000000000 : ℝ)*(X 0 1+X 2 1)+(20011446271/10880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (2719063103293733877/2720000000000000000 : ℝ)) (alpha := (20011446271/10880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2719063103293733877/2720000000000000000 : ℝ)*(X 0 2+X 1 2)+(20011446271/10880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (2719063103293733877/2720000000000000000 : ℝ)) (alpha := (20011446271/10880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2181315091/10000000000 : ℝ)*X 0 0+(2696767927/5000000000 : ℝ)*X 0 1+(5265278547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068970439/2000000000 : ℝ)*X 1 0+(-561594143/2500000000 : ℝ)*X 1 1+(5265278553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344852197/10000000000 : ℝ)*X 2 0+(1316319637/2500000000 : ℝ)*X 2 1+(-2246376577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368918487/10000000000 : ℝ)*X 0 0+(1060982857/2500000000 : ℝ)*X 0 1+(1124398853/2500000000 : ℝ)*X 0 2+(4368918487/10000000000 : ℝ)*X 1 0+(1060982857/2500000000 : ℝ)*X 1 1+(1124398853/2500000000 : ℝ)*X 1 2+(4368918487/10000000000 : ℝ)*X 2 0+(1060982857/2500000000 : ℝ)*X 2 1+(1124398853/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2181320031/10000000000 : ℝ)*X 0 0+(1053120051/2000000000 : ℝ)*X 0 1+(84268953/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531243069/1000000000 : ℝ)*X 1 0+(-33100659/156250000 : ℝ)*X 1 1+(215728519/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312430723/10000000000 : ℝ)*X 2 0+(5393212969/10000000000 : ℝ)*X 2 1+(-105922107/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368928267/10000000000 : ℝ)*X 0 0+(899391833/2000000000 : ℝ)*X 0 1+(2122284989/5000000000 : ℝ)*X 0 2+(4368928267/10000000000 : ℝ)*X 1 0+(899391833/2000000000 : ℝ)*X 1 1+(2122284989/5000000000 : ℝ)*X 1 2+(4368928267/10000000000 : ℝ)*X 2 0+(899391833/2000000000 : ℝ)*X 2 1+(2122284989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (276198150322476950914436007/34000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (323986553/20000000000000 : ℝ)*(base19) + (378446067/25000000000000 : ℝ)*(base23) + (7286773/12500000000000 : ℝ)*(lower2) + (209783507/100000000000000 : ℝ)*(upper3) + (61092737/50000000000000 : ℝ)*(upper5) + (2934796480908897/50000000000000 : ℝ)*(major0) + (2934796480908897/50000000000000 : ℝ)*(major1) + (2934796480908897/50000000000000 : ℝ)*(major2) + (7796873040220787/100000000000000 : ℝ)*(sp0) + (3898457670128431/50000000000000 : ℝ)*(sp1) + (7796915446405359/100000000000000 : ℝ)*(sp2) + (492780577727727/12500000000000 : ℝ)*(sp3) + (43919968841/100000000000000 : ℝ)*(sp4) + (12035420819/50000000000000 : ℝ)*(sp7) + (1971134346331727/50000000000000 : ℝ)*(f.failure) + (7796916960189627/100000000000000 : ℝ)*(f.sum) + (555527136513/272000000000000000000000000 : ℝ)*base66 + (1889710540584646331/136000000000000000000000000000000 : ℝ)*base68 + (1215489703640646331/136000000000000000000000000000000 : ℝ)*base70 + (328298668463353669/136000000000000000000000000000000 : ℝ)*base71 + (72747873599/272000000000000000000000000 : ℝ)*base73 + (338118605440646331/136000000000000000000000000000000 : ℝ)*base76 + (2130474113624646331/136000000000000000000000000000000 : ℝ)*base78 + (928555996928646331/136000000000000000000000000000000 : ℝ)*base80 + (149379097551/272000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (18770443/5000000000000000000000 : ℝ)*base89 + (18770443/5000000000000000000000 : ℝ)*base91 + (18770443/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3896858648872185358137/544000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156256117/12500000000000 : ℝ)*(base19) + (287377971/20000000000000 : ℝ)*(base23) + (105122067/25000000000000 : ℝ)*(lower1) + (17757643/12500000000000 : ℝ)*(upper3) + (1724641/3125000000000 : ℝ)*(lower4) + (35284667/25000000000000 : ℝ)*(upper5) + (5899146474191247/100000000000000 : ℝ)*(major0) + (5899146474191247/100000000000000 : ℝ)*(major1) + (5899146474191247/100000000000000 : ℝ)*(major2) + (5616661621/100000000000000 : ℝ)*(sp2) + (3918087309488257/50000000000000 : ℝ)*(sp4) + (3918086684463789/50000000000000 : ℝ)*(sp5) + (7836167565425039/100000000000000 : ℝ)*(sp6) + (990529522656961/25000000000000 : ℝ)*(sp7) + (990529522656961/25000000000000 : ℝ)*(f.failure) + (3918087309488257/50000000000000 : ℝ)*(f.sum) + (733311251279/544000000000000000000000000 : ℝ)*base66 + (4043675502145024619/272000000000000000000000000000000 : ℝ)*base67 + (2569452912865024619/272000000000000000000000000000000 : ℝ)*base69 + (36894944901790975381/272000000000000000000000000000000 : ℝ)*base72 + (1730542739471/544000000000000000000000000 : ℝ)*base74 + (32914920355198975381/272000000000000000000000000000000 : ℝ)*base76 + (2058192584001024619/272000000000000000000000000000000 : ℝ)*base77 + (4334176377742975381/272000000000000000000000000000000 : ℝ)*base80 + (1338869334383/544000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1846651/2500000000000000000000 : ℝ)*base90 + (1846651/2500000000000000000000 : ℝ)*base92 + (1846651/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1112_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1112_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1112_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1112_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1112_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1112_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1127/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1112_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

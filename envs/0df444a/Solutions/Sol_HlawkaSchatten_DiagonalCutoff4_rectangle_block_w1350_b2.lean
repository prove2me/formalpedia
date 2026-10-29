-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:24.093446+00:00
-- url     : https://prove2.me/submissions/19d0a7ed-e352-4350-9ab1-0649a284afbc

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
theorem support_rectangle_w1350_s6_0 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018538033/5000000000 : ℝ)*x 0 + (5412309539/10000000000 : ℝ)*x 1 + (1311209457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018538033/5000000000 : ℝ)^2155 ≤ (3101819953479/25000000000000 : ℝ)^1643 := by
    have hnat : (1018538033 : ℕ)^2155*25000000000000^1643 ≤ 3101819953479^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018538033 5000000000 3101819953479 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412309539/10000000000 : ℝ)^2155 ≤ (22349508241411/50000000000000 : ℝ)^1643 := by
    have hnat : (5412309539 : ℕ)^2155*50000000000000^1643 ≤ 22349508241411^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412309539 10000000000 22349508241411 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311209457/2500000000 : ℝ)^2155 ≤ (42893703695567/100000000000000 : ℝ)^1643 := by
    have hnat : (1311209457 : ℕ)^2155*100000000000000^1643 ≤ 42893703695567^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311209457 2500000000 42893703695567 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018538033/5000000000 : ℝ), (5412309539/10000000000 : ℝ), (1311209457/2500000000 : ℝ)] ![(3101819953479/25000000000000 : ℝ), (22349508241411/50000000000000 : ℝ), (42893703695567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018538033/5000000000 : ℝ)|^2155 ≤ (3101819953479/25000000000000 : ℝ)^1643
        have hw : |(-1018538033/5000000000 : ℝ)|=(1018538033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412309539/10000000000 : ℝ)|^2155 ≤ (22349508241411/50000000000000 : ℝ)^1643
        have hw : |(5412309539/10000000000 : ℝ)|=(5412309539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311209457/2500000000 : ℝ)|^2155 ≤ (42893703695567/100000000000000 : ℝ)^1643
        have hw : |(1311209457/2500000000 : ℝ)|=(1311209457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s6_1 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348862813/10000000000 : ℝ)*x 0 + (-2122397999/10000000000 : ℝ)*x 1 + (5244837821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348862813/10000000000 : ℝ)^2155 ≤ (22006497166079/50000000000000 : ℝ)^1643 := by
    have hnat : (5348862813 : ℕ)^2155*50000000000000^1643 ≤ 22006497166079^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348862813 10000000000 22006497166079 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122397999/10000000000 : ℝ)^2155 ≤ (10229142219/78125000000 : ℝ)^1643 := by
    have hnat : (2122397999 : ℕ)^2155*78125000000^1643 ≤ 10229142219^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122397999 10000000000 10229142219 78125000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244837821/10000000000 : ℝ)^2155 ≤ (42893703620479/100000000000000 : ℝ)^1643 := by
    have hnat : (5244837821 : ℕ)^2155*100000000000000^1643 ≤ 42893703620479^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244837821 10000000000 42893703620479 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348862813/10000000000 : ℝ), (-2122397999/10000000000 : ℝ), (5244837821/10000000000 : ℝ)] ![(22006497166079/50000000000000 : ℝ), (10229142219/78125000000 : ℝ), (42893703620479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348862813/10000000000 : ℝ)|^2155 ≤ (22006497166079/50000000000000 : ℝ)^1643
        have hw : |(5348862813/10000000000 : ℝ)|=(5348862813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2122397999/10000000000 : ℝ)|^2155 ≤ (10229142219/78125000000 : ℝ)^1643
        have hw : |(-2122397999/10000000000 : ℝ)|=(2122397999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244837821/10000000000 : ℝ)|^2155 ≤ (42893703620479/100000000000000 : ℝ)^1643
        have hw : |(5244837821/10000000000 : ℝ)|=(5244837821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s6_2 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674431399/5000000000 : ℝ)*x 0 + (1311209461/2500000000 : ℝ)*x 1 + (-530599497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674431399/5000000000 : ℝ)^2155 ≤ (11003248542567/25000000000000 : ℝ)^1643 := by
    have hnat : (2674431399 : ℕ)^2155*25000000000000^1643 ≤ 11003248542567^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674431399 5000000000 11003248542567 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311209461/2500000000 : ℝ)^2155 ≤ (10723425966799/25000000000000 : ℝ)^1643 := by
    have hnat : (1311209461 : ℕ)^2155*25000000000000^1643 ≤ 10723425966799^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311209461 2500000000 10723425966799 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530599497/2500000000 : ℝ)^2155 ≤ (13093301951313/100000000000000 : ℝ)^1643 := by
    have hnat : (530599497 : ℕ)^2155*100000000000000^1643 ≤ 13093301951313^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530599497 2500000000 13093301951313 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674431399/5000000000 : ℝ), (1311209461/2500000000 : ℝ), (-530599497/2500000000 : ℝ)] ![(11003248542567/25000000000000 : ℝ), (10723425966799/25000000000000 : ℝ), (13093301951313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674431399/5000000000 : ℝ)|^2155 ≤ (11003248542567/25000000000000 : ℝ)^1643
        have hw : |(2674431399/5000000000 : ℝ)|=(2674431399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311209461/2500000000 : ℝ)|^2155 ≤ (10723425966799/25000000000000 : ℝ)^1643
        have hw : |(1311209461/2500000000 : ℝ)|=(1311209461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-530599497/2500000000 : ℝ)|^2155 ≤ (13093301951313/100000000000000 : ℝ)^1643
        have hw : |(-530599497/2500000000 : ℝ)|=(530599497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s6_3 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2162265157/5000000000 : ℝ)*x 0 + (4151943669/10000000000 : ℝ)*x 1 + (2251890683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162265157/5000000000 : ℝ)^2155 ≤ (33303386075421/100000000000000 : ℝ)^1643 := by
    have hnat : (2162265157 : ℕ)^2155*100000000000000^1643 ≤ 33303386075421^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162265157 5000000000 33303386075421 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4151943669/10000000000 : ℝ)^2155 ≤ (31571050471913/100000000000000 : ℝ)^1643 := by
    have hnat : (4151943669 : ℕ)^2155*100000000000000^1643 ≤ 31571050471913^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151943669 10000000000 31571050471913 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251890683/5000000000 : ℝ)^2155 ≤ (35125563442193/100000000000000 : ℝ)^1643 := by
    have hnat : (2251890683 : ℕ)^2155*100000000000000^1643 ≤ 35125563442193^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251890683 5000000000 35125563442193 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162265157/5000000000 : ℝ), (4151943669/10000000000 : ℝ), (2251890683/5000000000 : ℝ)] ![(33303386075421/100000000000000 : ℝ), (31571050471913/100000000000000 : ℝ), (35125563442193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162265157/5000000000 : ℝ)|^2155 ≤ (33303386075421/100000000000000 : ℝ)^1643
        have hw : |(2162265157/5000000000 : ℝ)|=(2162265157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4151943669/10000000000 : ℝ)|^2155 ≤ (31571050471913/100000000000000 : ℝ)^1643
        have hw : |(4151943669/10000000000 : ℝ)|=(4151943669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251890683/5000000000 : ℝ)|^2155 ≤ (35125563442193/100000000000000 : ℝ)^1643
        have hw : |(2251890683/5000000000 : ℝ)|=(2251890683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s6_4 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037088027/10000000000 : ℝ)*x 0 + (5245438199/10000000000 : ℝ)*x 1 + (5411706177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037088027/10000000000 : ℝ)^2155 ≤ (193865240117/1562500000000 : ℝ)^1643 := by
    have hnat : (2037088027 : ℕ)^2155*1562500000000^1643 ≤ 193865240117^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037088027 10000000000 193865240117 1562500000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245438199/10000000000 : ℝ)^2155 ≤ (42900143885061/100000000000000 : ℝ)^1643 := by
    have hnat : (5245438199 : ℕ)^2155*100000000000000^1643 ≤ 42900143885061^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245438199 10000000000 42900143885061 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411706177/10000000000 : ℝ)^2155 ≤ (11173120183089/25000000000000 : ℝ)^1643 := by
    have hnat : (5411706177 : ℕ)^2155*25000000000000^1643 ≤ 11173120183089^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411706177 10000000000 11173120183089 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037088027/10000000000 : ℝ), (5245438199/10000000000 : ℝ), (5411706177/10000000000 : ℝ)] ![(193865240117/1562500000000 : ℝ), (42900143885061/100000000000000 : ℝ), (11173120183089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037088027/10000000000 : ℝ)|^2155 ≤ (193865240117/1562500000000 : ℝ)^1643
        have hw : |(-2037088027/10000000000 : ℝ)|=(2037088027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245438199/10000000000 : ℝ)|^2155 ≤ (42900143885061/100000000000000 : ℝ)^1643
        have hw : |(5245438199/10000000000 : ℝ)|=(5245438199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411706177/10000000000 : ℝ)|^2155 ≤ (11173120183089/25000000000000 : ℝ)^1643
        have hw : |(5411706177/10000000000 : ℝ)|=(5411706177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s6_5 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530568647/1000000000 : ℝ)*x 0 + (-1955529401/10000000000 : ℝ)*x 1 + (2705853141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530568647/1000000000 : ℝ)^2155 ≤ (43547593197087/100000000000000 : ℝ)^1643 := by
    have hnat : (530568647 : ℕ)^2155*100000000000000^1643 ≤ 43547593197087^1643*1000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530568647 1000000000 43547593197087 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955529401/10000000000 : ℝ)^2155 ≤ (5879962459119/50000000000000 : ℝ)^1643 := by
    have hnat : (1955529401 : ℕ)^2155*50000000000000^1643 ≤ 5879962459119^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955529401 10000000000 5879962459119 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705853141/5000000000 : ℝ)^2155 ≤ (44692481869719/100000000000000 : ℝ)^1643 := by
    have hnat : (2705853141 : ℕ)^2155*100000000000000^1643 ≤ 44692481869719^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705853141 5000000000 44692481869719 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530568647/1000000000 : ℝ), (-1955529401/10000000000 : ℝ), (2705853141/5000000000 : ℝ)] ![(43547593197087/100000000000000 : ℝ), (5879962459119/50000000000000 : ℝ), (44692481869719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530568647/1000000000 : ℝ)|^2155 ≤ (43547593197087/100000000000000 : ℝ)^1643
        have hw : |(530568647/1000000000 : ℝ)|=(530568647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955529401/10000000000 : ℝ)|^2155 ≤ (5879962459119/50000000000000 : ℝ)^1643
        have hw : |(-1955529401/10000000000 : ℝ)|=(1955529401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705853141/5000000000 : ℝ)|^2155 ≤ (44692481869719/100000000000000 : ℝ)^1643
        have hw : |(2705853141/5000000000 : ℝ)|=(2705853141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s6_6 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305686409/10000000000 : ℝ)*x 0 + (5411706549/10000000000 : ℝ)*x 1 + (-1955529117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305686409/10000000000 : ℝ)^2155 ≤ (21773796270197/50000000000000 : ℝ)^1643 := by
    have hnat : (5305686409 : ℕ)^2155*50000000000000^1643 ≤ 21773796270197^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305686409 10000000000 21773796270197 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411706549/10000000000 : ℝ)^2155 ≤ (2793280297617/6250000000000 : ℝ)^1643 := by
    have hnat : (5411706549 : ℕ)^2155*6250000000000^1643 ≤ 2793280297617^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411706549 10000000000 2793280297617 6250000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1955529117/10000000000 : ℝ)^2155 ≤ (11759922678133/100000000000000 : ℝ)^1643 := by
    have hnat : (1955529117 : ℕ)^2155*100000000000000^1643 ≤ 11759922678133^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955529117 10000000000 11759922678133 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305686409/10000000000 : ℝ), (5411706549/10000000000 : ℝ), (-1955529117/10000000000 : ℝ)] ![(21773796270197/50000000000000 : ℝ), (2793280297617/6250000000000 : ℝ), (11759922678133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305686409/10000000000 : ℝ)|^2155 ≤ (21773796270197/50000000000000 : ℝ)^1643
        have hw : |(5305686409/10000000000 : ℝ)|=(5305686409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411706549/10000000000 : ℝ)|^2155 ≤ (2793280297617/6250000000000 : ℝ)^1643
        have hw : |(5411706549/10000000000 : ℝ)|=(5411706549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1955529117/10000000000 : ℝ)|^2155 ≤ (11759922678133/100000000000000 : ℝ)^1643
        have hw : |(-1955529117/10000000000 : ℝ)|=(1955529117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s6_7 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081138941/2500000000 : ℝ)*x 0 + (562815063/1250000000 : ℝ)*x 1 + (4153211007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081138941/2500000000 : ℝ)^2155 ≤ (1665182157151/5000000000000 : ℝ)^1643 := by
    have hnat : (1081138941 : ℕ)^2155*5000000000000^1643 ≤ 1665182157151^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081138941 2500000000 1665182157151 5000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562815063/1250000000 : ℝ)^2155 ≤ (35112665978293/100000000000000 : ℝ)^1643 := by
    have hnat : (562815063 : ℕ)^2155*100000000000000^1643 ≤ 35112665978293^1643*1250000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562815063 1250000000 35112665978293 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4153211007/10000000000 : ℝ)^2155 ≤ (31583690859803/100000000000000 : ℝ)^1643 := by
    have hnat : (4153211007 : ℕ)^2155*100000000000000^1643 ≤ 31583690859803^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153211007 10000000000 31583690859803 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081138941/2500000000 : ℝ), (562815063/1250000000 : ℝ), (4153211007/10000000000 : ℝ)] ![(1665182157151/5000000000000 : ℝ), (35112665978293/100000000000000 : ℝ), (31583690859803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081138941/2500000000 : ℝ)|^2155 ≤ (1665182157151/5000000000000 : ℝ)^1643
        have hw : |(1081138941/2500000000 : ℝ)|=(1081138941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562815063/1250000000 : ℝ)|^2155 ≤ (35112665978293/100000000000000 : ℝ)^1643
        have hw : |(562815063/1250000000 : ℝ)|=(562815063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4153211007/10000000000 : ℝ)|^2155 ≤ (31583690859803/100000000000000 : ℝ)^1643
        have hw : |(4153211007/10000000000 : ℝ)|=(4153211007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1350_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11167/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14713/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (279/2500 : ℝ) ^ (4309/1024 : ℝ) ≤ (1966045146788397/20000000000000000000 : ℝ) := by
    have hpowers : (279/2500 : ℝ)^4309 ≤ (1966045146788397/20000000000000000000 : ℝ)^1024 := by
      have hnat : (279 : ℕ)^4309*20000000000000000000^1024 ≤ 1966045146788397^1024*2500^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        279 2500 1966045146788397 20000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (279/2500 : ℝ)) (X := (1966045146788397/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (92/625 : ℝ) ^ (4309/1024 : ℝ) ≤ (7879335126657807/25000000000000000000 : ℝ) := by
    have hpowers : (92/625 : ℝ)^4309 ≤ (7879335126657807/25000000000000000000 : ℝ)^1024 := by
      have hnat : (92 : ℕ)^4309*25000000000000000000^1024 ≤ 7879335126657807^1024*625^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92 625 7879335126657807 25000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92/625 : ℝ)) (X := (7879335126657807/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001966045146788397/10000000000000000000 : ℝ) ≤ (1250058397521851/1250000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (10001966045146788397/10000000000000000000 : ℝ)^1024 ≤ (1250058397521851/1250000000000000 : ℝ)^4309 := by
      have hnat : (10001966045146788397 : ℕ)^1024*1250000000000000^4309 ≤ 1250058397521851^4309*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001966045146788397 10000000000000000000 1250058397521851 1250000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250058397521851/1250000000000000 : ℝ)) (X := (10001966045146788397/10000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041347566240573213/100000000000000000000 : ℝ) ≤ (400039297504139/400000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (100041347566240573213/100000000000000000000 : ℝ)^1024 ≤ (400039297504139/400000000000000 : ℝ)^4309 := by
      have hnat : (100041347566240573213 : ℕ)^1024*400000000000000^4309 ≤ 400039297504139^4309*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041347566240573213 100000000000000000000 400039297504139 400000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400039297504139/400000000000000 : ℝ)) (X := (100041347566240573213/100000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507879335126657807/12500000000000000000 : ℝ) ≤ (5000748847516071/5000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (12507879335126657807/12500000000000000000 : ℝ)^1024 ≤ (5000748847516071/5000000000000000 : ℝ)^4309 := by
      have hnat : (12507879335126657807 : ℕ)^1024*5000000000000000^4309 ≤ 5000748847516071^4309*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507879335126657807 12500000000000000000 5000748847516071 5000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000748847516071/5000000000000000 : ℝ)) (X := (12507879335126657807/12500000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1966045146788397/20000000000000000000 : ℝ) ≤ ((444877032695180863/445000000000000000 : ℝ)+2*(515257428667/356000000000000 : ℝ)*(279/2500 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (444877032695180863/445000000000000000 : ℝ)+2*(515257428667/356000000000000 : ℝ)*(279/2500 : ℝ)=(1250058397521851/1250000000000000 : ℝ) by norm_num, show 1+2*(1966045146788397/20000000000000000000 : ℝ)=(10001966045146788397/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7879335126657807/25000000000000000000 : ℝ)+(1966045146788397/20000000000000000000 : ℝ) ≤ ((444877032695180863/445000000000000000 : ℝ)+(515257428667/356000000000000 : ℝ)*((92/625 : ℝ)+(279/2500 : ℝ)))^(4309/1024 : ℝ) := by
    rw [show (444877032695180863/445000000000000000 : ℝ)+(515257428667/356000000000000 : ℝ)*((92/625 : ℝ)+(279/2500 : ℝ))=(400039297504139/400000000000000 : ℝ) by norm_num, show 1+(7879335126657807/25000000000000000000 : ℝ)+(1966045146788397/20000000000000000000 : ℝ)=(100041347566240573213/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7879335126657807/25000000000000000000 : ℝ) ≤ ((444877032695180863/445000000000000000 : ℝ)+2*(515257428667/356000000000000 : ℝ)*(92/625 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (444877032695180863/445000000000000000 : ℝ)+2*(515257428667/356000000000000 : ℝ)*(92/625 : ℝ)=(5000748847516071/5000000000000000 : ℝ) by norm_num, show 1+2*(7879335126657807/25000000000000000000 : ℝ)=(12507879335126657807/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (444877032695180863/445000000000000000 : ℝ)*(X 1 0+X 2 0)+(515257428667/356000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (92/625 : ℝ)) (c := (444877032695180863/445000000000000000 : ℝ)) (alpha := (515257428667/356000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (444877032695180863/445000000000000000 : ℝ)*(X 0 1+X 2 1)+(515257428667/356000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (92/625 : ℝ)) (c := (444877032695180863/445000000000000000 : ℝ)) (alpha := (515257428667/356000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (444877032695180863/445000000000000000 : ℝ)*(X 0 2+X 1 2)+(515257428667/356000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (92/625 : ℝ)) (c := (444877032695180863/445000000000000000 : ℝ)) (alpha := (515257428667/356000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1018538033/5000000000 : ℝ)*X 0 0+(5412309539/10000000000 : ℝ)*X 0 1+(1311209457/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348862813/10000000000 : ℝ)*X 1 0+(-2122397999/10000000000 : ℝ)*X 1 1+(5244837821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674431399/5000000000 : ℝ)*X 2 0+(1311209461/2500000000 : ℝ)*X 2 1+(-530599497/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162265157/5000000000 : ℝ)*X 0 0+(4151943669/10000000000 : ℝ)*X 0 1+(2251890683/5000000000 : ℝ)*X 0 2+(2162265157/5000000000 : ℝ)*X 1 0+(4151943669/10000000000 : ℝ)*X 1 1+(2251890683/5000000000 : ℝ)*X 1 2+(2162265157/5000000000 : ℝ)*X 2 0+(4151943669/10000000000 : ℝ)*X 2 1+(2251890683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2037088027/10000000000 : ℝ)*X 0 0+(5245438199/10000000000 : ℝ)*X 0 1+(5411706177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530568647/1000000000 : ℝ)*X 1 0+(-1955529401/10000000000 : ℝ)*X 1 1+(2705853141/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305686409/10000000000 : ℝ)*X 2 0+(5411706549/10000000000 : ℝ)*X 2 1+(-1955529117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081138941/2500000000 : ℝ)*X 0 0+(562815063/1250000000 : ℝ)*X 0 1+(4153211007/10000000000 : ℝ)*X 0 2+(1081138941/2500000000 : ℝ)*X 1 0+(562815063/1250000000 : ℝ)*X 1 1+(4153211007/10000000000 : ℝ)*X 1 2+(1081138941/2500000000 : ℝ)*X 2 0+(562815063/1250000000 : ℝ)*X 2 1+(4153211007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46599445688064769016099853/5562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1587403689/100000000000000 : ℝ)*(base19) + (46479933/3125000000000 : ℝ)*(base23) + (44556309/100000000000000 : ℝ)*(lower2) + (49653743/25000000000000 : ℝ)*(upper3) + (147568441/100000000000000 : ℝ)*(upper5) + (1101684516092641/25000000000000 : ℝ)*(major0) + (1101684516092641/25000000000000 : ℝ)*(major1) + (1101684516092641/25000000000000 : ℝ)*(major2) + (1492797898000263/25000000000000 : ℝ)*(sp0) + (2985611543523357/50000000000000 : ℝ)*(sp1) + (5971223187092547/100000000000000 : ℝ)*(sp2) + (284223481395017/10000000000000 : ℝ)*(sp3) + (33082449351/100000000000000 : ℝ)*(sp4) + (4090273233/25000000000000 : ℝ)*(sp7) + (1421125587521551/50000000000000 : ℝ)*(f.failure) + (5971224674450403/100000000000000 : ℝ)*(f.sum) + (14998467120003/4450000000000000000000000000 : ℝ)*base66 + (46222828630887933/11125000000000000000000000000000 : ℝ)*base67 + (19385706419887933/11125000000000000000000000000000 : ℝ)*base69 + (94383903984012933/11125000000000000000000000000000 : ℝ)*base71 + (10284380325853/4450000000000000000000000000 : ℝ)*base74 + (153561728047512933/11125000000000000000000000000000 : ℝ)*base75 + (117491418717012933/11125000000000000000000000000000 : ℝ)*base77 + (37543606581012933/11125000000000000000000000000000 : ℝ)*base79 + (1958043781053/4450000000000000000000000000 : ℝ)*base82 + (7131363/1000000000000000000000 : ℝ)*base90 + (7131363/1000000000000000000000 : ℝ)*base92 + (7131363/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110459437634669871732803697/11125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (894746131/50000000000000 : ℝ)*(base19) + (541416581/25000000000000 : ℝ)*(base23) + (120992307/50000000000000 : ℝ)*(upper3) + (36751977/25000000000000 : ℝ)*(lower4) + (90898999/100000000000000 : ℝ)*(upper5) + (2219292841519873/50000000000000 : ℝ)*(major0) + (2219292841519873/50000000000000 : ℝ)*(major1) + (2219292841519873/50000000000000 : ℝ)*(major2) + (38487678867/100000000000000 : ℝ)*(sp1) + (59162352509/100000000000000 : ℝ)*(sp2) + (6014378831705087/100000000000000 : ℝ)*(sp4) + (3007169277266979/50000000000000 : ℝ)*(sp5) + (3007158751843127/50000000000000 : ℝ)*(sp6) + (22365564089139/781250000000 : ℝ)*(sp7) + (22365564089139/781250000000 : ℝ)*(f.failure) + (6014378831705087/100000000000000 : ℝ)*(f.sum) + (253874477809/8900000000000000000000000000 : ℝ)*base66 + (26083989090654149/22250000000000000000000000000000 : ℝ)*base67 + (231735871438845851/22250000000000000000000000000000 : ℝ)*base70 + (60852740329845851/22250000000000000000000000000000 : ℝ)*base72 + (77424069393991/8900000000000000000000000000 : ℝ)*base73 + (264548626487845851/22250000000000000000000000000000 : ℝ)*base76 + (65937528821904149/22250000000000000000000000000000 : ℝ)*base77 + (108132677379595851/22250000000000000000000000000000 : ℝ)*base80 + (3484780913309/8900000000000000000000000000 : ℝ)*base82 + (48107/15625000000000000000 : ℝ)*base90 + (48107/15625000000000000000 : ℝ)*base92 + (48107/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1350_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1350_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1350_s7_0 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-254635197/1250000000 : ℝ)*x 0 + (1353063107/2500000000 : ℝ)*x 1 + (5244891397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (254635197/1250000000 : ℝ)^2155 ≤ (387728869749/3125000000000 : ℝ)^1643 := by
    have hnat : (254635197 : ℕ)^2155*3125000000000^1643 ≤ 387728869749^1643*1250000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254635197 1250000000 387728869749 3125000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353063107/2500000000 : ℝ)^2155 ≤ (357587182673/800000000000 : ℝ)^1643 := by
    have hnat : (1353063107 : ℕ)^2155*800000000000^1643 ≤ 357587182673^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353063107 2500000000 357587182673 800000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244891397/10000000000 : ℝ)^2155 ≤ (5361784790221/12500000000000 : ℝ)^1643 := by
    have hnat : (5244891397 : ℕ)^2155*12500000000000^1643 ≤ 5361784790221^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244891397 10000000000 5361784790221 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-254635197/1250000000 : ℝ), (1353063107/2500000000 : ℝ), (5244891397/10000000000 : ℝ)] ![(387728869749/3125000000000 : ℝ), (357587182673/800000000000 : ℝ), (5361784790221/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-254635197/1250000000 : ℝ)|^2155 ≤ (387728869749/3125000000000 : ℝ)^1643
        have hw : |(-254635197/1250000000 : ℝ)|=(254635197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353063107/2500000000 : ℝ)|^2155 ≤ (357587182673/800000000000 : ℝ)^1643
        have hw : |(1353063107/2500000000 : ℝ)|=(1353063107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244891397/10000000000 : ℝ)|^2155 ≤ (5361784790221/12500000000000 : ℝ)^1643
        have hw : |(5244891397/10000000000 : ℝ)|=(5244891397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s7_1 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337212111/2500000000 : ℝ)*x 0 + (-2122346017/10000000000 : ℝ)*x 1 + (5244891489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337212111/2500000000 : ℝ)^2155 ≤ (44012839252251/100000000000000 : ℝ)^1643 := by
    have hnat : (1337212111 : ℕ)^2155*100000000000000^1643 ≤ 44012839252251^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337212111 2500000000 44012839252251 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122346017/10000000000 : ℝ)^2155 ≤ (3273220356659/25000000000000 : ℝ)^1643 := by
    have hnat : (2122346017 : ℕ)^2155*25000000000000^1643 ≤ 3273220356659^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122346017 10000000000 3273220356659 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244891489/10000000000 : ℝ)^2155 ≤ (42894279308639/100000000000000 : ℝ)^1643 := by
    have hnat : (5244891489 : ℕ)^2155*100000000000000^1643 ≤ 42894279308639^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244891489 10000000000 42894279308639 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337212111/2500000000 : ℝ), (-2122346017/10000000000 : ℝ), (5244891489/10000000000 : ℝ)] ![(44012839252251/100000000000000 : ℝ), (3273220356659/25000000000000 : ℝ), (42894279308639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337212111/2500000000 : ℝ)|^2155 ≤ (44012839252251/100000000000000 : ℝ)^1643
        have hw : |(1337212111/2500000000 : ℝ)|=(1337212111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2122346017/10000000000 : ℝ)|^2155 ≤ (3273220356659/25000000000000 : ℝ)^1643
        have hw : |(-2122346017/10000000000 : ℝ)|=(2122346017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244891489/10000000000 : ℝ)|^2155 ≤ (42894279308639/100000000000000 : ℝ)^1643
        have hw : |(5244891489/10000000000 : ℝ)|=(5244891489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s7_2 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (213953939/400000000 : ℝ)*x 0 + (1048978279/2000000000 : ℝ)*x 1 + (-21223461/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213953939/400000000 : ℝ)^2155 ≤ (5501604948353/12500000000000 : ℝ)^1643 := by
    have hnat : (213953939 : ℕ)^2155*12500000000000^1643 ≤ 5501604948353^1643*400000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213953939 400000000 5501604948353 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048978279/2000000000 : ℝ)^2155 ≤ (21447139150157/50000000000000 : ℝ)^1643 := by
    have hnat : (1048978279 : ℕ)^2155*50000000000000^1643 ≤ 21447139150157^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048978279 2000000000 21447139150157 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21223461/100000000 : ℝ)^2155 ≤ (13092882098231/100000000000000 : ℝ)^1643 := by
    have hnat : (21223461 : ℕ)^2155*100000000000000^1643 ≤ 13092882098231^1643*100000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21223461 100000000 13092882098231 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213953939/400000000 : ℝ), (1048978279/2000000000 : ℝ), (-21223461/100000000 : ℝ)] ![(5501604948353/12500000000000 : ℝ), (21447139150157/50000000000000 : ℝ), (13092882098231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213953939/400000000 : ℝ)|^2155 ≤ (5501604948353/12500000000000 : ℝ)^1643
        have hw : |(213953939/400000000 : ℝ)|=(213953939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048978279/2000000000 : ℝ)|^2155 ≤ (21447139150157/50000000000000 : ℝ)^1643
        have hw : |(1048978279/2000000000 : ℝ)|=(1048978279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21223461/100000000 : ℝ)|^2155 ≤ (13092882098231/100000000000000 : ℝ)^1643
        have hw : |(-21223461/100000000 : ℝ)|=(21223461/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s7_3 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2162267127/5000000000 : ℝ)*x 0 + (1038014871/2500000000 : ℝ)*x 1 + (2251832279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162267127/5000000000 : ℝ)^2155 ≤ (33303425872889/100000000000000 : ℝ)^1643 := by
    have hnat : (2162267127 : ℕ)^2155*100000000000000^1643 ≤ 33303425872889^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162267127 5000000000 33303425872889 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038014871/2500000000 : ℝ)^2155 ≤ (6314441111407/20000000000000 : ℝ)^1643 := by
    have hnat : (1038014871 : ℕ)^2155*20000000000000^1643 ≤ 6314441111407^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038014871 2500000000 6314441111407 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251832279/5000000000 : ℝ)^2155 ≤ (17562184277999/50000000000000 : ℝ)^1643 := by
    have hnat : (2251832279 : ℕ)^2155*50000000000000^1643 ≤ 17562184277999^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251832279 5000000000 17562184277999 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162267127/5000000000 : ℝ), (1038014871/2500000000 : ℝ), (2251832279/5000000000 : ℝ)] ![(33303425872889/100000000000000 : ℝ), (6314441111407/20000000000000 : ℝ), (17562184277999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162267127/5000000000 : ℝ)|^2155 ≤ (33303425872889/100000000000000 : ℝ)^1643
        have hw : |(2162267127/5000000000 : ℝ)|=(2162267127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038014871/2500000000 : ℝ)|^2155 ≤ (6314441111407/20000000000000 : ℝ)^1643
        have hw : |(1038014871/2500000000 : ℝ)|=(1038014871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251832279/5000000000 : ℝ)|^2155 ≤ (17562184277999/50000000000000 : ℝ)^1643
        have hw : |(2251832279/5000000000 : ℝ)|=(2251832279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s7_4 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018546829/5000000000 : ℝ)*x 0 + (5245490697/10000000000 : ℝ)*x 1 + (1082330007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018546829/5000000000 : ℝ)^2155 ≤ (12407420352263/100000000000000 : ℝ)^1643 := by
    have hnat : (1018546829 : ℕ)^2155*100000000000000^1643 ≤ 12407420352263^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018546829 5000000000 12407420352263 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245490697/10000000000 : ℝ)^2155 ≤ (42900707042883/100000000000000 : ℝ)^1643 := by
    have hnat : (5245490697 : ℕ)^2155*100000000000000^1643 ≤ 42900707042883^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245490697 10000000000 42900707042883 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082330007/2000000000 : ℝ)^2155 ≤ (44691872601357/100000000000000 : ℝ)^1643 := by
    have hnat : (1082330007 : ℕ)^2155*100000000000000^1643 ≤ 44691872601357^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082330007 2000000000 44691872601357 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018546829/5000000000 : ℝ), (5245490697/10000000000 : ℝ), (1082330007/2000000000 : ℝ)] ![(12407420352263/100000000000000 : ℝ), (42900707042883/100000000000000 : ℝ), (44691872601357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018546829/5000000000 : ℝ)|^2155 ≤ (12407420352263/100000000000000 : ℝ)^1643
        have hw : |(-1018546829/5000000000 : ℝ)|=(1018546829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245490697/10000000000 : ℝ)|^2155 ≤ (42900707042883/100000000000000 : ℝ)^1643
        have hw : |(5245490697/10000000000 : ℝ)|=(5245490697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082330007/2000000000 : ℝ)|^2155 ≤ (44691872601357/100000000000000 : ℝ)^1643
        have hw : |(1082330007/2000000000 : ℝ)|=(1082330007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s7_5 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530570053/1000000000 : ℝ)*x 0 + (-977793727/5000000000 : ℝ)*x 1 + (1082330007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530570053/1000000000 : ℝ)^2155 ≤ (4354774455941/10000000000000 : ℝ)^1643 := by
    have hnat : (530570053 : ℕ)^2155*10000000000000^1643 ≤ 4354774455941^1643*1000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530570053 1000000000 4354774455941 10000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977793727/5000000000 : ℝ)^2155 ≤ (1470047853063/12500000000000 : ℝ)^1643 := by
    have hnat : (977793727 : ℕ)^2155*12500000000000^1643 ≤ 1470047853063^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977793727 5000000000 1470047853063 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082330007/2000000000 : ℝ)^2155 ≤ (44691872601357/100000000000000 : ℝ)^1643 := by
    have hnat : (1082330007 : ℕ)^2155*100000000000000^1643 ≤ 44691872601357^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082330007 2000000000 44691872601357 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530570053/1000000000 : ℝ), (-977793727/5000000000 : ℝ), (1082330007/2000000000 : ℝ)] ![(4354774455941/10000000000000 : ℝ), (1470047853063/12500000000000 : ℝ), (44691872601357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530570053/1000000000 : ℝ)|^2155 ≤ (4354774455941/10000000000000 : ℝ)^1643
        have hw : |(530570053/1000000000 : ℝ)|=(530570053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-977793727/5000000000 : ℝ)|^2155 ≤ (1470047853063/12500000000000 : ℝ)^1643
        have hw : |(-977793727/5000000000 : ℝ)|=(977793727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082330007/2000000000 : ℝ)|^2155 ≤ (44691872601357/100000000000000 : ℝ)^1643
        have hw : |(1082330007/2000000000 : ℝ)|=(1082330007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s7_6 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305700531/10000000000 : ℝ)*x 0 + (2705825017/5000000000 : ℝ)*x 1 + (-977793727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305700531/10000000000 : ℝ)^2155 ≤ (680433508909/1562500000000 : ℝ)^1643 := by
    have hnat : (5305700531 : ℕ)^2155*1562500000000^1643 ≤ 680433508909^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305700531 10000000000 680433508909 1562500000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705825017/5000000000 : ℝ)^2155 ≤ (1787674903621/4000000000000 : ℝ)^1643 := by
    have hnat : (2705825017 : ℕ)^2155*4000000000000^1643 ≤ 1787674903621^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705825017 5000000000 1787674903621 4000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (977793727/5000000000 : ℝ)^2155 ≤ (1470047853063/12500000000000 : ℝ)^1643 := by
    have hnat : (977793727 : ℕ)^2155*12500000000000^1643 ≤ 1470047853063^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977793727 5000000000 1470047853063 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305700531/10000000000 : ℝ), (2705825017/5000000000 : ℝ), (-977793727/5000000000 : ℝ)] ![(680433508909/1562500000000 : ℝ), (1787674903621/4000000000000 : ℝ), (1470047853063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305700531/10000000000 : ℝ)|^2155 ≤ (680433508909/1562500000000 : ℝ)^1643
        have hw : |(5305700531/10000000000 : ℝ)|=(5305700531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705825017/5000000000 : ℝ)|^2155 ≤ (1787674903621/4000000000000 : ℝ)^1643
        have hw : |(2705825017/5000000000 : ℝ)|=(2705825017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-977793727/5000000000 : ℝ)|^2155 ≤ (1470047853063/12500000000000 : ℝ)^1643
        have hw : |(-977793727/5000000000 : ℝ)|=(977793727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s7_7 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081139903/2500000000 : ℝ)*x 0 + (2251202789/5000000000 : ℝ)*x 1 + (1038331241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081139903/2500000000 : ℝ)^2155 ≤ (16651841005639/50000000000000 : ℝ)^1643 := by
    have hnat : (1081139903 : ℕ)^2155*50000000000000^1643 ≤ 16651841005639^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081139903 2500000000 16651841005639 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251202789/5000000000 : ℝ)^2155 ≤ (7022298089299/20000000000000 : ℝ)^1643 := by
    have hnat : (2251202789 : ℕ)^2155*20000000000000^1643 ≤ 7022298089299^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251202789 5000000000 7022298089299 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038331241/2500000000 : ℝ)^2155 ≤ (31584827522111/100000000000000 : ℝ)^1643 := by
    have hnat : (1038331241 : ℕ)^2155*100000000000000^1643 ≤ 31584827522111^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038331241 2500000000 31584827522111 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081139903/2500000000 : ℝ), (2251202789/5000000000 : ℝ), (1038331241/2500000000 : ℝ)] ![(16651841005639/50000000000000 : ℝ), (7022298089299/20000000000000 : ℝ), (31584827522111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081139903/2500000000 : ℝ)|^2155 ≤ (16651841005639/50000000000000 : ℝ)^1643
        have hw : |(1081139903/2500000000 : ℝ)|=(1081139903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251202789/5000000000 : ℝ)|^2155 ≤ (7022298089299/20000000000000 : ℝ)^1643
        have hw : |(2251202789/5000000000 : ℝ)|=(2251202789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038331241/2500000000 : ℝ)|^2155 ≤ (31584827522111/100000000000000 : ℝ)^1643
        have hw : |(1038331241/2500000000 : ℝ)|=(1038331241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1350_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (349/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14711/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11167/100000 : ℝ) ^ (4309/1024 : ℝ) ≤ (9856198057064157/100000000000000000000 : ℝ) := by
    have hpowers : (11167/100000 : ℝ)^4309 ≤ (9856198057064157/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11167 : ℕ)^4309*100000000000000000000^1024 ≤ 9856198057064157^1024*100000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11167 100000 9856198057064157 100000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11167/100000 : ℝ)) (X := (9856198057064157/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14713/100000 : ℝ) ^ (4309/1024 : ℝ) ≤ (3145431954112197/10000000000000000000 : ℝ) := by
    have hpowers : (14713/100000 : ℝ)^4309 ≤ (3145431954112197/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14713 : ℕ)^4309*10000000000000000000^1024 ≤ 3145431954112197^1024*100000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14713 100000 3145431954112197 10000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14713/100000 : ℝ)) (X := (3145431954112197/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009856198057064157/50000000000000000000 : ℝ) ≤ (10000468414413289/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (50009856198057064157/50000000000000000000 : ℝ)^1024 ≤ (10000468414413289/10000000000000000 : ℝ)^4309 := by
      have hnat : (50009856198057064157 : ℕ)^1024*10000000000000000^4309 ≤ 10000468414413289^4309*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009856198057064157 50000000000000000000 10000468414413289 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000468414413289/10000000000000000 : ℝ)) (X := (50009856198057064157/50000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041310517598186127/100000000000000000000 : ℝ) ≤ (5000490778724447/5000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (100041310517598186127/100000000000000000000 : ℝ)^1024 ≤ (5000490778724447/5000000000000000 : ℝ)^4309 := by
      have hnat : (100041310517598186127 : ℕ)^1024*5000000000000000^4309 ≤ 5000490778724447^4309*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041310517598186127 100000000000000000000 5000490778724447 5000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000490778724447/5000000000000000 : ℝ)) (X := (100041310517598186127/100000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003145431954112197/5000000000000000000 : ℝ) ≤ (10001494700484499/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (5003145431954112197/5000000000000000000 : ℝ)^1024 ≤ (10001494700484499/10000000000000000 : ℝ)^4309 := by
      have hnat : (5003145431954112197 : ℕ)^1024*10000000000000000^4309 ≤ 10001494700484499^4309*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003145431954112197 5000000000000000000 10001494700484499 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001494700484499/10000000000000000 : ℝ)) (X := (5003145431954112197/5000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9856198057064157/100000000000000000000 : ℝ) ≤ ((984727790582008909/985000000000000000 : ℝ)+2*(11403178569/7880000000000 : ℝ)*(11167/100000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (984727790582008909/985000000000000000 : ℝ)+2*(11403178569/7880000000000 : ℝ)*(11167/100000 : ℝ)=(10000468414413289/10000000000000000 : ℝ) by norm_num, show 1+2*(9856198057064157/100000000000000000000 : ℝ)=(50009856198057064157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3145431954112197/10000000000000000000 : ℝ)+(9856198057064157/100000000000000000000 : ℝ) ≤ ((984727790582008909/985000000000000000 : ℝ)+(11403178569/7880000000000 : ℝ)*((14713/100000 : ℝ)+(11167/100000 : ℝ)))^(4309/1024 : ℝ) := by
    rw [show (984727790582008909/985000000000000000 : ℝ)+(11403178569/7880000000000 : ℝ)*((14713/100000 : ℝ)+(11167/100000 : ℝ))=(5000490778724447/5000000000000000 : ℝ) by norm_num, show 1+(3145431954112197/10000000000000000000 : ℝ)+(9856198057064157/100000000000000000000 : ℝ)=(100041310517598186127/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3145431954112197/10000000000000000000 : ℝ) ≤ ((984727790582008909/985000000000000000 : ℝ)+2*(11403178569/7880000000000 : ℝ)*(14713/100000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (984727790582008909/985000000000000000 : ℝ)+2*(11403178569/7880000000000 : ℝ)*(14713/100000 : ℝ)=(10001494700484499/10000000000000000 : ℝ) by norm_num, show 1+2*(3145431954112197/10000000000000000000 : ℝ)=(5003145431954112197/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (984727790582008909/985000000000000000 : ℝ)*(X 1 0+X 2 0)+(11403178569/7880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (984727790582008909/985000000000000000 : ℝ)) (alpha := (11403178569/7880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (984727790582008909/985000000000000000 : ℝ)*(X 0 1+X 2 1)+(11403178569/7880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (984727790582008909/985000000000000000 : ℝ)) (alpha := (11403178569/7880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (984727790582008909/985000000000000000 : ℝ)*(X 0 2+X 1 2)+(11403178569/7880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (984727790582008909/985000000000000000 : ℝ)) (alpha := (11403178569/7880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-254635197/1250000000 : ℝ)*X 0 0+(1353063107/2500000000 : ℝ)*X 0 1+(5244891397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337212111/2500000000 : ℝ)*X 1 0+(-2122346017/10000000000 : ℝ)*X 1 1+(5244891489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213953939/400000000 : ℝ)*X 2 0+(1048978279/2000000000 : ℝ)*X 2 1+(-21223461/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162267127/5000000000 : ℝ)*X 0 0+(1038014871/2500000000 : ℝ)*X 0 1+(2251832279/5000000000 : ℝ)*X 0 2+(2162267127/5000000000 : ℝ)*X 1 0+(1038014871/2500000000 : ℝ)*X 1 1+(2251832279/5000000000 : ℝ)*X 1 2+(2162267127/5000000000 : ℝ)*X 2 0+(1038014871/2500000000 : ℝ)*X 2 1+(2251832279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1018546829/5000000000 : ℝ)*X 0 0+(5245490697/10000000000 : ℝ)*X 0 1+(1082330007/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530570053/1000000000 : ℝ)*X 1 0+(-977793727/5000000000 : ℝ)*X 1 1+(1082330007/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305700531/10000000000 : ℝ)*X 2 0+(2705825017/5000000000 : ℝ)*X 2 1+(-977793727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081139903/2500000000 : ℝ)*X 0 0+(2251202789/5000000000 : ℝ)*X 0 1+(1038331241/2500000000 : ℝ)*X 0 2+(1081139903/2500000000 : ℝ)*X 1 0+(2251202789/5000000000 : ℝ)*X 1 1+(1038331241/2500000000 : ℝ)*X 1 2+(1081139903/2500000000 : ℝ)*X 2 0+(2251202789/5000000000 : ℝ)*X 2 1+(1038331241/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (97031396747457547329992319/9850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225692353/12500000000000 : ℝ)*(base19) + (1701883069/100000000000000 : ℝ)*(base23) + (36983481/50000000000000 : ℝ)*(lower2) + (74980741/25000000000000 : ℝ)*(upper3) + (2040303/2000000000000 : ℝ)*(upper5) + (881932226572499/20000000000000 : ℝ)*(major0) + (881932226572499/20000000000000 : ℝ)*(major1) + (881932226572499/20000000000000 : ℝ)*(major2) + (119502973005133/2000000000000 : ℝ)*(sp0) + (597518364053559/10000000000000 : ℝ)*(sp1) + (373448984011959/6250000000000 : ℝ)*(sp2) + (1422058195038951/50000000000000 : ℝ)*(sp3) + (36795817763/100000000000000 : ℝ)*(sp4) + (10050604613/50000000000000 : ℝ)*(sp7) + (355517061410891/12500000000000 : ℝ)*(f.failure) + (5975185446074413/100000000000000 : ℝ)*(f.sum) + (1784472531051/394000000000000000000000000 : ℝ)*base65 + (142631711784131409/19700000000000000000000000000000 : ℝ)*base68 + (229840552925731409/19700000000000000000000000000000 : ℝ)*base70 + (125293252692231409/19700000000000000000000000000000 : ℝ)*base72 + (889764644251/394000000000000000000000000 : ℝ)*base73 + (249008293499231409/19700000000000000000000000000000 : ℝ)*base76 + (18213477960231409/19700000000000000000000000000000 : ℝ)*base78 + (344942592803431409/19700000000000000000000000000000 : ℝ)*base80 + (407926380333/78800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (999217/250000000000000000000 : ℝ)*base89 + (999217/250000000000000000000 : ℝ)*base91 + (999217/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14577687426752602879514397/6156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206500549/50000000000000 : ℝ)*(base19) + (449635723/100000000000000 : ℝ)*(base23) + (141121679/100000000000000 : ℝ)*(lower1) + (24188843/50000000000000 : ℝ)*(upper3) + (16091199/100000000000000 : ℝ)*(lower4) + (48803381/100000000000000 : ℝ)*(upper5) + (555185908302013/12500000000000 : ℝ)*(major0) + (555185908302013/12500000000000 : ℝ)*(major1) + (555185908302013/12500000000000 : ℝ)*(major2) + (158999731/25000000000000 : ℝ)*(sp2) + (6018310791683703/100000000000000 : ℝ)*(sp4) + (1203662075736521/20000000000000 : ℝ)*(sp5) + (188072178314033/3125000000000 : ℝ)*(sp6) + (716165915554211/25000000000000 : ℝ)*(sp7) + (716165915554211/25000000000000 : ℝ)*(f.failure) + (6018310791683703/100000000000000 : ℝ)*(f.sum) + (610211873/3940000000000000000000000 : ℝ)*base65 + (583380927045071317/12312500000000000000000000000000 : ℝ)*base67 + (61811035769696317/12312500000000000000000000000000 : ℝ)*base69 + (29001769799133817/12312500000000000000000000000000 : ℝ)*base71 + (856458179837/98500000000000000000000000 : ℝ)*base73 + (1003061502689071317/12312500000000000000000000000000 : ℝ)*base75 + (65692909159008817/12312500000000000000000000000000 : ℝ)*base77 + (108464212612508817/12312500000000000000000000000000 : ℝ)*base79 + (20124964859/49250000000000000000000000 : ℝ)*base82 + (4147943/500000000000000000000 : ℝ)*base90 + (4147943/500000000000000000000 : ℝ)*base92 + (4147943/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1350_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (349/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1350_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1350_s8_0 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-81483407/400000000 : ℝ)*x 0 + (5412238893/10000000000 : ℝ)*x 1 + (327806399/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81483407/400000000 : ℝ)^2155 ≤ (6203676291763/50000000000000 : ℝ)^1643 := by
    have hnat : (81483407 : ℕ)^2155*50000000000000^1643 ≤ 6203676291763^1643*400000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81483407 400000000 6203676291763 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412238893/10000000000 : ℝ)^2155 ≤ (5587281402251/12500000000000 : ℝ)^1643 := by
    have hnat : (5412238893 : ℕ)^2155*12500000000000^1643 ≤ 5587281402251^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412238893 10000000000 5587281402251 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327806399/625000000 : ℝ)^2155 ≤ (2680899761113/6250000000000 : ℝ)^1643 := by
    have hnat : (327806399 : ℕ)^2155*6250000000000^1643 ≤ 2680899761113^1643*625000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327806399 625000000 2680899761113 6250000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81483407/400000000 : ℝ), (5412238893/10000000000 : ℝ), (327806399/625000000 : ℝ)] ![(6203676291763/50000000000000 : ℝ), (5587281402251/12500000000000 : ℝ), (2680899761113/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81483407/400000000 : ℝ)|^2155 ≤ (6203676291763/50000000000000 : ℝ)^1643
        have hw : |(-81483407/400000000 : ℝ)|=(81483407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412238893/10000000000 : ℝ)|^2155 ≤ (5587281402251/12500000000000 : ℝ)^1643
        have hw : |(5412238893/10000000000 : ℝ)|=(5412238893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327806399/625000000 : ℝ)|^2155 ≤ (2680899761113/6250000000000 : ℝ)^1643
        have hw : |(327806399/625000000 : ℝ)|=(327806399/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s8_1 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674421887/5000000000 : ℝ)*x 0 + (-2122337779/10000000000 : ℝ)*x 1 + (2622451201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674421887/5000000000 : ℝ)^2155 ≤ (88025577701/200000000000 : ℝ)^1643 := by
    have hnat : (2674421887 : ℕ)^2155*200000000000^1643 ≤ 88025577701^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674421887 5000000000 88025577701 200000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122337779/10000000000 : ℝ)^2155 ≤ (13092814768943/100000000000000 : ℝ)^1643 := by
    have hnat : (2122337779 : ℕ)^2155*100000000000000^1643 ≤ 13092814768943^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122337779 10000000000 13092814768943 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622451201/5000000000 : ℝ)^2155 ≤ (42894396370891/100000000000000 : ℝ)^1643 := by
    have hnat : (2622451201 : ℕ)^2155*100000000000000^1643 ≤ 42894396370891^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622451201 5000000000 42894396370891 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674421887/5000000000 : ℝ), (-2122337779/10000000000 : ℝ), (2622451201/5000000000 : ℝ)] ![(88025577701/200000000000 : ℝ), (13092814768943/100000000000000 : ℝ), (42894396370891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674421887/5000000000 : ℝ)|^2155 ≤ (88025577701/200000000000 : ℝ)^1643
        have hw : |(2674421887/5000000000 : ℝ)|=(2674421887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2122337779/10000000000 : ℝ)|^2155 ≤ (13092814768943/100000000000000 : ℝ)^1643
        have hw : |(-2122337779/10000000000 : ℝ)|=(2122337779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622451201/5000000000 : ℝ)|^2155 ≤ (42894396370891/100000000000000 : ℝ)^1643
        have hw : |(2622451201/5000000000 : ℝ)|=(2622451201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s8_2 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674422367/5000000000 : ℝ)*x 0 + (5244901813/10000000000 : ℝ)*x 1 + (-414519/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674422367/5000000000 : ℝ)^2155 ≤ (44012799211459/100000000000000 : ℝ)^1643 := by
    have hnat : (2674422367 : ℕ)^2155*100000000000000^1643 ≤ 44012799211459^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674422367 5000000000 44012799211459 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244901813/10000000000 : ℝ)^2155 ≤ (42894390052767/100000000000000 : ℝ)^1643 := by
    have hnat : (5244901813 : ℕ)^2155*100000000000000^1643 ≤ 42894390052767^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244901813 10000000000 42894390052767 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414519/1953125 : ℝ)^2155 ≤ (3273202682823/25000000000000 : ℝ)^1643 := by
    have hnat : (414519 : ℕ)^2155*25000000000000^1643 ≤ 3273202682823^1643*1953125^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414519 1953125 3273202682823 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674422367/5000000000 : ℝ), (5244901813/10000000000 : ℝ), (-414519/1953125 : ℝ)] ![(44012799211459/100000000000000 : ℝ), (42894390052767/100000000000000 : ℝ), (3273202682823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674422367/5000000000 : ℝ)|^2155 ≤ (44012799211459/100000000000000 : ℝ)^1643
        have hw : |(2674422367/5000000000 : ℝ)|=(2674422367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244901813/10000000000 : ℝ)|^2155 ≤ (42894390052767/100000000000000 : ℝ)^1643
        have hw : |(5244901813/10000000000 : ℝ)|=(5244901813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-414519/1953125 : ℝ)|^2155 ≤ (3273202682823/25000000000000 : ℝ)^1643
        have hw : |(-414519/1953125 : ℝ)|=(414519/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s8_3 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (432453509/1000000000 : ℝ)*x 0 + (4152085547/10000000000 : ℝ)*x 1 + (4503638321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432453509/1000000000 : ℝ)^2155 ≤ (16651717158613/50000000000000 : ℝ)^1643 := by
    have hnat : (432453509 : ℕ)^2155*50000000000000^1643 ≤ 16651717158613^1643*1000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432453509 1000000000 16651717158613 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152085547/10000000000 : ℝ)^2155 ≤ (315724654987/1000000000000 : ℝ)^1643 := by
    have hnat : (4152085547 : ℕ)^2155*1000000000000^1643 ≤ 315724654987^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152085547 10000000000 315724654987 1000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503638321/10000000000 : ℝ)^2155 ≤ (17562050083107/50000000000000 : ℝ)^1643 := by
    have hnat : (4503638321 : ℕ)^2155*50000000000000^1643 ≤ 17562050083107^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503638321 10000000000 17562050083107 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432453509/1000000000 : ℝ), (4152085547/10000000000 : ℝ), (4503638321/10000000000 : ℝ)] ![(16651717158613/50000000000000 : ℝ), (315724654987/1000000000000 : ℝ), (17562050083107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432453509/1000000000 : ℝ)|^2155 ≤ (16651717158613/50000000000000 : ℝ)^1643
        have hw : |(432453509/1000000000 : ℝ)|=(432453509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152085547/10000000000 : ℝ)|^2155 ≤ (315724654987/1000000000000 : ℝ)^1643
        have hw : |(4152085547/10000000000 : ℝ)|=(4152085547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503638321/10000000000 : ℝ)|^2155 ≤ (17562050083107/50000000000000 : ℝ)^1643
        have hw : |(4503638321/10000000000 : ℝ)|=(4503638321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s8_4 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-509274357/2500000000 : ℝ)*x 0 + (2622750711/5000000000 : ℝ)*x 1 + (5411636633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509274357/2500000000 : ℝ)^2155 ≤ (2481490093991/20000000000000 : ℝ)^1643 := by
    have hnat : (509274357 : ℕ)^2155*20000000000000^1643 ≤ 2481490093991^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509274357 2500000000 2481490093991 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622750711/5000000000 : ℝ)^2155 ≤ (2145041104629/5000000000000 : ℝ)^1643 := by
    have hnat : (2622750711 : ℕ)^2155*5000000000000^1643 ≤ 2145041104629^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622750711 5000000000 2145041104629 5000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411636633/10000000000 : ℝ)^2155 ≤ (2234586371549/5000000000000 : ℝ)^1643 := by
    have hnat : (5411636633 : ℕ)^2155*5000000000000^1643 ≤ 2234586371549^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411636633 10000000000 2234586371549 5000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509274357/2500000000 : ℝ), (2622750711/5000000000 : ℝ), (5411636633/10000000000 : ℝ)] ![(2481490093991/20000000000000 : ℝ), (2145041104629/5000000000000 : ℝ), (2234586371549/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509274357/2500000000 : ℝ)|^2155 ≤ (2481490093991/20000000000000 : ℝ)^1643
        have hw : |(-509274357/2500000000 : ℝ)|=(509274357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622750711/5000000000 : ℝ)|^2155 ≤ (2145041104629/5000000000000 : ℝ)^1643
        have hw : |(2622750711/5000000000 : ℝ)|=(2622750711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411636633/10000000000 : ℝ)|^2155 ≤ (2234586371549/5000000000000 : ℝ)^1643
        have hw : |(5411636633/10000000000 : ℝ)|=(5411636633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s8_5 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652851347/5000000000 : ℝ)*x 0 + (-977801491/5000000000 : ℝ)*x 1 + (5411636577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652851347/5000000000 : ℝ)^2155 ≤ (4354776785587/10000000000000 : ℝ)^1643 := by
    have hnat : (2652851347 : ℕ)^2155*10000000000000^1643 ≤ 4354776785587^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652851347 5000000000 4354776785587 10000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977801491/5000000000 : ℝ)^2155 ≤ (588025265293/5000000000000 : ℝ)^1643 := by
    have hnat : (977801491 : ℕ)^2155*5000000000000^1643 ≤ 588025265293^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977801491 5000000000 588025265293 5000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411636577/10000000000 : ℝ)^2155 ≤ (44691726824389/100000000000000 : ℝ)^1643 := by
    have hnat : (5411636577 : ℕ)^2155*100000000000000^1643 ≤ 44691726824389^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411636577 10000000000 44691726824389 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652851347/5000000000 : ℝ), (-977801491/5000000000 : ℝ), (5411636577/10000000000 : ℝ)] ![(4354776785587/10000000000000 : ℝ), (588025265293/5000000000000 : ℝ), (44691726824389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652851347/5000000000 : ℝ)|^2155 ≤ (4354776785587/10000000000000 : ℝ)^1643
        have hw : |(2652851347/5000000000 : ℝ)|=(2652851347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-977801491/5000000000 : ℝ)|^2155 ≤ (588025265293/5000000000000 : ℝ)^1643
        have hw : |(-977801491/5000000000 : ℝ)|=(977801491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411636577/10000000000 : ℝ)|^2155 ≤ (44691726824389/100000000000000 : ℝ)^1643
        have hw : |(5411636577/10000000000 : ℝ)|=(5411636577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s8_6 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326425721/2500000000 : ℝ)*x 0 + (2705818293/5000000000 : ℝ)*x 1 + (-195560271/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326425721/2500000000 : ℝ)^2155 ≤ (10886942475327/25000000000000 : ℝ)^1643 := by
    have hnat : (1326425721 : ℕ)^2155*25000000000000^1643 ≤ 10886942475327^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326425721 2500000000 10886942475327 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705818293/5000000000 : ℝ)^2155 ≤ (44691726921877/100000000000000 : ℝ)^1643 := by
    have hnat : (2705818293 : ℕ)^2155*100000000000000^1643 ≤ 44691726921877^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705818293 5000000000 44691726921877 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195560271/1000000000 : ℝ)^2155 ≤ (11760503160383/100000000000000 : ℝ)^1643 := by
    have hnat : (195560271 : ℕ)^2155*100000000000000^1643 ≤ 11760503160383^1643*1000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195560271 1000000000 11760503160383 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326425721/2500000000 : ℝ), (2705818293/5000000000 : ℝ), (-195560271/1000000000 : ℝ)] ![(10886942475327/25000000000000 : ℝ), (44691726921877/100000000000000 : ℝ), (11760503160383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326425721/2500000000 : ℝ)|^2155 ≤ (10886942475327/25000000000000 : ℝ)^1643
        have hw : |(1326425721/2500000000 : ℝ)|=(1326425721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705818293/5000000000 : ℝ)|^2155 ≤ (44691726921877/100000000000000 : ℝ)^1643
        have hw : |(2705818293/5000000000 : ℝ)|=(2705818293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195560271/1000000000 : ℝ)|^2155 ≤ (11760503160383/100000000000000 : ℝ)^1643
        have hw : |(-195560271/1000000000 : ℝ)|=(195560271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1350_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (349/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11169/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14711/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (349/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (349/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (349/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (349/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (349/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (349/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (349/3125 : ℝ) ^ (4309/1024 : ℝ) ≤ (4929956327546689/50000000000000000000 : ℝ) := by
    have hpowers : (349/3125 : ℝ)^4309 ≤ (4929956327546689/50000000000000000000 : ℝ)^1024 := by
      have hnat : (349 : ℕ)^4309*50000000000000000000^1024 ≤ 4929956327546689^1024*3125^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        349 3125 4929956327546689 50000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (349/3125 : ℝ)) (X := (4929956327546689/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14711/100000 : ℝ) ^ (4309/1024 : ℝ) ≤ (314363312089523/1000000000000000000 : ℝ) := by
    have hpowers : (14711/100000 : ℝ)^4309 ≤ (314363312089523/1000000000000000000 : ℝ)^1024 := by
      have hnat : (14711 : ℕ)^4309*1000000000000000000^1024 ≤ 314363312089523^1024*100000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14711 100000 314363312089523 1000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14711/100000 : ℝ)) (X := (314363312089523/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004929956327546689/25000000000000000000 : ℝ) ≤ (2000093718187153/2000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (25004929956327546689/25000000000000000000 : ℝ)^1024 ≤ (2000093718187153/2000000000000000 : ℝ)^4309 := by
      have hnat : (25004929956327546689 : ℕ)^1024*2000000000000000^4309 ≤ 2000093718187153^4309*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004929956327546689 25000000000000000000 2000093718187153 2000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000093718187153/2000000000000000 : ℝ)) (X := (25004929956327546689/25000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020648121932022839/50000000000000000000 : ℝ) ≤ (312530663073487/312500000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (50020648121932022839/50000000000000000000 : ℝ)^1024 ≤ (312530663073487/312500000000000 : ℝ)^4309 := by
      have hnat : (50020648121932022839 : ℕ)^1024*312500000000000^4309 ≤ 312530663073487^4309*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020648121932022839 50000000000000000000 312530663073487 312500000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312530663073487/312500000000000 : ℝ)) (X := (50020648121932022839/50000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (500314363312089523/500000000000000000 : ℝ) ≤ (10001493845767403/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (500314363312089523/500000000000000000 : ℝ)^1024 ≤ (10001493845767403/10000000000000000 : ℝ)^4309 := by
      have hnat : (500314363312089523 : ℕ)^1024*10000000000000000^4309 ≤ 10001493845767403^4309*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500314363312089523 500000000000000000 10001493845767403 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001493845767403/10000000000000000 : ℝ)) (X := (500314363312089523/500000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4929956327546689/50000000000000000000 : ℝ) ≤ ((11806736723908560737/11810000000000000000 : ℝ)+2*(170875805273/118100000000000 : ℝ)*(349/3125 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (11806736723908560737/11810000000000000000 : ℝ)+2*(170875805273/118100000000000 : ℝ)*(349/3125 : ℝ)=(2000093718187153/2000000000000000 : ℝ) by norm_num, show 1+2*(4929956327546689/50000000000000000000 : ℝ)=(25004929956327546689/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(314363312089523/1000000000000000000 : ℝ)+(4929956327546689/50000000000000000000 : ℝ) ≤ ((11806736723908560737/11810000000000000000 : ℝ)+(170875805273/118100000000000 : ℝ)*((14711/100000 : ℝ)+(349/3125 : ℝ)))^(4309/1024 : ℝ) := by
    rw [show (11806736723908560737/11810000000000000000 : ℝ)+(170875805273/118100000000000 : ℝ)*((14711/100000 : ℝ)+(349/3125 : ℝ))=(312530663073487/312500000000000 : ℝ) by norm_num, show 1+(314363312089523/1000000000000000000 : ℝ)+(4929956327546689/50000000000000000000 : ℝ)=(50020648121932022839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(314363312089523/1000000000000000000 : ℝ) ≤ ((11806736723908560737/11810000000000000000 : ℝ)+2*(170875805273/118100000000000 : ℝ)*(14711/100000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (11806736723908560737/11810000000000000000 : ℝ)+2*(170875805273/118100000000000 : ℝ)*(14711/100000 : ℝ)=(10001493845767403/10000000000000000 : ℝ) by norm_num, show 1+2*(314363312089523/1000000000000000000 : ℝ)=(500314363312089523/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11806736723908560737/11810000000000000000 : ℝ)*(X 1 0+X 2 0)+(170875805273/118100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (349/3125 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (11806736723908560737/11810000000000000000 : ℝ)) (alpha := (170875805273/118100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11806736723908560737/11810000000000000000 : ℝ)*(X 0 1+X 2 1)+(170875805273/118100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (349/3125 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (11806736723908560737/11810000000000000000 : ℝ)) (alpha := (170875805273/118100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11806736723908560737/11810000000000000000 : ℝ)*(X 0 2+X 1 2)+(170875805273/118100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (349/3125 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (11806736723908560737/11810000000000000000 : ℝ)) (alpha := (170875805273/118100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-81483407/400000000 : ℝ)*X 0 0+(5412238893/10000000000 : ℝ)*X 0 1+(327806399/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674421887/5000000000 : ℝ)*X 1 0+(-2122337779/10000000000 : ℝ)*X 1 1+(2622451201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674422367/5000000000 : ℝ)*X 2 0+(5244901813/10000000000 : ℝ)*X 2 1+(-414519/1953125 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((432453509/1000000000 : ℝ)*X 0 0+(4152085547/10000000000 : ℝ)*X 0 1+(4503638321/10000000000 : ℝ)*X 0 2+(432453509/1000000000 : ℝ)*X 1 0+(4152085547/10000000000 : ℝ)*X 1 1+(4503638321/10000000000 : ℝ)*X 1 2+(432453509/1000000000 : ℝ)*X 2 0+(4152085547/10000000000 : ℝ)*X 2 1+(4503638321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-509274357/2500000000 : ℝ)*X 0 0+(2622750711/5000000000 : ℝ)*X 0 1+(5411636633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652851347/5000000000 : ℝ)*X 1 0+(-977801491/5000000000 : ℝ)*X 1 1+(5411636577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326425721/2500000000 : ℝ)*X 2 0+(2705818293/5000000000 : ℝ)*X 2 1+(-195560271/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (553593081213296260359007677/147625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74116323/100000000000000 : ℝ)*(base23) + (34678657/10000000000000 : ℝ)*(lower2) + (5119427/20000000000000 : ℝ)*(upper3) + (198512501/100000000000000 : ℝ)*(upper4) + (1102561887265207/25000000000000 : ℝ)*(major0) + (1102561887265207/25000000000000 : ℝ)*(major1) + (1102561887265207/25000000000000 : ℝ)*(major2) + (2987985599727079/50000000000000 : ℝ)*(sp0) + (2987985154694219/50000000000000 : ℝ)*(sp1) + (5975972842810439/100000000000000 : ℝ)*(sp2) + (2844514717109591/100000000000000 : ℝ)*(sp3) + (4528279027/50000000000000 : ℝ)*(sp4) + (4973311887/50000000000000 : ℝ)*(sp5) + (146781709/2000000000000 : ℝ)*(sp6) + (2844514717109591/100000000000000 : ℝ)*(f.failure) + (1493995064003053/25000000000000 : ℝ)*(f.sum) + (2690713480463/738125000000000000000000000 : ℝ)*base65 + (3201901990157272441/295250000000000000000000000000000 : ℝ)*base68 + (2436980220028772441/295250000000000000000000000000000 : ℝ)*base70 + (798505451337977559/295250000000000000000000000000000 : ℝ)*base71 + (6944851535291/5905000000000000000000000000 : ℝ)*base74 + (1829622868133772441/295250000000000000000000000000000 : ℝ)*base76 + (759330542263477559/295250000000000000000000000000000 : ℝ)*base77 + (115352503963522441/295250000000000000000000000000000 : ℝ)*base80 + (16714633522689/5905000000000000000000000000 : ℝ)*base81 + (2976117/2000000000000000000000 : ℝ)*base89 + (2976117/2000000000000000000000 : ℝ)*base91 + (2976117/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1350_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (349/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1350_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1350_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1350_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1350_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1350_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

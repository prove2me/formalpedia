-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1659_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:19.063611+00:00
-- url     : https://prove2.me/submissions/3acce87c-486f-4b53-a010-f9c6c09ffdf4

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
theorem support_rectangle_w1659_s3_0 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1588273593/10000000000 : ℝ)*x 0 + (5444937411/10000000000 : ℝ)*x 1 + (1296104561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1588273593/10000000000 : ℝ)^4955 ≤ (9834936119943/100000000000000 : ℝ)^3931 := by
    have hnat : (1588273593 : ℕ)^4955*100000000000000^3931 ≤ 9834936119943^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588273593 10000000000 9834936119943 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444937411/10000000000 : ℝ)^4955 ≤ (46475144943087/100000000000000 : ℝ)^3931 := by
    have hnat : (5444937411 : ℕ)^4955*100000000000000^3931 ≤ 46475144943087^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444937411 10000000000 46475144943087 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296104561/2500000000 : ℝ)^4955 ≤ (43689918927853/100000000000000 : ℝ)^3931 := by
    have hnat : (1296104561 : ℕ)^4955*100000000000000^3931 ≤ 43689918927853^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296104561 2500000000 43689918927853 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1588273593/10000000000 : ℝ), (5444937411/10000000000 : ℝ), (1296104561/2500000000 : ℝ)] ![(9834936119943/100000000000000 : ℝ), (46475144943087/100000000000000 : ℝ), (43689918927853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1588273593/10000000000 : ℝ)|^4955 ≤ (9834936119943/100000000000000 : ℝ)^3931
        have hw : |(-1588273593/10000000000 : ℝ)|=(1588273593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444937411/10000000000 : ℝ)|^4955 ≤ (46475144943087/100000000000000 : ℝ)^3931
        have hw : |(5444937411/10000000000 : ℝ)|=(5444937411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296104561/2500000000 : ℝ)|^4955 ≤ (43689918927853/100000000000000 : ℝ)^3931
        have hw : |(1296104561/2500000000 : ℝ)|=(1296104561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s3_1 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069279/2000000 : ℝ)*x 0 + (-21529259/125000000 : ℝ)*x 1 + (1296104511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069279/2000000 : ℝ)^4955 ≤ (11354361472063/25000000000000 : ℝ)^3931 := by
    have hnat : (1069279 : ℕ)^4955*25000000000000^3931 ≤ 11354361472063^3931*2000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069279 2000000 11354361472063 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21529259/125000000 : ℝ)^4955 ≤ (2723159320903/25000000000000 : ℝ)^3931 := by
    have hnat : (21529259 : ℕ)^4955*25000000000000^3931 ≤ 2723159320903^3931*125000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21529259 125000000 2723159320903 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296104511/2500000000 : ℝ)^4955 ≤ (43689916803377/100000000000000 : ℝ)^3931 := by
    have hnat : (1296104511 : ℕ)^4955*100000000000000^3931 ≤ 43689916803377^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296104511 2500000000 43689916803377 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069279/2000000 : ℝ), (-21529259/125000000 : ℝ), (1296104511/2500000000 : ℝ)] ![(11354361472063/25000000000000 : ℝ), (2723159320903/25000000000000 : ℝ), (43689916803377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069279/2000000 : ℝ)|^4955 ≤ (11354361472063/25000000000000 : ℝ)^3931
        have hw : |(1069279/2000000 : ℝ)|=(1069279/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21529259/125000000 : ℝ)|^4955 ≤ (2723159320903/25000000000000 : ℝ)^3931
        have hw : |(-21529259/125000000 : ℝ)|=(21529259/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296104511/2500000000 : ℝ)|^4955 ≤ (43689916803377/100000000000000 : ℝ)^3931
        have hw : |(1296104511/2500000000 : ℝ)|=(1296104511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s3_2 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346395023/10000000000 : ℝ)*x 0 + (5184418129/10000000000 : ℝ)*x 1 + (-53823143/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346395023/10000000000 : ℝ)^4955 ≤ (45417446134533/100000000000000 : ℝ)^3931 := by
    have hnat : (5346395023 : ℕ)^4955*100000000000000^3931 ≤ 45417446134533^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346395023 10000000000 45417446134533 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184418129/10000000000 : ℝ)^4955 ≤ (43689917706279/100000000000000 : ℝ)^3931 := by
    have hnat : (5184418129 : ℕ)^4955*100000000000000^3931 ≤ 43689917706279^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184418129 10000000000 43689917706279 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53823143/312500000 : ℝ)^4955 ≤ (10892636135677/100000000000000 : ℝ)^3931 := by
    have hnat : (53823143 : ℕ)^4955*100000000000000^3931 ≤ 10892636135677^3931*312500000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53823143 312500000 10892636135677 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346395023/10000000000 : ℝ), (5184418129/10000000000 : ℝ), (-53823143/312500000 : ℝ)] ![(45417446134533/100000000000000 : ℝ), (43689917706279/100000000000000 : ℝ), (10892636135677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346395023/10000000000 : ℝ)|^4955 ≤ (45417446134533/100000000000000 : ℝ)^3931
        have hw : |(5346395023/10000000000 : ℝ)|=(5346395023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184418129/10000000000 : ℝ)|^4955 ≤ (43689917706279/100000000000000 : ℝ)^3931
        have hw : |(5184418129/10000000000 : ℝ)|=(5184418129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53823143/312500000 : ℝ)|^4955 ≤ (10892636135677/100000000000000 : ℝ)^3931
        have hw : |(-53823143/312500000 : ℝ)|=(53823143/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s3_3 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (417387483/1000000000 : ℝ)*x 0 + (480374881/1250000000 : ℝ)*x 1 + (4524674899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417387483/1000000000 : ℝ)^4955 ≤ (8310600585311/25000000000000 : ℝ)^3931 := by
    have hnat : (417387483 : ℕ)^4955*25000000000000^3931 ≤ 8310600585311^3931*1000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417387483 1000000000 8310600585311 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480374881/1250000000 : ℝ)^4955 ≤ (29955707286563/100000000000000 : ℝ)^3931 := by
    have hnat : (480374881 : ℕ)^4955*100000000000000^3931 ≤ 29955707286563^3931*1250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480374881 1250000000 29955707286563 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524674899/10000000000 : ℝ)^4955 ≤ (9200472587829/25000000000000 : ℝ)^3931 := by
    have hnat : (4524674899 : ℕ)^4955*25000000000000^3931 ≤ 9200472587829^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524674899 10000000000 9200472587829 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417387483/1000000000 : ℝ), (480374881/1250000000 : ℝ), (4524674899/10000000000 : ℝ)] ![(8310600585311/25000000000000 : ℝ), (29955707286563/100000000000000 : ℝ), (9200472587829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417387483/1000000000 : ℝ)|^4955 ≤ (8310600585311/25000000000000 : ℝ)^3931
        have hw : |(417387483/1000000000 : ℝ)|=(417387483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(480374881/1250000000 : ℝ)|^4955 ≤ (29955707286563/100000000000000 : ℝ)^3931
        have hw : |(480374881/1250000000 : ℝ)|=(480374881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524674899/10000000000 : ℝ)|^4955 ≤ (9200472587829/25000000000000 : ℝ)^3931
        have hw : |(4524674899/10000000000 : ℝ)|=(4524674899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s3_4 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-794168601/5000000000 : ℝ)*x 0 + (5186397941/10000000000 : ℝ)*x 1 + (5442936497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (794168601/5000000000 : ℝ)^4955 ≤ (2458858151677/25000000000000 : ℝ)^3931 := by
    have hnat : (794168601 : ℕ)^4955*25000000000000^3931 ≤ 2458858151677^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794168601 5000000000 2458858151677 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186397941/10000000000 : ℝ)^4955 ≤ (43710949066979/100000000000000 : ℝ)^3931 := by
    have hnat : (5186397941 : ℕ)^4955*100000000000000^3931 ≤ 43710949066979^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186397941 10000000000 43710949066979 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442936497/10000000000 : ℝ)^4955 ≤ (2322680915497/5000000000000 : ℝ)^3931 := by
    have hnat : (5442936497 : ℕ)^4955*5000000000000^3931 ≤ 2322680915497^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442936497 10000000000 2322680915497 5000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-794168601/5000000000 : ℝ), (5186397941/10000000000 : ℝ), (5442936497/10000000000 : ℝ)] ![(2458858151677/25000000000000 : ℝ), (43710949066979/100000000000000 : ℝ), (2322680915497/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-794168601/5000000000 : ℝ)|^4955 ≤ (2458858151677/25000000000000 : ℝ)^3931
        have hw : |(-794168601/5000000000 : ℝ)|=(794168601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186397941/10000000000 : ℝ)|^4955 ≤ (43710949066979/100000000000000 : ℝ)^3931
        have hw : |(5186397941/10000000000 : ℝ)|=(5186397941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442936497/10000000000 : ℝ)|^4955 ≤ (2322680915497/5000000000000 : ℝ)^3931
        have hw : |(5442936497/10000000000 : ℝ)|=(5442936497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s3_5 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638362891/5000000000 : ℝ)*x 0 + (-292764421/2000000000 : ℝ)*x 1 + (5442936511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638362891/5000000000 : ℝ)^4955 ≤ (22336354301973/50000000000000 : ℝ)^3931 := by
    have hnat : (2638362891 : ℕ)^4955*50000000000000^3931 ≤ 22336354301973^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638362891 5000000000 22336354301973 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292764421/2000000000 : ℝ)^4955 ≤ (8873672923541/100000000000000 : ℝ)^3931 := by
    have hnat : (292764421 : ℕ)^4955*100000000000000^3931 ≤ 8873672923541^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292764421 2000000000 8873672923541 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442936511/10000000000 : ℝ)^4955 ≤ (929072369211/2000000000000 : ℝ)^3931 := by
    have hnat : (5442936511 : ℕ)^4955*2000000000000^3931 ≤ 929072369211^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442936511 10000000000 929072369211 2000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638362891/5000000000 : ℝ), (-292764421/2000000000 : ℝ), (5442936511/10000000000 : ℝ)] ![(22336354301973/50000000000000 : ℝ), (8873672923541/100000000000000 : ℝ), (929072369211/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638362891/5000000000 : ℝ)|^4955 ≤ (22336354301973/50000000000000 : ℝ)^3931
        have hw : |(2638362891/5000000000 : ℝ)|=(2638362891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-292764421/2000000000 : ℝ)|^4955 ≤ (8873672923541/100000000000000 : ℝ)^3931
        have hw : |(-292764421/2000000000 : ℝ)|=(292764421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442936511/10000000000 : ℝ)|^4955 ≤ (929072369211/2000000000000 : ℝ)^3931
        have hw : |(5442936511/10000000000 : ℝ)|=(5442936511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s3_6 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319181431/2500000000 : ℝ)*x 0 + (1360734171/2500000000 : ℝ)*x 1 + (-731910971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319181431/2500000000 : ℝ)^4955 ≤ (44672707985009/100000000000000 : ℝ)^3931 := by
    have hnat : (1319181431 : ℕ)^4955*100000000000000^3931 ≤ 44672707985009^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319181431 2500000000 44672707985009 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360734171/2500000000 : ℝ)^4955 ≤ (9290724064333/20000000000000 : ℝ)^3931 := by
    have hnat : (1360734171 : ℕ)^4955*20000000000000^3931 ≤ 9290724064333^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360734171 2500000000 9290724064333 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (731910971/5000000000 : ℝ)^4955 ≤ (4436835839021/50000000000000 : ℝ)^3931 := by
    have hnat : (731910971 : ℕ)^4955*50000000000000^3931 ≤ 4436835839021^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731910971 5000000000 4436835839021 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319181431/2500000000 : ℝ), (1360734171/2500000000 : ℝ), (-731910971/5000000000 : ℝ)] ![(44672707985009/100000000000000 : ℝ), (9290724064333/20000000000000 : ℝ), (4436835839021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319181431/2500000000 : ℝ)|^4955 ≤ (44672707985009/100000000000000 : ℝ)^3931
        have hw : |(1319181431/2500000000 : ℝ)|=(1319181431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360734171/2500000000 : ℝ)|^4955 ≤ (9290724064333/20000000000000 : ℝ)^3931
        have hw : |(1360734171/2500000000 : ℝ)|=(1360734171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-731910971/5000000000 : ℝ)|^4955 ≤ (4436835839021/50000000000000 : ℝ)^3931
        have hw : |(-731910971/5000000000 : ℝ)|=(731910971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s3_7 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1043510101/2500000000 : ℝ)*x 0 + (903898911/2000000000 : ℝ)*x 1 + (384823359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043510101/2500000000 : ℝ)^4955 ≤ (33244064559241/100000000000000 : ℝ)^3931 := by
    have hnat : (1043510101 : ℕ)^4955*100000000000000^3931 ≤ 33244064559241^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043510101 2500000000 33244064559241 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903898911/2000000000 : ℝ)^4955 ≤ (36748787581257/100000000000000 : ℝ)^3931 := by
    have hnat : (903898911 : ℕ)^4955*100000000000000^3931 ≤ 36748787581257^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903898911 2000000000 36748787581257 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384823359/1000000000 : ℝ)^4955 ≤ (30007147838543/100000000000000 : ℝ)^3931 := by
    have hnat : (384823359 : ℕ)^4955*100000000000000^3931 ≤ 30007147838543^3931*1000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384823359 1000000000 30007147838543 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1043510101/2500000000 : ℝ), (903898911/2000000000 : ℝ), (384823359/1000000000 : ℝ)] ![(33244064559241/100000000000000 : ℝ), (36748787581257/100000000000000 : ℝ), (30007147838543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1043510101/2500000000 : ℝ)|^4955 ≤ (33244064559241/100000000000000 : ℝ)^3931
        have hw : |(1043510101/2500000000 : ℝ)|=(1043510101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903898911/2000000000 : ℝ)|^4955 ≤ (36748787581257/100000000000000 : ℝ)^3931
        have hw : |(903898911/2000000000 : ℝ)|=(903898911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(384823359/1000000000 : ℝ)|^4955 ≤ (30007147838543/100000000000000 : ℝ)^3931
        have hw : |(384823359/1000000000 : ℝ)|=(384823359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1659_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10713/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8127/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (333/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (333/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (333/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (333/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (333/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (333/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (333/3125 : ℝ) ^ (4951/1024 : ℝ) ≤ (994090682256537/50000000000000000000 : ℝ) := by
    have hpowers : (333/3125 : ℝ)^4951 ≤ (994090682256537/50000000000000000000 : ℝ)^1024 := by
      have hnat : (333 : ℕ)^4951*50000000000000000000^1024 ≤ 994090682256537^1024*3125^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        333 3125 994090682256537 50000000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (333/3125 : ℝ)) (X := (994090682256537/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16317/100000 : ℝ) ^ (4951/1024 : ℝ) ≤ (1950099114893047/12500000000000000000 : ℝ) := by
    have hpowers : (16317/100000 : ℝ)^4951 ≤ (1950099114893047/12500000000000000000 : ℝ)^1024 := by
      have hnat : (16317 : ℕ)^4951*12500000000000000000^1024 ≤ 1950099114893047^1024*100000^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16317 100000 1950099114893047 12500000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16317/100000 : ℝ)) (X := (1950099114893047/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000994090682256537/25000000000000000000 : ℝ) ≤ (5000041120291103/5000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (25000994090682256537/25000000000000000000 : ℝ)^1024 ≤ (5000041120291103/5000000000000000 : ℝ)^4951 := by
      have hnat : (25000994090682256537 : ℕ)^1024*5000000000000000^4951 ≤ 5000041120291103^4951*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000994090682256537 25000000000000000000 5000041120291103 5000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000041120291103/5000000000000000 : ℝ)) (X := (25000994090682256537/25000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000351779485673149/2000000000000000000 : ℝ) ≤ (10000363761935457/10000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (2000351779485673149/2000000000000000000 : ℝ)^1024 ≤ (10000363761935457/10000000000000000 : ℝ)^4951 := by
      have hnat : (2000351779485673149 : ℕ)^1024*10000000000000000^4951 ≤ 10000363761935457^4951*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000351779485673149 2000000000000000000 10000363761935457 10000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000363761935457/10000000000000000 : ℝ)) (X := (2000351779485673149/2000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251950099114893047/6250000000000000000 : ℝ) ≤ (2500161320822177/2500000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (6251950099114893047/6250000000000000000 : ℝ)^1024 ≤ (2500161320822177/2500000000000000 : ℝ)^4951 := by
      have hnat : (6251950099114893047 : ℕ)^1024*2500000000000000^4951 ≤ 2500161320822177^4951*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251950099114893047 6250000000000000000 2500161320822177 2500000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500161320822177/2500000000000000 : ℝ)) (X := (6251950099114893047/6250000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(994090682256537/50000000000000000000 : ℝ) ≤ ((4999511197743807/5000000000000000 : ℝ)+2*(447569719/900000000000 : ℝ)*(333/3125 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (4999511197743807/5000000000000000 : ℝ)+2*(447569719/900000000000 : ℝ)*(333/3125 : ℝ)=(5000041120291103/5000000000000000 : ℝ) by norm_num, show 1+2*(994090682256537/50000000000000000000 : ℝ)=(25000994090682256537/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1950099114893047/12500000000000000000 : ℝ)+(994090682256537/50000000000000000000 : ℝ) ≤ ((4999511197743807/5000000000000000 : ℝ)+(447569719/900000000000 : ℝ)*((16317/100000 : ℝ)+(333/3125 : ℝ)))^(4951/1024 : ℝ) := by
    rw [show (4999511197743807/5000000000000000 : ℝ)+(447569719/900000000000 : ℝ)*((16317/100000 : ℝ)+(333/3125 : ℝ))=(10000363761935457/10000000000000000 : ℝ) by norm_num, show 1+(1950099114893047/12500000000000000000 : ℝ)+(994090682256537/50000000000000000000 : ℝ)=(2000351779485673149/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1950099114893047/12500000000000000000 : ℝ) ≤ ((4999511197743807/5000000000000000 : ℝ)+2*(447569719/900000000000 : ℝ)*(16317/100000 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (4999511197743807/5000000000000000 : ℝ)+2*(447569719/900000000000 : ℝ)*(16317/100000 : ℝ)=(2500161320822177/2500000000000000 : ℝ) by norm_num, show 1+2*(1950099114893047/12500000000000000000 : ℝ)=(6251950099114893047/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4999511197743807/5000000000000000 : ℝ)*(X 1 0+X 2 0)+(447569719/900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (333/3125 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (4999511197743807/5000000000000000 : ℝ)) (alpha := (447569719/900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4999511197743807/5000000000000000 : ℝ)*(X 0 1+X 2 1)+(447569719/900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (333/3125 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (4999511197743807/5000000000000000 : ℝ)) (alpha := (447569719/900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4999511197743807/5000000000000000 : ℝ)*(X 0 2+X 1 2)+(447569719/900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (333/3125 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (4999511197743807/5000000000000000 : ℝ)) (alpha := (447569719/900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1588273593/10000000000 : ℝ)*X 0 0+(5444937411/10000000000 : ℝ)*X 0 1+(1296104561/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069279/2000000 : ℝ)*X 1 0+(-21529259/125000000 : ℝ)*X 1 1+(1296104511/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346395023/10000000000 : ℝ)*X 2 0+(5184418129/10000000000 : ℝ)*X 2 1+(-53823143/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((417387483/1000000000 : ℝ)*X 0 0+(480374881/1250000000 : ℝ)*X 0 1+(4524674899/10000000000 : ℝ)*X 0 2+(417387483/1000000000 : ℝ)*X 1 0+(480374881/1250000000 : ℝ)*X 1 1+(4524674899/10000000000 : ℝ)*X 1 2+(417387483/1000000000 : ℝ)*X 2 0+(480374881/1250000000 : ℝ)*X 2 1+(4524674899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-794168601/5000000000 : ℝ)*X 0 0+(5186397941/10000000000 : ℝ)*X 0 1+(5442936497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638362891/5000000000 : ℝ)*X 1 0+(-292764421/2000000000 : ℝ)*X 1 1+(5442936511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319181431/2500000000 : ℝ)*X 2 0+(1360734171/2500000000 : ℝ)*X 2 1+(-731910971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1043510101/2500000000 : ℝ)*X 0 0+(903898911/2000000000 : ℝ)*X 0 1+(384823359/1000000000 : ℝ)*X 0 2+(1043510101/2500000000 : ℝ)*X 1 0+(903898911/2000000000 : ℝ)*X 1 1+(384823359/1000000000 : ℝ)*X 1 2+(1043510101/2500000000 : ℝ)*X 2 0+(903898911/2000000000 : ℝ)*X 2 1+(384823359/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (668664883908466360690269/125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17215499/5000000000000 : ℝ)*(base19) + (212704141/100000000000000 : ℝ)*(base23) + (15838043/20000000000000 : ℝ)*(lower2) + (984353/20000000000000 : ℝ)*(upper3) + (2153337/12500000000000 : ℝ)*(upper5) + (1326366894817889/50000000000000 : ℝ)*(major0) + (1326366894817889/50000000000000 : ℝ)*(major1) + (1326366894817889/50000000000000 : ℝ)*(major2) + (3838490717111481/100000000000000 : ℝ)*(sp0) + (479811703310583/12500000000000 : ℝ)*(sp1) + (479811719761313/12500000000000 : ℝ)*(sp2) + (366743253244999/25000000000000 : ℝ)*(sp3) + (3253683163/100000000000000 : ℝ)*(sp4) + (208593137/50000000000000 : ℝ)*(sp7) + (146697343016627/10000000000000 : ℝ)*(f.failure) + (959623492698661/25000000000000 : ℝ)*(f.sum) + (169742583383/45000000000000000000000000 : ℝ)*base66 + (23385006500620807/2250000000000000000000000000000 : ℝ)*base67 + (16156175095129193/2250000000000000000000000000000 : ℝ)*base70 + (295438046620807/2250000000000000000000000000000 : ℝ)*base71 + (16595558467/2812500000000000000000000 : ℝ)*base73 + (6448590237379193/2250000000000000000000000000000 : ℝ)*base76 + (25316045535379193/2250000000000000000000000000000 : ℝ)*base78 + (24666587368879193/2250000000000000000000000000000 : ℝ)*base80 + (182993591/22500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (88843/1000000000000000000000 : ℝ)*base90 + (88843/1000000000000000000000 : ℝ)*base92 + (88843/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (535589481322266203351831/62500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1371197049/100000000000000 : ℝ)*(base19) + (1436103491/100000000000000 : ℝ)*(base23) + (3992351/12500000000000 : ℝ)*(upper2) + (215259323/100000000000000 : ℝ)*(upper3) + (47813023/25000000000000 : ℝ)*(upper5) + (673472794901763/25000000000000 : ℝ)*(major0) + (673472794901763/25000000000000 : ℝ)*(major1) + (673472794901763/25000000000000 : ℝ)*(major2) + (4013844261/25000000000000 : ℝ)*(sp1) + (19632143933/100000000000000 : ℝ)*(sp2) + (1949024213040311/50000000000000 : ℝ)*(sp4) + (3898030999506529/100000000000000 : ℝ)*(sp5) + (1949013678916599/50000000000000 : ℝ)*(sp6) + (297946729497151/20000000000000 : ℝ)*(sp7) + (297946729497151/20000000000000 : ℝ)*(f.failure) + (1949024213040311/50000000000000 : ℝ)*(f.sum) + (9443293039/3750000000000000000000000 : ℝ)*base65 + (305736582220223/375000000000000000000000000000 : ℝ)*base67 + (448720985845223/375000000000000000000000000000 : ℝ)*base69 + (702564443095223/375000000000000000000000000000 : ℝ)*base71 + (8090069801/3750000000000000000000000 : ℝ)*base74 + (2074083065470223/375000000000000000000000000000 : ℝ)*base75 + (331081893220223/375000000000000000000000000000 : ℝ)*base77 + (5222362524595223/375000000000000000000000000000 : ℝ)*base79 + (22666482547/7500000000000000000000000 : ℝ)*base82 + (8716041/2000000000000000000000 : ℝ)*base89 + (8716041/2000000000000000000000 : ℝ)*base91 + (8716041/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1659_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10713/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1659_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1659_s4_0 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1588310231/10000000000 : ℝ)*x 0 + (108895017/200000000 : ℝ)*x 1 + (129614507/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1588310231/10000000000 : ℝ)^4955 ≤ (307350690299/3125000000000 : ℝ)^3931 := by
    have hnat : (1588310231 : ℕ)^4955*3125000000000^3931 ≤ 307350690299^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588310231 10000000000 307350690299 3125000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108895017/200000000 : ℝ)^4955 ≤ (9294627551621/20000000000000 : ℝ)^3931 := by
    have hnat : (108895017 : ℕ)^4955*20000000000000^3931 ≤ 9294627551621^3931*200000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108895017 200000000 9294627551621 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129614507/250000000 : ℝ)^4955 ≤ (21845820071393/50000000000000 : ℝ)^3931 := by
    have hnat : (129614507 : ℕ)^4955*50000000000000^3931 ≤ 21845820071393^3931*250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129614507 250000000 21845820071393 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1588310231/10000000000 : ℝ), (108895017/200000000 : ℝ), (129614507/250000000 : ℝ)] ![(307350690299/3125000000000 : ℝ), (9294627551621/20000000000000 : ℝ), (21845820071393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1588310231/10000000000 : ℝ)|^4955 ≤ (307350690299/3125000000000 : ℝ)^3931
        have hw : |(-1588310231/10000000000 : ℝ)|=(1588310231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108895017/200000000 : ℝ)|^4955 ≤ (9294627551621/20000000000000 : ℝ)^3931
        have hw : |(108895017/200000000 : ℝ)|=(108895017/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129614507/250000000 : ℝ)|^4955 ≤ (21845820071393/50000000000000 : ℝ)^3931
        have hw : |(129614507/250000000 : ℝ)|=(129614507/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s4_1 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346344527/10000000000 : ℝ)*x 0 + (-107637021/625000000 : ℝ)*x 1 + (129614507/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346344527/10000000000 : ℝ)^4955 ≤ (22708452715801/50000000000000 : ℝ)^3931 := by
    have hnat : (5346344527 : ℕ)^4955*50000000000000^3931 ≤ 22708452715801^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346344527 10000000000 22708452715801 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107637021/625000000 : ℝ)^4955 ≤ (2178290882847/20000000000000 : ℝ)^3931 := by
    have hnat : (107637021 : ℕ)^4955*20000000000000^3931 ≤ 2178290882847^3931*625000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107637021 625000000 2178290882847 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129614507/250000000 : ℝ)^4955 ≤ (21845820071393/50000000000000 : ℝ)^3931 := by
    have hnat : (129614507 : ℕ)^4955*50000000000000^3931 ≤ 21845820071393^3931*250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129614507 250000000 21845820071393 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346344527/10000000000 : ℝ), (-107637021/625000000 : ℝ), (129614507/250000000 : ℝ)] ![(22708452715801/50000000000000 : ℝ), (2178290882847/20000000000000 : ℝ), (21845820071393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346344527/10000000000 : ℝ)|^4955 ≤ (22708452715801/50000000000000 : ℝ)^3931
        have hw : |(5346344527/10000000000 : ℝ)|=(5346344527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107637021/625000000 : ℝ)|^4955 ≤ (2178290882847/20000000000000 : ℝ)^3931
        have hw : |(-107637021/625000000 : ℝ)|=(107637021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129614507/250000000 : ℝ)|^4955 ≤ (21845820071393/50000000000000 : ℝ)^3931
        have hw : |(129614507/250000000 : ℝ)|=(129614507/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s4_2 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346344527/10000000000 : ℝ)*x 0 + (129614507/250000000 : ℝ)*x 1 + (-107637021/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346344527/10000000000 : ℝ)^4955 ≤ (22708452715801/50000000000000 : ℝ)^3931 := by
    have hnat : (5346344527 : ℕ)^4955*50000000000000^3931 ≤ 22708452715801^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346344527 10000000000 22708452715801 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129614507/250000000 : ℝ)^4955 ≤ (21845820071393/50000000000000 : ℝ)^3931 := by
    have hnat : (129614507 : ℕ)^4955*50000000000000^3931 ≤ 21845820071393^3931*250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129614507 250000000 21845820071393 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107637021/625000000 : ℝ)^4955 ≤ (2178290882847/20000000000000 : ℝ)^3931 := by
    have hnat : (107637021 : ℕ)^4955*20000000000000^3931 ≤ 2178290882847^3931*625000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107637021 625000000 2178290882847 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346344527/10000000000 : ℝ), (129614507/250000000 : ℝ), (-107637021/625000000 : ℝ)] ![(22708452715801/50000000000000 : ℝ), (21845820071393/50000000000000 : ℝ), (2178290882847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346344527/10000000000 : ℝ)|^4955 ≤ (22708452715801/50000000000000 : ℝ)^3931
        have hw : |(5346344527/10000000000 : ℝ)|=(5346344527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129614507/250000000 : ℝ)|^4955 ≤ (21845820071393/50000000000000 : ℝ)^3931
        have hw : |(129614507/250000000 : ℝ)|=(129614507/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-107637021/625000000 : ℝ)|^4955 ≤ (2178290882847/20000000000000 : ℝ)^3931
        have hw : |(-107637021/625000000 : ℝ)|=(107637021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s4_3 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4173899523/10000000000 : ℝ)*x 0 + (3843452139/10000000000 : ℝ)*x 1 + (2262108243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173899523/10000000000 : ℝ)^4955 ≤ (6648530047251/20000000000000 : ℝ)^3931 := by
    have hnat : (4173899523 : ℕ)^4955*20000000000000^3931 ≤ 6648530047251^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173899523 10000000000 6648530047251 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3843452139/10000000000 : ℝ)^4955 ≤ (14980079575959/50000000000000 : ℝ)^3931 := by
    have hnat : (3843452139 : ℕ)^4955*50000000000000^3931 ≤ 14980079575959^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843452139 10000000000 14980079575959 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262108243/5000000000 : ℝ)^4955 ≤ (1149912206359/3125000000000 : ℝ)^3931 := by
    have hnat : (2262108243 : ℕ)^4955*3125000000000^3931 ≤ 1149912206359^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262108243 5000000000 1149912206359 3125000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173899523/10000000000 : ℝ), (3843452139/10000000000 : ℝ), (2262108243/5000000000 : ℝ)] ![(6648530047251/20000000000000 : ℝ), (14980079575959/50000000000000 : ℝ), (1149912206359/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173899523/10000000000 : ℝ)|^4955 ≤ (6648530047251/20000000000000 : ℝ)^3931
        have hw : |(4173899523/10000000000 : ℝ)|=(4173899523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3843452139/10000000000 : ℝ)|^4955 ≤ (14980079575959/50000000000000 : ℝ)^3931
        have hw : |(3843452139/10000000000 : ℝ)|=(3843452139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262108243/5000000000 : ℝ)|^4955 ≤ (1149912206359/3125000000000 : ℝ)^3931
        have hw : |(2262108243/5000000000 : ℝ)|=(2262108243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s4_4 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-397093243/2500000000 : ℝ)*x 0 + (1037310961/2000000000 : ℝ)*x 1 + (5442755639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397093243/2500000000 : ℝ)^4955 ≤ (9835711804249/100000000000000 : ℝ)^3931 := by
    have hnat : (397093243 : ℕ)^4955*100000000000000^3931 ≤ 9835711804249^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397093243 2500000000 9835711804249 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037310961/2000000000 : ℝ)^4955 ≤ (43712615508243/100000000000000 : ℝ)^3931 := by
    have hnat : (1037310961 : ℕ)^4955*100000000000000^3931 ≤ 43712615508243^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037310961 2000000000 43712615508243 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442755639/10000000000 : ℝ)^4955 ≤ (46451672668807/100000000000000 : ℝ)^3931 := by
    have hnat : (5442755639 : ℕ)^4955*100000000000000^3931 ≤ 46451672668807^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442755639 10000000000 46451672668807 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397093243/2500000000 : ℝ), (1037310961/2000000000 : ℝ), (5442755639/10000000000 : ℝ)] ![(9835711804249/100000000000000 : ℝ), (43712615508243/100000000000000 : ℝ), (46451672668807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397093243/2500000000 : ℝ)|^4955 ≤ (9835711804249/100000000000000 : ℝ)^3931
        have hw : |(-397093243/2500000000 : ℝ)|=(397093243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037310961/2000000000 : ℝ)|^4955 ≤ (43712615508243/100000000000000 : ℝ)^3931
        have hw : |(1037310961/2000000000 : ℝ)|=(1037310961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442755639/10000000000 : ℝ)|^4955 ≤ (46451672668807/100000000000000 : ℝ)^3931
        have hw : |(5442755639/10000000000 : ℝ)|=(5442755639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s4_5 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (844283/1600000 : ℝ)*x 0 + (-292803363/2000000000 : ℝ)*x 1 + (5442755587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844283/1600000 : ℝ)^4955 ≤ (8934633425991/20000000000000 : ℝ)^3931 := by
    have hnat : (844283 : ℕ)^4955*20000000000000^3931 ≤ 8934633425991^3931*1600000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844283 1600000 8934633425991 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292803363/2000000000 : ℝ)^4955 ≤ (4437580373687/50000000000000 : ℝ)^3931 := by
    have hnat : (292803363 : ℕ)^4955*50000000000000^3931 ≤ 4437580373687^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292803363 2000000000 4437580373687 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442755587/10000000000 : ℝ)^4955 ≤ (23225836054701/50000000000000 : ℝ)^3931 := by
    have hnat : (5442755587 : ℕ)^4955*50000000000000^3931 ≤ 23225836054701^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442755587 10000000000 23225836054701 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(844283/1600000 : ℝ), (-292803363/2000000000 : ℝ), (5442755587/10000000000 : ℝ)] ![(8934633425991/20000000000000 : ℝ), (4437580373687/50000000000000 : ℝ), (23225836054701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(844283/1600000 : ℝ)|^4955 ≤ (8934633425991/20000000000000 : ℝ)^3931
        have hw : |(844283/1600000 : ℝ)|=(844283/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-292803363/2000000000 : ℝ)|^4955 ≤ (4437580373687/50000000000000 : ℝ)^3931
        have hw : |(-292803363/2000000000 : ℝ)|=(292803363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442755587/10000000000 : ℝ)|^4955 ≤ (23225836054701/50000000000000 : ℝ)^3931
        have hw : |(5442755587/10000000000 : ℝ)|=(5442755587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s4_6 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131919219/250000000 : ℝ)*x 0 + (272137767/500000000 : ℝ)*x 1 + (-1464017149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131919219/250000000 : ℝ)^4955 ≤ (11168291809167/25000000000000 : ℝ)^3931 := by
    have hnat : (131919219 : ℕ)^4955*25000000000000^3931 ≤ 11168291809167^3931*250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131919219 250000000 11168291809167 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272137767/500000000 : ℝ)^4955 ≤ (46451669452227/100000000000000 : ℝ)^3931 := by
    have hnat : (272137767 : ℕ)^4955*100000000000000^3931 ≤ 46451669452227^3931*500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272137767 500000000 46451669452227 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1464017149/10000000000 : ℝ)^4955 ≤ (8875163299589/100000000000000 : ℝ)^3931 := by
    have hnat : (1464017149 : ℕ)^4955*100000000000000^3931 ≤ 8875163299589^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464017149 10000000000 8875163299589 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131919219/250000000 : ℝ), (272137767/500000000 : ℝ), (-1464017149/10000000000 : ℝ)] ![(11168291809167/25000000000000 : ℝ), (46451669452227/100000000000000 : ℝ), (8875163299589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131919219/250000000 : ℝ)|^4955 ≤ (11168291809167/25000000000000 : ℝ)^3931
        have hw : |(131919219/250000000 : ℝ)|=(131919219/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272137767/500000000 : ℝ)|^4955 ≤ (46451669452227/100000000000000 : ℝ)^3931
        have hw : |(272137767/500000000 : ℝ)|=(272137767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1464017149/10000000000 : ℝ)|^4955 ≤ (8875163299589/100000000000000 : ℝ)^3931
        have hw : |(-1464017149/10000000000 : ℝ)|=(1464017149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s4_7 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (834812781/2000000000 : ℝ)*x 0 + (903809949/2000000000 : ℝ)*x 1 + (3848673411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834812781/2000000000 : ℝ)^4955 ≤ (16622150245049/50000000000000 : ℝ)^3931 := by
    have hnat : (834812781 : ℕ)^4955*50000000000000^3931 ≤ 16622150245049^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834812781 2000000000 16622150245049 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903809949/2000000000 : ℝ)^4955 ≤ (36744228653211/100000000000000 : ℝ)^3931 := by
    have hnat : (903809949 : ℕ)^4955*100000000000000^3931 ≤ 36744228653211^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903809949 2000000000 36744228653211 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3848673411/10000000000 : ℝ)^4955 ≤ (30011470849469/100000000000000 : ℝ)^3931 := by
    have hnat : (3848673411 : ℕ)^4955*100000000000000^3931 ≤ 30011470849469^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3848673411 10000000000 30011470849469 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834812781/2000000000 : ℝ), (903809949/2000000000 : ℝ), (3848673411/10000000000 : ℝ)] ![(16622150245049/50000000000000 : ℝ), (36744228653211/100000000000000 : ℝ), (30011470849469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834812781/2000000000 : ℝ)|^4955 ≤ (16622150245049/50000000000000 : ℝ)^3931
        have hw : |(834812781/2000000000 : ℝ)|=(834812781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903809949/2000000000 : ℝ)|^4955 ≤ (36744228653211/100000000000000 : ℝ)^3931
        have hw : |(903809949/2000000000 : ℝ)|=(903809949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3848673411/10000000000 : ℝ)|^4955 ≤ (30011470849469/100000000000000 : ℝ)^3931
        have hw : |(3848673411/10000000000 : ℝ)|=(3848673411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1659_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10713/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2679/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13/80 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10713/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10713/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10713/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10713/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10713/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10713/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10713/100000 : ℝ) ^ (4951/1024 : ℝ) ≤ (510032786759039/25000000000000000000 : ℝ) := by
    have hpowers : (10713/100000 : ℝ)^4951 ≤ (510032786759039/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10713 : ℕ)^4951*25000000000000000000^1024 ≤ 510032786759039^1024*100000^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10713 100000 510032786759039 25000000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10713/100000 : ℝ)) (X := (510032786759039/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8127/50000 : ℝ) ^ (4951/1024 : ℝ) ≤ (95698179065917/625000000000000000 : ℝ) := by
    have hpowers : (8127/50000 : ℝ)^4951 ≤ (95698179065917/625000000000000000 : ℝ)^1024 := by
      have hnat : (8127 : ℕ)^4951*625000000000000000^1024 ≤ 95698179065917^1024*50000^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8127 50000 95698179065917 625000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8127/50000 : ℝ)) (X := (95698179065917/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500510032786759039/12500000000000000000 : ℝ) ≤ (125001054867951/125000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (12500510032786759039/12500000000000000000 : ℝ)^1024 ≤ (125001054867951/125000000000000 : ℝ)^4951 := by
      have hnat : (12500510032786759039 : ℕ)^1024*125000000000000^4951 ≤ 125001054867951^4951*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500510032786759039 12500000000000000000 125001054867951 125000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125001054867951/125000000000000 : ℝ)) (X := (12500510032786759039/12500000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004337959949395719/25000000000000000000 : ℝ) ≤ (10000358858035831/10000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (25004337959949395719/25000000000000000000 : ℝ)^1024 ≤ (10000358858035831/10000000000000000 : ℝ)^4951 := by
      have hnat : (25004337959949395719 : ℕ)^1024*10000000000000000^4951 ≤ 10000358858035831^4951*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004337959949395719 25000000000000000000 10000358858035831 10000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000358858035831/10000000000000000 : ℝ)) (X := (25004337959949395719/25000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312595698179065917/312500000000000000 : ℝ) ≤ (5000316663317791/5000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (312595698179065917/312500000000000000 : ℝ)^1024 ≤ (5000316663317791/5000000000000000 : ℝ)^4951 := by
      have hnat : (312595698179065917 : ℕ)^1024*5000000000000000^4951 ≤ 5000316663317791^4951*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312595698179065917 312500000000000000 5000316663317791 5000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000316663317791/5000000000000000 : ℝ)) (X := (312595698179065917/312500000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(510032786759039/25000000000000000000 : ℝ) ≤ ((9234097806274509059/9235000000000000000 : ℝ)+2*(274468599751/554100000000000 : ℝ)*(10713/100000 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (9234097806274509059/9235000000000000000 : ℝ)+2*(274468599751/554100000000000 : ℝ)*(10713/100000 : ℝ)=(125001054867951/125000000000000 : ℝ) by norm_num, show 1+2*(510032786759039/25000000000000000000 : ℝ)=(12500510032786759039/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(95698179065917/625000000000000000 : ℝ)+(510032786759039/25000000000000000000 : ℝ) ≤ ((9234097806274509059/9235000000000000000 : ℝ)+(274468599751/554100000000000 : ℝ)*((8127/50000 : ℝ)+(10713/100000 : ℝ)))^(4951/1024 : ℝ) := by
    rw [show (9234097806274509059/9235000000000000000 : ℝ)+(274468599751/554100000000000 : ℝ)*((8127/50000 : ℝ)+(10713/100000 : ℝ))=(10000358858035831/10000000000000000 : ℝ) by norm_num, show 1+(95698179065917/625000000000000000 : ℝ)+(510032786759039/25000000000000000000 : ℝ)=(25004337959949395719/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(95698179065917/625000000000000000 : ℝ) ≤ ((9234097806274509059/9235000000000000000 : ℝ)+2*(274468599751/554100000000000 : ℝ)*(8127/50000 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (9234097806274509059/9235000000000000000 : ℝ)+2*(274468599751/554100000000000 : ℝ)*(8127/50000 : ℝ)=(5000316663317791/5000000000000000 : ℝ) by norm_num, show 1+2*(95698179065917/625000000000000000 : ℝ)=(312595698179065917/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9234097806274509059/9235000000000000000 : ℝ)*(X 1 0+X 2 0)+(274468599751/554100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (10713/100000 : ℝ)) (hi := (8127/50000 : ℝ)) (c := (9234097806274509059/9235000000000000000 : ℝ)) (alpha := (274468599751/554100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9234097806274509059/9235000000000000000 : ℝ)*(X 0 1+X 2 1)+(274468599751/554100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (10713/100000 : ℝ)) (hi := (8127/50000 : ℝ)) (c := (9234097806274509059/9235000000000000000 : ℝ)) (alpha := (274468599751/554100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9234097806274509059/9235000000000000000 : ℝ)*(X 0 2+X 1 2)+(274468599751/554100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (10713/100000 : ℝ)) (hi := (8127/50000 : ℝ)) (c := (9234097806274509059/9235000000000000000 : ℝ)) (alpha := (274468599751/554100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1588310231/10000000000 : ℝ)*X 0 0+(108895017/200000000 : ℝ)*X 0 1+(129614507/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346344527/10000000000 : ℝ)*X 1 0+(-107637021/625000000 : ℝ)*X 1 1+(129614507/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346344527/10000000000 : ℝ)*X 2 0+(129614507/250000000 : ℝ)*X 2 1+(-107637021/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4173899523/10000000000 : ℝ)*X 0 0+(3843452139/10000000000 : ℝ)*X 0 1+(2262108243/5000000000 : ℝ)*X 0 2+(4173899523/10000000000 : ℝ)*X 1 0+(3843452139/10000000000 : ℝ)*X 1 1+(2262108243/5000000000 : ℝ)*X 1 2+(4173899523/10000000000 : ℝ)*X 2 0+(3843452139/10000000000 : ℝ)*X 2 1+(2262108243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-397093243/2500000000 : ℝ)*X 0 0+(1037310961/2000000000 : ℝ)*X 0 1+(5442755639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((844283/1600000 : ℝ)*X 1 0+(-292803363/2000000000 : ℝ)*X 1 1+(5442755587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((131919219/250000000 : ℝ)*X 2 0+(272137767/500000000 : ℝ)*X 2 1+(-1464017149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((834812781/2000000000 : ℝ)*X 0 0+(903809949/2000000000 : ℝ)*X 0 1+(3848673411/10000000000 : ℝ)*X 0 2+(834812781/2000000000 : ℝ)*X 1 0+(903809949/2000000000 : ℝ)*X 1 1+(3848673411/10000000000 : ℝ)*X 1 2+(834812781/2000000000 : ℝ)*X 2 0+(903809949/2000000000 : ℝ)*X 2 1+(3848673411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44445781262146417832819683/4617500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1510005647/100000000000000 : ℝ)*(base19) + (353616067/25000000000000 : ℝ)*(base23) + (51079713/100000000000000 : ℝ)*(lower2) + (117267883/50000000000000 : ℝ)*(upper3) + (83242929/50000000000000 : ℝ)*(upper5) + (53126233206179/2000000000000 : ℝ)*(major0) + (53126233206179/2000000000000 : ℝ)*(major1) + (2656311660308951/100000000000000 : ℝ)*(major2) + (24022824447123/625000000000 : ℝ)*(sp0) + (1921834740703981/50000000000000 : ℝ)*(sp1) + (192183478847467/5000000000000 : ℝ)*(sp2) + (183618013850611/12500000000000 : ℝ)*(sp3) + (2384984241/12500000000000 : ℝ)*(sp4) + (1579509829/20000000000000 : ℝ)*(sp7) + (1468952008354033/100000000000000 : ℝ)*(f.failure) + (480458873926701/12500000000000 : ℝ)*(f.sum) + (40771140370307/18470000000000000000000000000 : ℝ)*base65 + (484068503866742317/55410000000000000000000000000000 : ℝ)*base68 + (29568482328809861327/2770500000000000000000000000000000 : ℝ)*base69 + (567514751828402317/55410000000000000000000000000000 : ℝ)*base72 + (48225717421533/18470000000000000000000000000 : ℝ)*base74 + (9283898612034138673/2770500000000000000000000000000000 : ℝ)*base76 + (200550480422613317/55410000000000000000000000000000 : ℝ)*base78 + (105984828162093317/55410000000000000000000000000000 : ℝ)*base80 + (25115703171947/5541000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (53816903/10000000000000000000000 : ℝ)*base89 + (53816903/10000000000000000000000 : ℝ)*base91 + (46183097/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3489666956473080307024183497/461750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1178348119/100000000000000 : ℝ)*(base19) + (1252181237/100000000000000 : ℝ)*(base23) + (6207239/2000000000000 : ℝ)*(lower1) + (34707081/50000000000000 : ℝ)*(upper3) + (71958019/100000000000000 : ℝ)*(lower4) + (84758673/50000000000000 : ℝ)*(upper5) + (2697435321001387/100000000000000 : ℝ)*(major0) + (2697435321001387/100000000000000 : ℝ)*(major1) + (2697435321001387/100000000000000 : ℝ)*(major2) + (2651868759/50000000000000 : ℝ)*(sp1) + (3903176816852467/100000000000000 : ℝ)*(sp4) + (390317033476683/10000000000000 : ℝ)*(sp5) + (390317556467123/10000000000000 : ℝ)*(sp6) + (745846786617131/50000000000000 : ℝ)*(sp7) + (745846786617131/50000000000000 : ℝ)*(f.failure) + (3903176816852467/100000000000000 : ℝ)*(f.sum) + (34617722953493/27705000000000000000000000000 : ℝ)*base66 + (27542334625031455501/2770500000000000000000000000000000 : ℝ)*base68 + (7314088432916455501/2770500000000000000000000000000000 : ℝ)*base70 + (10770898080936955501/2770500000000000000000000000000000 : ℝ)*base72 + (95781040387223/27705000000000000000000000000 : ℝ)*base74 + (22408916197824955501/2770500000000000000000000000000000 : ℝ)*base76 + (2598888084873955501/2770500000000000000000000000000000 : ℝ)*base78 + (12947103096213955501/2770500000000000000000000000000000 : ℝ)*base80 + (82754972779823/27705000000000000000000000000 : ℝ)*base82 + (16028221/5000000000000000000000 : ℝ)*base89 + (16028221/5000000000000000000000 : ℝ)*base91 + (16028221/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1659_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10713/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2679/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13/80 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1659_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1659_box_0 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1333513427/10000000000 : ℝ)*x 0 + (1081171911/2000000000 : ℝ)*x 1 + (1351465201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333513427/10000000000 : ℝ)^4955 ≤ (788977993429/10000000000000 : ℝ)^3931 := by
    have hnat : (1333513427 : ℕ)^4955*10000000000000^3931 ≤ 788977993429^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333513427 10000000000 788977993429 10000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081171911/2000000000 : ℝ)^4955 ≤ (23027551660123/50000000000000 : ℝ)^3931 := by
    have hnat : (1081171911 : ℕ)^4955*50000000000000^3931 ≤ 23027551660123^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081171911 2000000000 23027551660123 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351465201/2500000000 : ℝ)^4955 ≤ (23027558366471/50000000000000 : ℝ)^3931 := by
    have hnat : (1351465201 : ℕ)^4955*50000000000000^3931 ≤ 23027558366471^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351465201 2500000000 23027558366471 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1333513427/10000000000 : ℝ), (1081171911/2000000000 : ℝ), (1351465201/2500000000 : ℝ)] ![(788977993429/10000000000000 : ℝ), (23027551660123/50000000000000 : ℝ), (23027558366471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1333513427/10000000000 : ℝ)|^4955 ≤ (788977993429/10000000000000 : ℝ)^3931
        have hw : |(-1333513427/10000000000 : ℝ)|=(1333513427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081171911/2000000000 : ℝ)|^4955 ≤ (23027551660123/50000000000000 : ℝ)^3931
        have hw : |(1081171911/2000000000 : ℝ)|=(1081171911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351465201/2500000000 : ℝ)|^4955 ≤ (23027558366471/50000000000000 : ℝ)^3931
        have hw : |(1351465201/2500000000 : ℝ)|=(1351465201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_1 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625465443/5000000000 : ℝ)*x 0 + (-775652939/5000000000 : ℝ)*x 1 + (5405859991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625465443/5000000000 : ℝ)^4955 ≤ (8879523668281/20000000000000 : ℝ)^3931 := by
    have hnat : (2625465443 : ℕ)^4955*20000000000000^3931 ≤ 8879523668281^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625465443 5000000000 8879523668281 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775652939/5000000000 : ℝ)^4955 ≤ (9547273645133/100000000000000 : ℝ)^3931 := by
    have hnat : (775652939 : ℕ)^4955*100000000000000^3931 ≤ 9547273645133^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775652939 5000000000 9547273645133 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405859991/10000000000 : ℝ)^4955 ≤ (2302755400117/5000000000000 : ℝ)^3931 := by
    have hnat : (5405859991 : ℕ)^4955*5000000000000^3931 ≤ 2302755400117^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405859991 10000000000 2302755400117 5000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625465443/5000000000 : ℝ), (-775652939/5000000000 : ℝ), (5405859991/10000000000 : ℝ)] ![(8879523668281/20000000000000 : ℝ), (9547273645133/100000000000000 : ℝ), (2302755400117/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625465443/5000000000 : ℝ)|^4955 ≤ (8879523668281/20000000000000 : ℝ)^3931
        have hw : |(2625465443/5000000000 : ℝ)|=(2625465443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-775652939/5000000000 : ℝ)|^4955 ≤ (9547273645133/100000000000000 : ℝ)^3931
        have hw : |(-775652939/5000000000 : ℝ)|=(775652939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405859991/10000000000 : ℝ)|^4955 ≤ (2302755400117/5000000000000 : ℝ)^3931
        have hw : |(5405859991/10000000000 : ℝ)|=(5405859991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_2 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625465353/5000000000 : ℝ)*x 0 + (5405860473/10000000000 : ℝ)*x 1 + (-775652729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625465353/5000000000 : ℝ)^4955 ≤ (44397616423017/100000000000000 : ℝ)^3931 := by
    have hnat : (2625465353 : ℕ)^4955*100000000000000^3931 ≤ 44397616423017^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625465353 5000000000 44397616423017 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405860473/10000000000 : ℝ)^4955 ≤ (2878444573651/6250000000000 : ℝ)^3931 := by
    have hnat : (5405860473 : ℕ)^4955*6250000000000^3931 ≤ 2878444573651^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405860473 10000000000 2878444573651 6250000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (775652729/5000000000 : ℝ)^4955 ≤ (9547270386977/100000000000000 : ℝ)^3931 := by
    have hnat : (775652729 : ℕ)^4955*100000000000000^3931 ≤ 9547270386977^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775652729 5000000000 9547270386977 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625465353/5000000000 : ℝ), (5405860473/10000000000 : ℝ), (-775652729/5000000000 : ℝ)] ![(44397616423017/100000000000000 : ℝ), (2878444573651/6250000000000 : ℝ), (9547270386977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625465353/5000000000 : ℝ)|^4955 ≤ (44397616423017/100000000000000 : ℝ)^3931
        have hw : |(2625465353/5000000000 : ℝ)|=(2625465353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405860473/10000000000 : ℝ)|^4955 ≤ (2878444573651/6250000000000 : ℝ)^3931
        have hw : |(5405860473/10000000000 : ℝ)|=(5405860473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-775652729/5000000000 : ℝ)|^4955 ≤ (9547270386977/100000000000000 : ℝ)^3931
        have hw : |(-775652729/5000000000 : ℝ)|=(775652729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_3 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4450120313/10000000000 : ℝ)*x 0 + (4047665861/10000000000 : ℝ)*x 1 + (2023833133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4450120313/10000000000 : ℝ)^4955 ≤ (18019588934529/50000000000000 : ℝ)^3931 := by
    have hnat : (4450120313 : ℕ)^4955*50000000000000^3931 ≤ 18019588934529^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450120313 10000000000 18019588934529 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4047665861/10000000000 : ℝ)^4955 ≤ (31980409039259/100000000000000 : ℝ)^3931 := by
    have hnat : (4047665861 : ℕ)^4955*100000000000000^3931 ≤ 31980409039259^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4047665861 10000000000 31980409039259 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023833133/5000000000 : ℝ)^4955 ≤ (15990206536347/50000000000000 : ℝ)^3931 := by
    have hnat : (2023833133 : ℕ)^4955*50000000000000^3931 ≤ 15990206536347^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023833133 5000000000 15990206536347 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4450120313/10000000000 : ℝ), (4047665861/10000000000 : ℝ), (2023833133/5000000000 : ℝ)] ![(18019588934529/50000000000000 : ℝ), (31980409039259/100000000000000 : ℝ), (15990206536347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4450120313/10000000000 : ℝ)|^4955 ≤ (18019588934529/50000000000000 : ℝ)^3931
        have hw : |(4450120313/10000000000 : ℝ)|=(4450120313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4047665861/10000000000 : ℝ)|^4955 ≤ (31980409039259/100000000000000 : ℝ)^3931
        have hw : |(4047665861/10000000000 : ℝ)|=(4047665861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2023833133/5000000000 : ℝ)|^4955 ≤ (15990206536347/50000000000000 : ℝ)^3931
        have hw : |(2023833133/5000000000 : ℝ)|=(2023833133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_4 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-463419021/2500000000 : ℝ)*x 0 + (5215946753/10000000000 : ℝ)*x 1 + (208637853/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463419021/2500000000 : ℝ)^4955 ≤ (11949821332767/100000000000000 : ℝ)^3931 := by
    have hnat : (463419021 : ℕ)^4955*100000000000000^3931 ≤ 11949821332767^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463419021 2500000000 11949821332767 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215946753/10000000000 : ℝ)^4955 ≤ (8805018320297/20000000000000 : ℝ)^3931 := by
    have hnat : (5215946753 : ℕ)^4955*20000000000000^3931 ≤ 8805018320297^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215946753 10000000000 8805018320297 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208637853/400000000 : ℝ)^4955 ≤ (550313588099/1250000000000 : ℝ)^3931 := by
    have hnat : (208637853 : ℕ)^4955*1250000000000^3931 ≤ 550313588099^3931*400000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208637853 400000000 550313588099 1250000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-463419021/2500000000 : ℝ), (5215946753/10000000000 : ℝ), (208637853/400000000 : ℝ)] ![(11949821332767/100000000000000 : ℝ), (8805018320297/20000000000000 : ℝ), (550313588099/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-463419021/2500000000 : ℝ)|^4955 ≤ (11949821332767/100000000000000 : ℝ)^3931
        have hw : |(-463419021/2500000000 : ℝ)|=(463419021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215946753/10000000000 : ℝ)|^4955 ≤ (8805018320297/20000000000000 : ℝ)^3931
        have hw : |(5215946753/10000000000 : ℝ)|=(5215946753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208637853/400000000 : ℝ)|^4955 ≤ (550313588099/1250000000000 : ℝ)^3931
        have hw : |(208637853/400000000 : ℝ)|=(208637853/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_5 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16816021/31250000 : ℝ)*x 0 + (-326598419/2000000000 : ℝ)*x 1 + (2607973369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16816021/31250000 : ℝ)^4955 ≤ (4578966210913/10000000000000 : ℝ)^3931 := by
    have hnat : (16816021 : ℕ)^4955*10000000000000^3931 ≤ 4578966210913^3931*31250000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16816021 31250000 4578966210913 10000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326598419/2000000000 : ℝ)^4955 ≤ (10185246430797/100000000000000 : ℝ)^3931 := by
    have hnat : (326598419 : ℕ)^4955*100000000000000^3931 ≤ 10185246430797^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326598419 2000000000 10185246430797 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607973369/5000000000 : ℝ)^4955 ≤ (44025091441897/100000000000000 : ℝ)^3931 := by
    have hnat : (2607973369 : ℕ)^4955*100000000000000^3931 ≤ 44025091441897^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607973369 5000000000 44025091441897 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16816021/31250000 : ℝ), (-326598419/2000000000 : ℝ), (2607973369/5000000000 : ℝ)] ![(4578966210913/10000000000000 : ℝ), (10185246430797/100000000000000 : ℝ), (44025091441897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16816021/31250000 : ℝ)|^4955 ≤ (4578966210913/10000000000000 : ℝ)^3931
        have hw : |(16816021/31250000 : ℝ)|=(16816021/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-326598419/2000000000 : ℝ)|^4955 ≤ (10185246430797/100000000000000 : ℝ)^3931
        have hw : |(-326598419/2000000000 : ℝ)|=(326598419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607973369/5000000000 : ℝ)|^4955 ≤ (44025091441897/100000000000000 : ℝ)^3931
        have hw : |(2607973369/5000000000 : ℝ)|=(2607973369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_6 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538112713/1000000000 : ℝ)*x 0 + (651993289/1250000000 : ℝ)*x 1 + (-102062007/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538112713/1000000000 : ℝ)^4955 ≤ (1144741662669/2500000000000 : ℝ)^3931 := by
    have hnat : (538112713 : ℕ)^4955*2500000000000^3931 ≤ 1144741662669^3931*1000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538112713 1000000000 1144741662669 2500000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651993289/1250000000 : ℝ)^4955 ≤ (44025086909611/100000000000000 : ℝ)^3931 := by
    have hnat : (651993289 : ℕ)^4955*100000000000000^3931 ≤ 44025086909611^3931*1250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651993289 1250000000 44025086909611 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102062007/625000000 : ℝ)^4955 ≤ (10185246564449/100000000000000 : ℝ)^3931 := by
    have hnat : (102062007 : ℕ)^4955*100000000000000^3931 ≤ 10185246564449^3931*625000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102062007 625000000 10185246564449 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538112713/1000000000 : ℝ), (651993289/1250000000 : ℝ), (-102062007/625000000 : ℝ)] ![(1144741662669/2500000000000 : ℝ), (44025086909611/100000000000000 : ℝ), (10185246564449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538112713/1000000000 : ℝ)|^4955 ≤ (1144741662669/2500000000000 : ℝ)^3931
        have hw : |(538112713/1000000000 : ℝ)|=(538112713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651993289/1250000000 : ℝ)|^4955 ≤ (44025086909611/100000000000000 : ℝ)^3931
        have hw : |(651993289/1250000000 : ℝ)|=(651993289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102062007/625000000 : ℝ)|^4955 ≤ (10185246564449/100000000000000 : ℝ)^3931
        have hw : |(-102062007/625000000 : ℝ)|=(102062007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_7 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1945514173/5000000000 : ℝ)*x 0 + (540861349/1250000000 : ℝ)*x 1 + (4326890739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1945514173/5000000000 : ℝ)^4955 ≤ (30428379818771/100000000000000 : ℝ)^3931 := by
    have hnat : (1945514173 : ℕ)^4955*100000000000000^3931 ≤ 30428379818771^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945514173 5000000000 30428379818771 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540861349/1250000000 : ℝ)^4955 ≤ (34785810352899/100000000000000 : ℝ)^3931 := by
    have hnat : (540861349 : ℕ)^4955*100000000000000^3931 ≤ 34785810352899^3931*1250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540861349 1250000000 34785810352899 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4326890739/10000000000 : ℝ)^4955 ≤ (17392904907907/50000000000000 : ℝ)^3931 := by
    have hnat : (4326890739 : ℕ)^4955*50000000000000^3931 ≤ 17392904907907^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326890739 10000000000 17392904907907 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1945514173/5000000000 : ℝ), (540861349/1250000000 : ℝ), (4326890739/10000000000 : ℝ)] ![(30428379818771/100000000000000 : ℝ), (34785810352899/100000000000000 : ℝ), (17392904907907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1945514173/5000000000 : ℝ)|^4955 ≤ (30428379818771/100000000000000 : ℝ)^3931
        have hw : |(1945514173/5000000000 : ℝ)|=(1945514173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540861349/1250000000 : ℝ)|^4955 ≤ (34785810352899/100000000000000 : ℝ)^3931
        have hw : |(540861349/1250000000 : ℝ)|=(540861349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4326890739/10000000000 : ℝ)|^4955 ≤ (17392904907907/50000000000000 : ℝ)^3931
        have hw : |(4326890739/10000000000 : ℝ)|=(4326890739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_8 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1742651341/10000000000 : ℝ)*x 0 + (5079155079/10000000000 : ℝ)*x 1 + (5435204867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742651341/10000000000 : ℝ)^4955 ≤ (11054796783933/100000000000000 : ℝ)^3931 := by
    have hnat : (1742651341 : ℕ)^4955*100000000000000^3931 ≤ 11054796783933^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742651341 10000000000 11054796783933 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079155079/10000000000 : ℝ)^4955 ≤ (42574745479877/100000000000000 : ℝ)^3931 := by
    have hnat : (5079155079 : ℕ)^4955*100000000000000^3931 ≤ 42574745479877^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079155079 10000000000 42574745479877 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435204867/10000000000 : ℝ)^4955 ≤ (46370457718163/100000000000000 : ℝ)^3931 := by
    have hnat : (5435204867 : ℕ)^4955*100000000000000^3931 ≤ 46370457718163^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435204867 10000000000 46370457718163 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1742651341/10000000000 : ℝ), (5079155079/10000000000 : ℝ), (5435204867/10000000000 : ℝ)] ![(11054796783933/100000000000000 : ℝ), (42574745479877/100000000000000 : ℝ), (46370457718163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1742651341/10000000000 : ℝ)|^4955 ≤ (11054796783933/100000000000000 : ℝ)^3931
        have hw : |(-1742651341/10000000000 : ℝ)|=(1742651341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079155079/10000000000 : ℝ)|^4955 ≤ (42574745479877/100000000000000 : ℝ)^3931
        have hw : |(5079155079/10000000000 : ℝ)|=(5079155079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435204867/10000000000 : ℝ)|^4955 ≤ (46370457718163/100000000000000 : ℝ)^3931
        have hw : |(5435204867/10000000000 : ℝ)|=(5435204867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_9 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307703947/2500000000 : ℝ)*x 0 + (-307652463/2000000000 : ℝ)*x 1 + (1358801187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307703947/2500000000 : ℝ)^4955 ≤ (22091672241243/50000000000000 : ℝ)^3931 := by
    have hnat : (1307703947 : ℕ)^4955*50000000000000^3931 ≤ 22091672241243^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307703947 2500000000 22091672241243 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307652463/2000000000 : ℝ)^4955 ≤ (2361549767317/25000000000000 : ℝ)^3931 := by
    have hnat : (307652463 : ℕ)^4955*25000000000000^3931 ≤ 2361549767317^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307652463 2000000000 2361549767317 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358801187/2500000000 : ℝ)^4955 ≤ (2898153527403/6250000000000 : ℝ)^3931 := by
    have hnat : (1358801187 : ℕ)^4955*6250000000000^3931 ≤ 2898153527403^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358801187 2500000000 2898153527403 6250000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307703947/2500000000 : ℝ), (-307652463/2000000000 : ℝ), (1358801187/2500000000 : ℝ)] ![(22091672241243/50000000000000 : ℝ), (2361549767317/25000000000000 : ℝ), (2898153527403/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307703947/2500000000 : ℝ)|^4955 ≤ (22091672241243/50000000000000 : ℝ)^3931
        have hw : |(1307703947/2500000000 : ℝ)|=(1307703947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-307652463/2000000000 : ℝ)|^4955 ≤ (2361549767317/25000000000000 : ℝ)^3931
        have hw : |(-307652463/2000000000 : ℝ)|=(307652463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358801187/2500000000 : ℝ)|^4955 ≤ (2898153527403/6250000000000 : ℝ)^3931
        have hw : |(1358801187/2500000000 : ℝ)|=(1358801187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_10 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307703913/2500000000 : ℝ)*x 0 + (2717602421/5000000000 : ℝ)*x 1 + (-1538262371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307703913/2500000000 : ℝ)^4955 ≤ (22091671517243/50000000000000 : ℝ)^3931 := by
    have hnat : (1307703913 : ℕ)^4955*50000000000000^3931 ≤ 22091671517243^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307703913 2500000000 22091671517243 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717602421/5000000000 : ℝ)^4955 ≤ (9274091489863/20000000000000 : ℝ)^3931 := by
    have hnat : (2717602421 : ℕ)^4955*20000000000000^3931 ≤ 9274091489863^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717602421 5000000000 9274091489863 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1538262371/10000000000 : ℝ)^4955 ≤ (4723099751367/50000000000000 : ℝ)^3931 := by
    have hnat : (1538262371 : ℕ)^4955*50000000000000^3931 ≤ 4723099751367^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1538262371 10000000000 4723099751367 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307703913/2500000000 : ℝ), (2717602421/5000000000 : ℝ), (-1538262371/10000000000 : ℝ)] ![(22091671517243/50000000000000 : ℝ), (9274091489863/20000000000000 : ℝ), (4723099751367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307703913/2500000000 : ℝ)|^4955 ≤ (22091671517243/50000000000000 : ℝ)^3931
        have hw : |(1307703913/2500000000 : ℝ)|=(1307703913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717602421/5000000000 : ℝ)|^4955 ≤ (9274091489863/20000000000000 : ℝ)^3931
        have hw : |(2717602421/5000000000 : ℝ)|=(2717602421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1538262371/10000000000 : ℝ)|^4955 ≤ (4723099751367/50000000000000 : ℝ)^3931
        have hw : |(-1538262371/10000000000 : ℝ)|=(1538262371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_11 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (453413443/1000000000 : ℝ)*x 0 + (1001110777/2500000000 : ℝ)*x 1 + (250277703/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453413443/1000000000 : ℝ)^4955 ≤ (115309059859/312500000000 : ℝ)^3931 := by
    have hnat : (453413443 : ℕ)^4955*312500000000^3931 ≤ 115309059859^3931*1000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453413443 1000000000 115309059859 312500000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001110777/2500000000 : ℝ)^4955 ≤ (7887637429233/25000000000000 : ℝ)^3931 := by
    have hnat : (1001110777 : ℕ)^4955*25000000000000^3931 ≤ 7887637429233^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001110777 2500000000 7887637429233 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250277703/625000000 : ℝ)^4955 ≤ (1971909444207/6250000000000 : ℝ)^3931 := by
    have hnat : (250277703 : ℕ)^4955*6250000000000^3931 ≤ 1971909444207^3931*625000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250277703 625000000 1971909444207 6250000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(453413443/1000000000 : ℝ), (1001110777/2500000000 : ℝ), (250277703/625000000 : ℝ)] ![(115309059859/312500000000 : ℝ), (7887637429233/25000000000000 : ℝ), (1971909444207/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(453413443/1000000000 : ℝ)|^4955 ≤ (115309059859/312500000000 : ℝ)^3931
        have hw : |(453413443/1000000000 : ℝ)|=(453413443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001110777/2500000000 : ℝ)|^4955 ≤ (7887637429233/25000000000000 : ℝ)^3931
        have hw : |(1001110777/2500000000 : ℝ)|=(1001110777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(250277703/625000000 : ℝ)|^4955 ≤ (1971909444207/6250000000000 : ℝ)^3931
        have hw : |(250277703/625000000 : ℝ)|=(250277703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_12 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1442666673/10000000000 : ℝ)*x 0 + (692186381/1250000000 : ℝ)*x 1 + (5196148167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1442666673/10000000000 : ℝ)^4955 ≤ (4356163791531/50000000000000 : ℝ)^3931 := by
    have hnat : (1442666673 : ℕ)^4955*50000000000000^3931 ≤ 4356163791531^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442666673 10000000000 4356163791531 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692186381/1250000000 : ℝ)^4955 ≤ (23736558542007/50000000000000 : ℝ)^3931 := by
    have hnat : (692186381 : ℕ)^4955*50000000000000^3931 ≤ 23736558542007^3931*1250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692186381 1250000000 23736558542007 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196148167/10000000000 : ℝ)^4955 ≤ (43814555321999/100000000000000 : ℝ)^3931 := by
    have hnat : (5196148167 : ℕ)^4955*100000000000000^3931 ≤ 43814555321999^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196148167 10000000000 43814555321999 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1442666673/10000000000 : ℝ), (692186381/1250000000 : ℝ), (5196148167/10000000000 : ℝ)] ![(4356163791531/50000000000000 : ℝ), (23736558542007/50000000000000 : ℝ), (43814555321999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1442666673/10000000000 : ℝ)|^4955 ≤ (4356163791531/50000000000000 : ℝ)^3931
        have hw : |(-1442666673/10000000000 : ℝ)|=(1442666673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692186381/1250000000 : ℝ)|^4955 ≤ (23736558542007/50000000000000 : ℝ)^3931
        have hw : |(692186381/1250000000 : ℝ)|=(692186381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196148167/10000000000 : ℝ)|^4955 ≤ (43814555321999/100000000000000 : ℝ)^3931
        have hw : |(5196148167/10000000000 : ℝ)|=(5196148167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_13 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394709013/10000000000 : ℝ)*x 0 + (-6411047/39062500 : ℝ)*x 1 + (259807469/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394709013/10000000000 : ℝ)^4955 ≤ (2296769632753/5000000000000 : ℝ)^3931 := by
    have hnat : (5394709013 : ℕ)^4955*5000000000000^3931 ≤ 2296769632753^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394709013 10000000000 2296769632753 5000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6411047/39062500 : ℝ)^4955 ≤ (10250039108439/100000000000000 : ℝ)^3931 := by
    have hnat : (6411047 : ℕ)^4955*100000000000000^3931 ≤ 10250039108439^3931*39062500^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6411047 39062500 10250039108439 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259807469/500000000 : ℝ)^4955 ≤ (21907284107267/50000000000000 : ℝ)^3931 := by
    have hnat : (259807469 : ℕ)^4955*50000000000000^3931 ≤ 21907284107267^3931*500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259807469 500000000 21907284107267 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394709013/10000000000 : ℝ), (-6411047/39062500 : ℝ), (259807469/500000000 : ℝ)] ![(2296769632753/5000000000000 : ℝ), (10250039108439/100000000000000 : ℝ), (21907284107267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394709013/10000000000 : ℝ)|^4955 ≤ (2296769632753/5000000000000 : ℝ)^3931
        have hw : |(5394709013/10000000000 : ℝ)|=(5394709013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6411047/39062500 : ℝ)|^4955 ≤ (10250039108439/100000000000000 : ℝ)^3931
        have hw : |(-6411047/39062500 : ℝ)|=(6411047/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259807469/500000000 : ℝ)|^4955 ≤ (21907284107267/50000000000000 : ℝ)^3931
        have hw : |(259807469/500000000 : ℝ)|=(259807469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_14 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134867747/250000000 : ℝ)*x 0 + (5196148647/10000000000 : ℝ)*x 1 + (-1641227841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134867747/250000000 : ℝ)^4955 ≤ (11483850490137/25000000000000 : ℝ)^3931 := by
    have hnat : (134867747 : ℕ)^4955*25000000000000^3931 ≤ 11483850490137^3931*250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134867747 250000000 11483850490137 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196148647/10000000000 : ℝ)^4955 ≤ (684602506621/1562500000000 : ℝ)^3931 := by
    have hnat : (5196148647 : ℕ)^4955*1562500000000^3931 ≤ 684602506621^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196148647 10000000000 684602506621 1562500000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1641227841/10000000000 : ℝ)^4955 ≤ (2050007520969/20000000000000 : ℝ)^3931 := by
    have hnat : (1641227841 : ℕ)^4955*20000000000000^3931 ≤ 2050007520969^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641227841 10000000000 2050007520969 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134867747/250000000 : ℝ), (5196148647/10000000000 : ℝ), (-1641227841/10000000000 : ℝ)] ![(11483850490137/25000000000000 : ℝ), (684602506621/1562500000000 : ℝ), (2050007520969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134867747/250000000 : ℝ)|^4955 ≤ (11483850490137/25000000000000 : ℝ)^3931
        have hw : |(134867747/250000000 : ℝ)|=(134867747/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196148647/10000000000 : ℝ)|^4955 ≤ (684602506621/1562500000000 : ℝ)^3931
        have hw : |(5196148647/10000000000 : ℝ)|=(5196148647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1641227841/10000000000 : ℝ)|^4955 ≤ (2050007520969/20000000000000 : ℝ)^3931
        have hw : |(-1641227841/10000000000 : ℝ)|=(1641227841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_box_15 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3831115971/10000000000 : ℝ)*x 0 + (435594633/1000000000 : ℝ)*x 1 + (4355945159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3831115971/10000000000 : ℝ)^4955 ≤ (29838998447037/100000000000000 : ℝ)^3931 := by
    have hnat : (3831115971 : ℕ)^4955*100000000000000^3931 ≤ 29838998447037^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3831115971 10000000000 29838998447037 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435594633/1000000000 : ℝ)^4955 ≤ (8770126679301/25000000000000 : ℝ)^3931 := by
    have hnat : (435594633 : ℕ)^4955*25000000000000^3931 ≤ 8770126679301^3931*1000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435594633 1000000000 8770126679301 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4355945159/10000000000 : ℝ)^4955 ≤ (3508049482997/10000000000000 : ℝ)^3931 := by
    have hnat : (4355945159 : ℕ)^4955*10000000000000^3931 ≤ 3508049482997^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355945159 10000000000 3508049482997 10000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3831115971/10000000000 : ℝ), (435594633/1000000000 : ℝ), (4355945159/10000000000 : ℝ)] ![(29838998447037/100000000000000 : ℝ), (8770126679301/25000000000000 : ℝ), (3508049482997/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3831115971/10000000000 : ℝ)|^4955 ≤ (29838998447037/100000000000000 : ℝ)^3931
        have hw : |(3831115971/10000000000 : ℝ)|=(3831115971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(435594633/1000000000 : ℝ)|^4955 ≤ (8770126679301/25000000000000 : ℝ)^3931
        have hw : |(435594633/1000000000 : ℝ)|=(435594633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4355945159/10000000000 : ℝ)|^4955 ≤ (3508049482997/10000000000000 : ℝ)^3931
        have hw : |(4355945159/10000000000 : ℝ)|=(4355945159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1659_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13/80 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2679/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(32553/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58723/100000 : ℝ) ∧ (81359/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8831/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13/80 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2679/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13/80 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2679/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13/80 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2679/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13/80 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2679/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13/80 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2679/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13/80 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2679/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2679/25000 : ℝ) ^ (4951/1024 : ℝ) ≤ (204289486933911/10000000000000000000 : ℝ) := by
    have hpowers : (2679/25000 : ℝ)^4951 ≤ (204289486933911/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2679 : ℕ)^4951*10000000000000000000^1024 ≤ 204289486933911^1024*25000^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2679 25000 204289486933911 10000000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2679/25000 : ℝ)) (X := (204289486933911/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13/80 : ℝ) ^ (4951/1024 : ℝ) ≤ (955843661776807/6250000000000000000 : ℝ) := by
    have hpowers : (13/80 : ℝ)^4951 ≤ (955843661776807/6250000000000000000 : ℝ)^1024 := by
      have hnat : (13 : ℕ)^4951*6250000000000000000^1024 ≤ 955843661776807^1024*80^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13 80 955843661776807 6250000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13/80 : ℝ)) (X := (955843661776807/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000204289486933911/5000000000000000000 : ℝ) ≤ (10000084503754803/10000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (5000204289486933911/5000000000000000000 : ℝ)^1024 ≤ (10000084503754803/10000000000000000 : ℝ)^4951 := by
      have hnat : (5000204289486933911 : ℕ)^1024*10000000000000000^4951 ≤ 10000084503754803^4951*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000204289486933911 5000000000000000000 10000084503754803 10000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084503754803/10000000000000000 : ℝ)) (X := (5000204289486933911/5000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008668196728884011/50000000000000000000 : ℝ) ≤ (1000035853860791/1000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (50008668196728884011/50000000000000000000 : ℝ)^1024 ≤ (1000035853860791/1000000000000000 : ℝ)^4951 := by
      have hnat : (50008668196728884011 : ℕ)^1024*1000000000000000^4951 ≤ 1000035853860791^4951*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008668196728884011 50000000000000000000 1000035853860791 1000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000035853860791/1000000000000000 : ℝ)) (X := (50008668196728884011/50000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3125955843661776807/3125000000000000000 : ℝ) ≤ (10000632573461017/10000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (3125955843661776807/3125000000000000000 : ℝ)^1024 ≤ (10000632573461017/10000000000000000 : ℝ)^4951 := by
      have hnat : (3125955843661776807 : ℕ)^1024*10000000000000000^4951 ≤ 10000632573461017^4951*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125955843661776807 3125000000000000000 10000632573461017 10000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000632573461017/10000000000000000 : ℝ)) (X := (3125955843661776807/3125000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(204289486933911/10000000000000000000 : ℝ) ≤ ((27667297264403645289/27670000000000000000 : ℝ)+2*(274034853107/553400000000000 : ℝ)*(2679/25000 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (27667297264403645289/27670000000000000000 : ℝ)+2*(274034853107/553400000000000 : ℝ)*(2679/25000 : ℝ)=(10000084503754803/10000000000000000 : ℝ) by norm_num, show 1+2*(204289486933911/10000000000000000000 : ℝ)=(5000204289486933911/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(955843661776807/6250000000000000000 : ℝ)+(204289486933911/10000000000000000000 : ℝ) ≤ ((27667297264403645289/27670000000000000000 : ℝ)+(274034853107/553400000000000 : ℝ)*((13/80 : ℝ)+(2679/25000 : ℝ)))^(4951/1024 : ℝ) := by
    rw [show (27667297264403645289/27670000000000000000 : ℝ)+(274034853107/553400000000000 : ℝ)*((13/80 : ℝ)+(2679/25000 : ℝ))=(1000035853860791/1000000000000000 : ℝ) by norm_num, show 1+(955843661776807/6250000000000000000 : ℝ)+(204289486933911/10000000000000000000 : ℝ)=(50008668196728884011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(955843661776807/6250000000000000000 : ℝ) ≤ ((27667297264403645289/27670000000000000000 : ℝ)+2*(274034853107/553400000000000 : ℝ)*(13/80 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (27667297264403645289/27670000000000000000 : ℝ)+2*(274034853107/553400000000000 : ℝ)*(13/80 : ℝ)=(10000632573461017/10000000000000000 : ℝ) by norm_num, show 1+2*(955843661776807/6250000000000000000 : ℝ)=(3125955843661776807/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27667297264403645289/27670000000000000000 : ℝ)*(X 1 0+X 2 0)+(274034853107/553400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (2679/25000 : ℝ)) (hi := (13/80 : ℝ)) (c := (27667297264403645289/27670000000000000000 : ℝ)) (alpha := (274034853107/553400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27667297264403645289/27670000000000000000 : ℝ)*(X 0 1+X 2 1)+(274034853107/553400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (2679/25000 : ℝ)) (hi := (13/80 : ℝ)) (c := (27667297264403645289/27670000000000000000 : ℝ)) (alpha := (274034853107/553400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27667297264403645289/27670000000000000000 : ℝ)*(X 0 2+X 1 2)+(274034853107/553400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (2679/25000 : ℝ)) (hi := (13/80 : ℝ)) (c := (27667297264403645289/27670000000000000000 : ℝ)) (alpha := (274034853107/553400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1333513427/10000000000 : ℝ)*X 0 0+(1081171911/2000000000 : ℝ)*X 0 1+(1351465201/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625465443/5000000000 : ℝ)*X 1 0+(-775652939/5000000000 : ℝ)*X 1 1+(5405859991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625465353/5000000000 : ℝ)*X 2 0+(5405860473/10000000000 : ℝ)*X 2 1+(-775652729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4450120313/10000000000 : ℝ)*X 0 0+(4047665861/10000000000 : ℝ)*X 0 1+(2023833133/5000000000 : ℝ)*X 0 2+(4450120313/10000000000 : ℝ)*X 1 0+(4047665861/10000000000 : ℝ)*X 1 1+(2023833133/5000000000 : ℝ)*X 1 2+(4450120313/10000000000 : ℝ)*X 2 0+(4047665861/10000000000 : ℝ)*X 2 1+(2023833133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-463419021/2500000000 : ℝ)*X 0 0+(5215946753/10000000000 : ℝ)*X 0 1+(208637853/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16816021/31250000 : ℝ)*X 1 0+(-326598419/2000000000 : ℝ)*X 1 1+(2607973369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((538112713/1000000000 : ℝ)*X 2 0+(651993289/1250000000 : ℝ)*X 2 1+(-102062007/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1945514173/5000000000 : ℝ)*X 0 0+(540861349/1250000000 : ℝ)*X 0 1+(4326890739/10000000000 : ℝ)*X 0 2+(1945514173/5000000000 : ℝ)*X 1 0+(540861349/1250000000 : ℝ)*X 1 1+(4326890739/10000000000 : ℝ)*X 1 2+(1945514173/5000000000 : ℝ)*X 2 0+(540861349/1250000000 : ℝ)*X 2 1+(4326890739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1742651341/10000000000 : ℝ)*X 0 0+(5079155079/10000000000 : ℝ)*X 0 1+(5435204867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1307703947/2500000000 : ℝ)*X 1 0+(-307652463/2000000000 : ℝ)*X 1 1+(1358801187/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307703913/2500000000 : ℝ)*X 2 0+(2717602421/5000000000 : ℝ)*X 2 1+(-1538262371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((453413443/1000000000 : ℝ)*X 0 0+(1001110777/2500000000 : ℝ)*X 0 1+(250277703/625000000 : ℝ)*X 0 2+(453413443/1000000000 : ℝ)*X 1 0+(1001110777/2500000000 : ℝ)*X 1 1+(250277703/625000000 : ℝ)*X 1 2+(453413443/1000000000 : ℝ)*X 2 0+(1001110777/2500000000 : ℝ)*X 2 1+(250277703/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1442666673/10000000000 : ℝ)*X 0 0+(692186381/1250000000 : ℝ)*X 0 1+(5196148167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5394709013/10000000000 : ℝ)*X 1 0+(-6411047/39062500 : ℝ)*X 1 1+(259807469/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((134867747/250000000 : ℝ)*X 2 0+(5196148647/10000000000 : ℝ)*X 2 1+(-1641227841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3831115971/10000000000 : ℝ)*X 0 0+(435594633/1000000000 : ℝ)*X 0 1+(4355945159/10000000000 : ℝ)*X 0 2+(3831115971/10000000000 : ℝ)*X 1 0+(435594633/1000000000 : ℝ)*X 1 1+(4355945159/10000000000 : ℝ)*X 1 2+(3831115971/10000000000 : ℝ)*X 2 0+(435594633/1000000000 : ℝ)*X 2 1+(4355945159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-32553/50000 : ℝ) ≤ (-450352944259631288552649299606049/691750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (731577/50000000000000 : ℝ)*(lower2) + (1628189/4000000000000 : ℝ)*(upper4) + (3807523/12500000000000 : ℝ)*(upper5) + (888007334226351/50000000000000 : ℝ)*(major0) + (888007334226351/50000000000000 : ℝ)*(major1) + (888007334226351/50000000000000 : ℝ)*(major2) + (4419314803/100000000000000 : ℝ)*(sp2) + (204900473/25000000000000 : ℝ)*(sp3) + (1295791062394163/50000000000000 : ℝ)*(sp4) + (647895437263389/25000000000000 : ℝ)*(sp5) + (103663286066331/4000000000000 : ℝ)*(sp6) + (982143088084899/100000000000000 : ℝ)*(sp7) + (277886547/6250000000000 : ℝ)*(sp8) + (2410959761/50000000000000 : ℝ)*(sp13) + (982143907686791/100000000000000 : ℝ)*(f.failure) + (1295793285486539/50000000000000 : ℝ)*(f.sum) + (40478020733167/13835000000000000000000000000 : ℝ)*base65 + (4637490329782339561/1383500000000000000000000000000000 : ℝ)*base68 + (10542123976775839561/1383500000000000000000000000000000 : ℝ)*base70 + (7451982356857339561/1383500000000000000000000000000000 : ℝ)*base72 + (746016630397/13835000000000000000000000000 : ℝ)*base73 + (11374308570934839561/1383500000000000000000000000000000 : ℝ)*base76 + (2537615429884339561/1383500000000000000000000000000000 : ℝ)*base78 + (5117361085887839561/1383500000000000000000000000000000 : ℝ)*base80 + (3949211633427/3458750000000000000000000000 : ℝ)*base82 + (122065281/10000000000000000000000 : ℝ)*base89 + (122065281/10000000000000000000000 : ℝ)*base91 + (122065281/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58723/100000 : ℝ) ≤ (812462414503235372792085952274043/1383500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (226451/800000000000 : ℝ)*(lower1) + (66823389/100000000000000 : ℝ)*(lower3) + (2558699/6250000000000 : ℝ)*(upper4) + (3399471/100000000000000 : ℝ)*(upper5) + (373538871911827/20000000000000 : ℝ)*(major0) + (373538871911827/20000000000000 : ℝ)*(major1) + (58365448736223/3125000000000 : ℝ)*(major2) + (1341480963083503/50000000000000 : ℝ)*(sp0) + (1341485245335861/50000000000000 : ℝ)*(sp1) + (1341481818488553/50000000000000 : ℝ)*(sp2) + (1032840202619661/100000000000000 : ℝ)*(sp3) + (1370738923/20000000000000 : ℝ)*(sp6) + (186043009/6250000000000 : ℝ)*(sp7) + (1712900943/20000000000000 : ℝ)*(sp12) + (206568635861561/20000000000000 : ℝ)*(f.failure) + (1341485245335861/50000000000000 : ℝ)*(f.sum) + (229714970691597/55340000000000000000000000000 : ℝ)*base65 + (219259350112853003/553400000000000000000000000000000 : ℝ)*base67 + (2091640641826785019/172937500000000000000000000000000 : ℝ)*base69 + (1532922697193146997/553400000000000000000000000000000 : ℝ)*base72 + (90749020276977/55340000000000000000000000000 : ℝ)*base73 + (1249204270989847519/172937500000000000000000000000000 : ℝ)*base75 + (407204767856183003/553400000000000000000000000000000 : ℝ)*base77 + (2741291744130583003/553400000000000000000000000000000 : ℝ)*base79 + (1893411403813/5534000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2499649/2000000000000000000000 : ℝ)*base90 + (2499649/2000000000000000000000 : ℝ)*base92 + (22499649/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81359/100000 : ℝ) ≤ (1125632810985199442429130666464133/1383500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7803051/100000000000000 : ℝ)*(upper0) + (1969529/20000000000000 : ℝ)*(upper1) + (17950227/50000000000000 : ℝ)*(upper2) + (489931952159633/25000000000000 : ℝ)*(major0) + (489931952159633/25000000000000 : ℝ)*(major1) + (1959727808638533/100000000000000 : ℝ)*(major2) + (995080181/20000000000000 : ℝ)*(sp1) + (3058538747/50000000000000 : ℝ)*(sp2) + (595768867/20000000000000 : ℝ)*(sp3) + (870544283/50000000000000 : ℝ)*(sp4) + (702148845218797/25000000000000 : ℝ)*(sp8) + (2808592146562849/100000000000000 : ℝ)*(sp9) + (140429550244313/5000000000000 : ℝ)*(sp10) + (541867550898199/50000000000000 : ℝ)*(sp11) + (1083738080640733/100000000000000 : ℝ)*(f.failure) + (1404298560981877/50000000000000 : ℝ)*(f.sum) + (1842438585867/11068000000000000000000000000 : ℝ)*base65 + (2988484872543943563/691750000000000000000000000000000 : ℝ)*base68 + (6874571591375521037/2767000000000000000000000000000000 : ℝ)*base69 + (2635065209857943563/691750000000000000000000000000000 : ℝ)*base72 + (32324374101399/11068000000000000000000000000 : ℝ)*base73 + (163105286288521037/2767000000000000000000000000000000 : ℝ)*base75 + (1762431081275281063/691750000000000000000000000000000 : ℝ)*base78 + (5312299735531218937/691750000000000000000000000000000 : ℝ)*base79 + (527626229177/3458750000000000000000000000 : ℝ)*base82 + (78916603/10000000000000000000000 : ℝ)*base89 + (78916603/10000000000000000000000 : ℝ)*base91 + (21083397/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-8831/10000 : ℝ) ≤ (-1221738327287598520964186812672827/1383500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205869999/100000000000000 : ℝ)*(lower2) + (153336009/100000000000000 : ℝ)*(upper3) + (54343463/50000000000000 : ℝ)*(upper5) + (2004276636372881/100000000000000 : ℝ)*(major0) + (2004276636372881/100000000000000 : ℝ)*(major1) + (1002138318186441/50000000000000 : ℝ)*(major2) + (2818443011/50000000000000 : ℝ)*(sp0) + (1771646353/5000000000000 : ℝ)*(sp6) + (18936397019/50000000000000 : ℝ)*(sp7) + (140240737/4000000000000 : ℝ)*(sp8) + (2929606283179207/100000000000000 : ℝ)*(sp12) + (1464807713041827/50000000000000 : ℝ)*(sp13) + (2929579993156593/100000000000000 : ℝ)*(sp14) + (1108335905136289/100000000000000 : ℝ)*(sp15) + (1108373777930327/100000000000000 : ℝ)*(f.failure) + (1464807713041827/50000000000000 : ℝ)*(f.sum) + (24349587194061/55340000000000000000000000000 : ℝ)*base65 + (626795899252707609/2767000000000000000000000000000000 : ℝ)*base67 + (2231080177662498551/1383500000000000000000000000000000 : ℝ)*base70 + (21073316050641292391/2767000000000000000000000000000000 : ℝ)*base72 + (192419967342721/55340000000000000000000000000 : ℝ)*base73 + (4855601413139501449/1383500000000000000000000000000000 : ℝ)*base75 + (9362148323857357609/2767000000000000000000000000000000 : ℝ)*base77 + (8015171478707357609/2767000000000000000000000000000000 : ℝ)*base79 + (202581907650733/27670000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (102167857/10000000000000000000000 : ℝ)*base89 + (102167857/10000000000000000000000 : ℝ)*base91 + (2167857/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1659_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13/80 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2679/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32553/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58723/100000 : ℝ) else (81359/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8831/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1659_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1659_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32553/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58723/100000 : ℝ) else (81359/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8831/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1659_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1659_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1659_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32553/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58723/100000 : ℝ) else (81359/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8831/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1659_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

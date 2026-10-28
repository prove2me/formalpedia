-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:23:35.893527+00:00
-- url     : https://prove2.me/submissions/ed834efc-7603-4fd5-9c56-82d88adc211d

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
theorem support_rectangle_w1281_box_0 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1925596673/10000000000 : ℝ)*x 0 + (337028903/625000000 : ℝ)*x 1 + (5392462741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925596673/10000000000 : ℝ)^4241 ≤ (11398193969427/100000000000000 : ℝ)^3217 := by
    have hnat : (1925596673 : ℕ)^4241*100000000000000^3217 ≤ 11398193969427^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925596673 10000000000 11398193969427 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337028903/625000000 : ℝ)^4241 ≤ (22150450713121/50000000000000 : ℝ)^3217 := by
    have hnat : (337028903 : ℕ)^4241*50000000000000^3217 ≤ 22150450713121^3217*625000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337028903 625000000 22150450713121 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392462741/10000000000 : ℝ)^4241 ≤ (8860180919907/20000000000000 : ℝ)^3217 := by
    have hnat : (5392462741 : ℕ)^4241*20000000000000^3217 ≤ 8860180919907^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392462741 10000000000 8860180919907 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1925596673/10000000000 : ℝ), (337028903/625000000 : ℝ), (5392462741/10000000000 : ℝ)] ![(11398193969427/100000000000000 : ℝ), (22150450713121/50000000000000 : ℝ), (8860180919907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1925596673/10000000000 : ℝ)|^4241 ≤ (11398193969427/100000000000000 : ℝ)^3217
        have hw : |(-1925596673/10000000000 : ℝ)|=(1925596673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337028903/625000000 : ℝ)|^4241 ≤ (22150450713121/50000000000000 : ℝ)^3217
        have hw : |(337028903/625000000 : ℝ)|=(337028903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392462741/10000000000 : ℝ)|^4241 ≤ (8860180919907/20000000000000 : ℝ)^3217
        have hw : |(5392462741/10000000000 : ℝ)|=(5392462741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_1 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660520587/1250000000 : ℝ)*x 0 + (-103681949/500000000 : ℝ)*x 1 + (5392462399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660520587/1250000000 : ℝ)^4241 ≤ (2695735293069/6250000000000 : ℝ)^3217 := by
    have hnat : (660520587 : ℕ)^4241*6250000000000^3217 ≤ 2695735293069^3217*1250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660520587 1250000000 2695735293069 6250000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103681949/500000000 : ℝ)^4241 ≤ (6283667196191/50000000000000 : ℝ)^3217 := by
    have hnat : (103681949 : ℕ)^4241*50000000000000^3217 ≤ 6283667196191^3217*500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103681949 500000000 6283667196191 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392462399/10000000000 : ℝ)^4241 ≤ (22150450447777/50000000000000 : ℝ)^3217 := by
    have hnat : (5392462399 : ℕ)^4241*50000000000000^3217 ≤ 22150450447777^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392462399 10000000000 22150450447777 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660520587/1250000000 : ℝ), (-103681949/500000000 : ℝ), (5392462399/10000000000 : ℝ)] ![(2695735293069/6250000000000 : ℝ), (6283667196191/50000000000000 : ℝ), (22150450447777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660520587/1250000000 : ℝ)|^4241 ≤ (2695735293069/6250000000000 : ℝ)^3217
        have hw : |(660520587/1250000000 : ℝ)|=(660520587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103681949/500000000 : ℝ)|^4241 ≤ (6283667196191/50000000000000 : ℝ)^3217
        have hw : |(-103681949/500000000 : ℝ)|=(103681949/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392462399/10000000000 : ℝ)|^4241 ≤ (22150450447777/50000000000000 : ℝ)^3217
        have hw : |(5392462399/10000000000 : ℝ)|=(5392462399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_2 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165130139/312500000 : ℝ)*x 0 + (5392462469/10000000000 : ℝ)*x 1 + (-103681961/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165130139/312500000 : ℝ)^4241 ≤ (21565881010233/50000000000000 : ℝ)^3217 := by
    have hnat : (165130139 : ℕ)^4241*50000000000000^3217 ≤ 21565881010233^3217*312500000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165130139 312500000 21565881010233 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392462469/10000000000 : ℝ)^4241 ≤ (44300901653679/100000000000000 : ℝ)^3217 := by
    have hnat : (5392462469 : ℕ)^4241*100000000000000^3217 ≤ 44300901653679^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392462469 10000000000 44300901653679 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103681961/500000000 : ℝ)^4241 ≤ (1570917038737/12500000000000 : ℝ)^3217 := by
    have hnat : (103681961 : ℕ)^4241*12500000000000^3217 ≤ 1570917038737^3217*500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103681961 500000000 1570917038737 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165130139/312500000 : ℝ), (5392462469/10000000000 : ℝ), (-103681961/500000000 : ℝ)] ![(21565881010233/50000000000000 : ℝ), (44300901653679/100000000000000 : ℝ), (1570917038737/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165130139/312500000 : ℝ)|^4241 ≤ (21565881010233/50000000000000 : ℝ)^3217
        have hw : |(165130139/312500000 : ℝ)|=(165130139/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392462469/10000000000 : ℝ)|^4241 ≤ (44300901653679/100000000000000 : ℝ)^3217
        have hw : |(5392462469/10000000000 : ℝ)|=(5392462469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103681961/500000000 : ℝ)|^4241 ≤ (1570917038737/12500000000000 : ℝ)^3217
        have hw : |(-103681961/500000000 : ℝ)|=(103681961/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_3 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1123134957/2500000000 : ℝ)*x 0 + (4272005473/10000000000 : ℝ)*x 1 + (4272005601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123134957/2500000000 : ℝ)^4241 ≤ (870596678737/2500000000000 : ℝ)^3217 := by
    have hnat : (1123134957 : ℕ)^4241*2500000000000^3217 ≤ 870596678737^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123134957 2500000000 870596678737 2500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4272005473/10000000000 : ℝ)^4241 ≤ (32588065778109/100000000000000 : ℝ)^3217 := by
    have hnat : (4272005473 : ℕ)^4241*100000000000000^3217 ≤ 32588065778109^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272005473 10000000000 32588065778109 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4272005601/10000000000 : ℝ)^4241 ≤ (8147016766333/25000000000000 : ℝ)^3217 := by
    have hnat : (4272005601 : ℕ)^4241*25000000000000^3217 ≤ 8147016766333^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272005601 10000000000 8147016766333 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123134957/2500000000 : ℝ), (4272005473/10000000000 : ℝ), (4272005601/10000000000 : ℝ)] ![(870596678737/2500000000000 : ℝ), (32588065778109/100000000000000 : ℝ), (8147016766333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123134957/2500000000 : ℝ)|^4241 ≤ (870596678737/2500000000000 : ℝ)^3217
        have hw : |(1123134957/2500000000 : ℝ)|=(1123134957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4272005473/10000000000 : ℝ)|^4241 ≤ (32588065778109/100000000000000 : ℝ)^3217
        have hw : |(4272005473/10000000000 : ℝ)|=(4272005473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4272005601/10000000000 : ℝ)|^4241 ≤ (8147016766333/25000000000000 : ℝ)^3217
        have hw : |(4272005601/10000000000 : ℝ)|=(4272005601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_4 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-56822751/250000000 : ℝ)*x 0 + (1052678069/2000000000 : ℝ)*x 1 + (5263390703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56822751/250000000 : ℝ)^4241 ≤ (14183277370081/100000000000000 : ℝ)^3217 := by
    have hnat : (56822751 : ℕ)^4241*100000000000000^3217 ≤ 14183277370081^3217*250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56822751 250000000 14183277370081 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052678069/2000000000 : ℝ)^4241 ≤ (21454179689953/50000000000000 : ℝ)^3217 := by
    have hnat : (1052678069 : ℕ)^4241*50000000000000^3217 ≤ 21454179689953^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052678069 2000000000 21454179689953 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263390703/10000000000 : ℝ)^4241 ≤ (10727090806847/25000000000000 : ℝ)^3217 := by
    have hnat : (5263390703 : ℕ)^4241*25000000000000^3217 ≤ 10727090806847^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263390703 10000000000 10727090806847 25000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56822751/250000000 : ℝ), (1052678069/2000000000 : ℝ), (5263390703/10000000000 : ℝ)] ![(14183277370081/100000000000000 : ℝ), (21454179689953/50000000000000 : ℝ), (10727090806847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56822751/250000000 : ℝ)|^4241 ≤ (14183277370081/100000000000000 : ℝ)^3217
        have hw : |(-56822751/250000000 : ℝ)|=(56822751/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052678069/2000000000 : ℝ)|^4241 ≤ (21454179689953/50000000000000 : ℝ)^3217
        have hw : |(1052678069/2000000000 : ℝ)|=(1052678069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263390703/10000000000 : ℝ)|^4241 ≤ (10727090806847/25000000000000 : ℝ)^3217
        have hw : |(5263390703/10000000000 : ℝ)|=(5263390703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_5 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375059479/10000000000 : ℝ)*x 0 + (-265622221/1250000000 : ℝ)*x 1 + (5263390581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375059479/10000000000 : ℝ)^4241 ≤ (44112517995563/100000000000000 : ℝ)^3217 := by
    have hnat : (5375059479 : ℕ)^4241*100000000000000^3217 ≤ 44112517995563^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375059479 10000000000 44112517995563 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265622221/1250000000 : ℝ)^4241 ≤ (6489560041667/50000000000000 : ℝ)^3217 := by
    have hnat : (265622221 : ℕ)^4241*50000000000000^3217 ≤ 6489560041667^3217*1250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265622221 1250000000 6489560041667 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263390581/10000000000 : ℝ)^4241 ≤ (8581672383247/20000000000000 : ℝ)^3217 := by
    have hnat : (5263390581 : ℕ)^4241*20000000000000^3217 ≤ 8581672383247^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263390581 10000000000 8581672383247 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375059479/10000000000 : ℝ), (-265622221/1250000000 : ℝ), (5263390581/10000000000 : ℝ)] ![(44112517995563/100000000000000 : ℝ), (6489560041667/50000000000000 : ℝ), (8581672383247/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375059479/10000000000 : ℝ)|^4241 ≤ (44112517995563/100000000000000 : ℝ)^3217
        have hw : |(5375059479/10000000000 : ℝ)|=(5375059479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265622221/1250000000 : ℝ)|^4241 ≤ (6489560041667/50000000000000 : ℝ)^3217
        have hw : |(-265622221/1250000000 : ℝ)|=(265622221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263390581/10000000000 : ℝ)|^4241 ≤ (8581672383247/20000000000000 : ℝ)^3217
        have hw : |(5263390581/10000000000 : ℝ)|=(5263390581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_6 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375059809/10000000000 : ℝ)*x 0 + (5263390337/10000000000 : ℝ)*x 1 + (-2124977649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375059809/10000000000 : ℝ)^4241 ≤ (2757032597869/6250000000000 : ℝ)^3217 := by
    have hnat : (5375059809 : ℕ)^4241*6250000000000^3217 ≤ 2757032597869^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375059809 10000000000 2757032597869 6250000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263390337/10000000000 : ℝ)^4241 ≤ (42908359293929/100000000000000 : ℝ)^3217 := by
    have hnat : (5263390337 : ℕ)^4241*100000000000000^3217 ≤ 42908359293929^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263390337 10000000000 42908359293929 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124977649/10000000000 : ℝ)^4241 ≤ (811194945321/6250000000000 : ℝ)^3217 := by
    have hnat : (2124977649 : ℕ)^4241*6250000000000^3217 ≤ 811194945321^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124977649 10000000000 811194945321 6250000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375059809/10000000000 : ℝ), (5263390337/10000000000 : ℝ), (-2124977649/10000000000 : ℝ)] ![(2757032597869/6250000000000 : ℝ), (42908359293929/100000000000000 : ℝ), (811194945321/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375059809/10000000000 : ℝ)|^4241 ≤ (2757032597869/6250000000000 : ℝ)^3217
        have hw : |(5375059809/10000000000 : ℝ)|=(5375059809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263390337/10000000000 : ℝ)|^4241 ≤ (42908359293929/100000000000000 : ℝ)^3217
        have hw : |(5263390337/10000000000 : ℝ)|=(5263390337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124977649/10000000000 : ℝ)|^4241 ≤ (811194945321/6250000000000 : ℝ)^3217
        have hw : |(-2124977649/10000000000 : ℝ)|=(2124977649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_7 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4192285227/10000000000 : ℝ)*x 0 + (2211038597/5000000000 : ℝ)*x 1 + (1105519233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192285227/10000000000 : ℝ)^4241 ≤ (31788755634089/100000000000000 : ℝ)^3217 := by
    have hnat : (4192285227 : ℕ)^4241*100000000000000^3217 ≤ 31788755634089^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192285227 10000000000 31788755634089 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211038597/5000000000 : ℝ)^4241 ≤ (85264058769/250000000000 : ℝ)^3217 := by
    have hnat : (2211038597 : ℕ)^4241*250000000000^3217 ≤ 85264058769^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211038597 5000000000 85264058769 250000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105519233/2500000000 : ℝ)^4241 ≤ (34105620843699/100000000000000 : ℝ)^3217 := by
    have hnat : (1105519233 : ℕ)^4241*100000000000000^3217 ≤ 34105620843699^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105519233 2500000000 34105620843699 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192285227/10000000000 : ℝ), (2211038597/5000000000 : ℝ), (1105519233/2500000000 : ℝ)] ![(31788755634089/100000000000000 : ℝ), (85264058769/250000000000 : ℝ), (34105620843699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192285227/10000000000 : ℝ)|^4241 ≤ (31788755634089/100000000000000 : ℝ)^3217
        have hw : |(4192285227/10000000000 : ℝ)|=(4192285227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2211038597/5000000000 : ℝ)|^4241 ≤ (85264058769/250000000000 : ℝ)^3217
        have hw : |(2211038597/5000000000 : ℝ)|=(2211038597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105519233/2500000000 : ℝ)|^4241 ≤ (34105620843699/100000000000000 : ℝ)^3217
        have hw : |(1105519233/2500000000 : ℝ)|=(1105519233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_8 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200150109/10000000000 : ℝ)*x 0 + (5174832483/10000000000 : ℝ)*x 1 + (337906461/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200150109/10000000000 : ℝ)^4241 ≤ (1358779469381/10000000000000 : ℝ)^3217 := by
    have hnat : (2200150109 : ℕ)^4241*10000000000000^3217 ≤ 1358779469381^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200150109 10000000000 1358779469381 10000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174832483/10000000000 : ℝ)^4241 ≤ (5244896582127/12500000000000 : ℝ)^3217 := by
    have hnat : (5174832483 : ℕ)^4241*12500000000000^3217 ≤ 5244896582127^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174832483 10000000000 5244896582127 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337906461/625000000 : ℝ)^4241 ≤ (889060652511/2000000000000 : ℝ)^3217 := by
    have hnat : (337906461 : ℕ)^4241*2000000000000^3217 ≤ 889060652511^3217*625000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337906461 625000000 889060652511 2000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200150109/10000000000 : ℝ), (5174832483/10000000000 : ℝ), (337906461/625000000 : ℝ)] ![(1358779469381/10000000000000 : ℝ), (5244896582127/12500000000000 : ℝ), (889060652511/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200150109/10000000000 : ℝ)|^4241 ≤ (1358779469381/10000000000000 : ℝ)^3217
        have hw : |(-2200150109/10000000000 : ℝ)|=(2200150109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174832483/10000000000 : ℝ)|^4241 ≤ (5244896582127/12500000000000 : ℝ)^3217
        have hw : |(5174832483/10000000000 : ℝ)|=(5174832483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337906461/625000000 : ℝ)|^4241 ≤ (889060652511/2000000000000 : ℝ)^3217
        have hw : |(337906461/625000000 : ℝ)|=(337906461/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_9 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527427053/1000000000 : ℝ)*x 0 + (-413583383/2000000000 : ℝ)*x 1 + (540650349/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527427053/1000000000 : ℝ)^4241 ≤ (8605065774807/20000000000000 : ℝ)^3217 := by
    have hnat : (527427053 : ℕ)^4241*20000000000000^3217 ≤ 8605065774807^3217*1000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527427053 1000000000 8605065774807 20000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413583383/2000000000 : ℝ)^4241 ≤ (12521637241041/100000000000000 : ℝ)^3217 := by
    have hnat : (413583383 : ℕ)^4241*100000000000000^3217 ≤ 12521637241041^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413583383 2000000000 12521637241041 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540650349/1000000000 : ℝ)^4241 ≤ (2778314616327/6250000000000 : ℝ)^3217 := by
    have hnat : (540650349 : ℕ)^4241*6250000000000^3217 ≤ 2778314616327^3217*1000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540650349 1000000000 2778314616327 6250000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527427053/1000000000 : ℝ), (-413583383/2000000000 : ℝ), (540650349/1000000000 : ℝ)] ![(8605065774807/20000000000000 : ℝ), (12521637241041/100000000000000 : ℝ), (2778314616327/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527427053/1000000000 : ℝ)|^4241 ≤ (8605065774807/20000000000000 : ℝ)^3217
        have hw : |(527427053/1000000000 : ℝ)|=(527427053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413583383/2000000000 : ℝ)|^4241 ≤ (12521637241041/100000000000000 : ℝ)^3217
        have hw : |(-413583383/2000000000 : ℝ)|=(413583383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540650349/1000000000 : ℝ)|^4241 ≤ (2778314616327/6250000000000 : ℝ)^3217
        have hw : |(540650349/1000000000 : ℝ)|=(540650349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_10 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105485411/200000000 : ℝ)*x 0 + (1081300677/2000000000 : ℝ)*x 1 + (-2067917031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105485411/200000000 : ℝ)^4241 ≤ (268908306807/625000000000 : ℝ)^3217 := by
    have hnat : (105485411 : ℕ)^4241*625000000000^3217 ≤ 268908306807^3217*200000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105485411 200000000 268908306807 625000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081300677/2000000000 : ℝ)^4241 ≤ (44453032723103/100000000000000 : ℝ)^3217 := by
    have hnat : (1081300677 : ℕ)^4241*100000000000000^3217 ≤ 44453032723103^3217*2000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081300677 2000000000 44453032723103 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067917031/10000000000 : ℝ)^4241 ≤ (500865526681/4000000000000 : ℝ)^3217 := by
    have hnat : (2067917031 : ℕ)^4241*4000000000000^3217 ≤ 500865526681^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067917031 10000000000 500865526681 4000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105485411/200000000 : ℝ), (1081300677/2000000000 : ℝ), (-2067917031/10000000000 : ℝ)] ![(268908306807/625000000000 : ℝ), (44453032723103/100000000000000 : ℝ), (500865526681/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105485411/200000000 : ℝ)|^4241 ≤ (268908306807/625000000000 : ℝ)^3217
        have hw : |(105485411/200000000 : ℝ)|=(105485411/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081300677/2000000000 : ℝ)|^4241 ≤ (44453032723103/100000000000000 : ℝ)^3217
        have hw : |(1081300677/2000000000 : ℝ)|=(1081300677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067917031/10000000000 : ℝ)|^4241 ≤ (500865526681/4000000000000 : ℝ)^3217
        have hw : |(-2067917031/10000000000 : ℝ)|=(2067917031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_11 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (565580221/1250000000 : ℝ)*x 0 + (4255666659/10000000000 : ℝ)*x 1 + (531958381/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565580221/1250000000 : ℝ)^4241 ≤ (17576142357087/50000000000000 : ℝ)^3217 := by
    have hnat : (565580221 : ℕ)^4241*50000000000000^3217 ≤ 17576142357087^3217*1250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565580221 1250000000 17576142357087 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4255666659/10000000000 : ℝ)^4241 ≤ (32423855681807/100000000000000 : ℝ)^3217 := by
    have hnat : (4255666659 : ℕ)^4241*100000000000000^3217 ≤ 32423855681807^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255666659 10000000000 32423855681807 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531958381/1250000000 : ℝ)^4241 ≤ (32423859588991/100000000000000 : ℝ)^3217 := by
    have hnat : (531958381 : ℕ)^4241*100000000000000^3217 ≤ 32423859588991^3217*1250000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531958381 1250000000 32423859588991 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(565580221/1250000000 : ℝ), (4255666659/10000000000 : ℝ), (531958381/1250000000 : ℝ)] ![(17576142357087/50000000000000 : ℝ), (32423855681807/100000000000000 : ℝ), (32423859588991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(565580221/1250000000 : ℝ)|^4241 ≤ (17576142357087/50000000000000 : ℝ)^3217
        have hw : |(565580221/1250000000 : ℝ)|=(565580221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4255666659/10000000000 : ℝ)|^4241 ≤ (32423855681807/100000000000000 : ℝ)^3217
        have hw : |(4255666659/10000000000 : ℝ)|=(4255666659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531958381/1250000000 : ℝ)|^4241 ≤ (32423859588991/100000000000000 : ℝ)^3217
        have hw : |(531958381/1250000000 : ℝ)|=(531958381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_12 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-999409801/5000000000 : ℝ)*x 0 + (5478669557/10000000000 : ℝ)*x 1 + (5252379387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999409801/5000000000 : ℝ)^4241 ≤ (1496626973339/12500000000000 : ℝ)^3217 := by
    have hnat : (999409801 : ℕ)^4241*12500000000000^3217 ≤ 1496626973339^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999409801 5000000000 1496626973339 12500000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478669557/10000000000 : ℝ)^4241 ≤ (45236921877783/100000000000000 : ℝ)^3217 := by
    have hnat : (5478669557 : ℕ)^4241*100000000000000^3217 ≤ 45236921877783^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478669557 10000000000 45236921877783 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252379387/10000000000 : ℝ)^4241 ≤ (21395031159253/50000000000000 : ℝ)^3217 := by
    have hnat : (5252379387 : ℕ)^4241*50000000000000^3217 ≤ 21395031159253^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252379387 10000000000 21395031159253 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-999409801/5000000000 : ℝ), (5478669557/10000000000 : ℝ), (5252379387/10000000000 : ℝ)] ![(1496626973339/12500000000000 : ℝ), (45236921877783/100000000000000 : ℝ), (21395031159253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-999409801/5000000000 : ℝ)|^4241 ≤ (1496626973339/12500000000000 : ℝ)^3217
        have hw : |(-999409801/5000000000 : ℝ)|=(999409801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478669557/10000000000 : ℝ)|^4241 ≤ (45236921877783/100000000000000 : ℝ)^3217
        have hw : |(5478669557/10000000000 : ℝ)|=(5478669557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252379387/10000000000 : ℝ)|^4241 ≤ (21395031159253/50000000000000 : ℝ)^3217
        have hw : |(5252379387/10000000000 : ℝ)|=(5252379387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_13 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691405487/5000000000 : ℝ)*x 0 + (-106462539/500000000 : ℝ)*x 1 + (1313094791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691405487/5000000000 : ℝ)^4241 ≤ (22098201167819/50000000000000 : ℝ)^3217 := by
    have hnat : (2691405487 : ℕ)^4241*50000000000000^3217 ≤ 22098201167819^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691405487 5000000000 22098201167819 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106462539/500000000 : ℝ)^4241 ≤ (13013537723359/100000000000000 : ℝ)^3217 := by
    have hnat : (106462539 : ℕ)^4241*100000000000000^3217 ≤ 13013537723359^3217*500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106462539 500000000 13013537723359 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313094791/2500000000 : ℝ)^4241 ≤ (42790059923487/100000000000000 : ℝ)^3217 := by
    have hnat : (1313094791 : ℕ)^4241*100000000000000^3217 ≤ 42790059923487^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313094791 2500000000 42790059923487 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691405487/5000000000 : ℝ), (-106462539/500000000 : ℝ), (1313094791/2500000000 : ℝ)] ![(22098201167819/50000000000000 : ℝ), (13013537723359/100000000000000 : ℝ), (42790059923487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691405487/5000000000 : ℝ)|^4241 ≤ (22098201167819/50000000000000 : ℝ)^3217
        have hw : |(2691405487/5000000000 : ℝ)|=(2691405487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106462539/500000000 : ℝ)|^4241 ≤ (13013537723359/100000000000000 : ℝ)^3217
        have hw : |(-106462539/500000000 : ℝ)|=(106462539/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313094791/2500000000 : ℝ)|^4241 ≤ (42790059923487/100000000000000 : ℝ)^3217
        have hw : |(1313094791/2500000000 : ℝ)|=(1313094791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_14 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382810903/10000000000 : ℝ)*x 0 + (1313094853/2500000000 : ℝ)*x 1 + (-1064625273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382810903/10000000000 : ℝ)^4241 ≤ (44196401567121/100000000000000 : ℝ)^3217 := by
    have hnat : (5382810903 : ℕ)^4241*100000000000000^3217 ≤ 44196401567121^3217*10000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382810903 10000000000 44196401567121 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313094853/2500000000 : ℝ)^4241 ≤ (21395031293503/50000000000000 : ℝ)^3217 := by
    have hnat : (1313094853 : ℕ)^4241*50000000000000^3217 ≤ 21395031293503^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313094853 2500000000 21395031293503 50000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064625273/5000000000 : ℝ)^4241 ≤ (813345989873/6250000000000 : ℝ)^3217 := by
    have hnat : (1064625273 : ℕ)^4241*6250000000000^3217 ≤ 813345989873^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064625273 5000000000 813345989873 6250000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382810903/10000000000 : ℝ), (1313094853/2500000000 : ℝ), (-1064625273/5000000000 : ℝ)] ![(44196401567121/100000000000000 : ℝ), (21395031293503/50000000000000 : ℝ), (813345989873/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382810903/10000000000 : ℝ)|^4241 ≤ (44196401567121/100000000000000 : ℝ)^3217
        have hw : |(5382810903/10000000000 : ℝ)|=(5382810903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313094853/2500000000 : ℝ)|^4241 ≤ (21395031293503/50000000000000 : ℝ)^3217
        have hw : |(1313094853/2500000000 : ℝ)|=(1313094853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064625273/5000000000 : ℝ)|^4241 ≤ (813345989873/6250000000000 : ℝ)^3217
        have hw : |(-1064625273/5000000000 : ℝ)|=(1064625273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1281_box_15 (p : ℝ) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2083112037/5000000000 : ℝ)*x 0 + (2217434973/5000000000 : ℝ)*x 1 + (1108717309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083112037/5000000000 : ℝ)^4241 ≤ (31528498262213/100000000000000 : ℝ)^3217 := by
    have hnat : (2083112037 : ℕ)^4241*100000000000000^3217 ≤ 31528498262213^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083112037 5000000000 31528498262213 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217434973/5000000000 : ℝ)^4241 ≤ (34235754471899/100000000000000 : ℝ)^3217 := by
    have hnat : (2217434973 : ℕ)^4241*100000000000000^3217 ≤ 34235754471899^3217*5000000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217434973 5000000000 34235754471899 100000000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108717309/2500000000 : ℝ)^4241 ≤ (2139734202893/6250000000000 : ℝ)^3217 := by
    have hnat : (1108717309 : ℕ)^4241*6250000000000^3217 ≤ 2139734202893^3217*2500000000^4241 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108717309 2500000000 2139734202893 6250000000000 4241 3217 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4241/1024 : ℝ)) 4241 3217 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083112037/5000000000 : ℝ), (2217434973/5000000000 : ℝ), (1108717309/2500000000 : ℝ)] ![(31528498262213/100000000000000 : ℝ), (34235754471899/100000000000000 : ℝ), (2139734202893/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083112037/5000000000 : ℝ)|^4241 ≤ (31528498262213/100000000000000 : ℝ)^3217
        have hw : |(2083112037/5000000000 : ℝ)|=(2083112037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217434973/5000000000 : ℝ)|^4241 ≤ (34235754471899/100000000000000 : ℝ)^3217
        have hw : |(2217434973/5000000000 : ℝ)|=(2217434973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108717309/2500000000 : ℝ)|^4241 ≤ (2139734202893/6250000000000 : ℝ)^3217
        have hw : |(1108717309/2500000000 : ℝ)|=(1108717309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1281_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    -(62837/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7353/12500 : ℝ) ∧ (7959/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84111/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1833/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1833/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11/100 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1833/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1833/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11/100 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1833/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1833/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11/100 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11/100 : ℝ) ^ (265/64 : ℝ) ≤ (5367061741192857/50000000000000000000 : ℝ) := by
    have hpowers : (11/100 : ℝ)^265 ≤ (5367061741192857/50000000000000000000 : ℝ)^64 := by
      have hnat : (11 : ℕ)^265*50000000000000000000^64 ≤ 5367061741192857^64*100^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11 100 5367061741192857 50000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11/100 : ℝ)) (X := (5367061741192857/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hpowhi : (1833/12500 : ℝ) ^ (265/64 : ℝ) ≤ (8824783662127219/25000000000000000000 : ℝ) := by
    have hpowers : (1833/12500 : ℝ)^265 ≤ (8824783662127219/25000000000000000000 : ℝ)^64 := by
      have hnat : (1833 : ℕ)^265*25000000000000000000^64 ≤ 8824783662127219^64*12500^265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1833 12500 8824783662127219 25000000000000000000 265 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1833/12500 : ℝ)) (X := (8824783662127219/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005367061741192857/25000000000000000000 : ℝ) ≤ (5000259218104727/5000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (25005367061741192857/25000000000000000000 : ℝ)^64 ≤ (5000259218104727/5000000000000000 : ℝ)^265 := by
      have hnat : (25005367061741192857 : ℕ)^64*5000000000000000^265 ≤ 5000259218104727^265*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005367061741192857 25000000000000000000 5000259218104727 5000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000259218104727/5000000000000000 : ℝ)) (X := (25005367061741192857/25000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004603325813089459/10000000000000000000 : ℝ) ≤ (8000889242061/8000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (10004603325813089459/10000000000000000000 : ℝ)^64 ≤ (8000889242061/8000000000000 : ℝ)^265 := by
      have hnat : (10004603325813089459 : ℕ)^64*8000000000000^265 ≤ 8000889242061^265*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004603325813089459 10000000000000000000 8000889242061 8000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (8000889242061/8000000000000 : ℝ)) (X := (10004603325813089459/10000000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508824783662127219/12500000000000000000 : ℝ) ≤ (5000852334471523/5000000000000000 : ℝ) ^ (265/64 : ℝ) := by
    have hpowers : (12508824783662127219/12500000000000000000 : ℝ)^64 ≤ (5000852334471523/5000000000000000 : ℝ)^265 := by
      have hnat : (12508824783662127219 : ℕ)^64*5000000000000000^265 ≤ 5000852334471523^265*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508824783662127219 12500000000000000000 5000852334471523 5000000000000000 64 265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000852334471523/5000000000000000 : ℝ)) (X := (12508824783662127219/12500000000000000000 : ℝ)) (by norm_num) 265 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5367061741192857/50000000000000000000 : ℝ) ≤ ((1144651593443810233/1145000000000000000 : ℝ)+2*(148279091699/91600000000000 : ℝ)*(11/100 : ℝ))^(265/64 : ℝ) := by
    rw [show (1144651593443810233/1145000000000000000 : ℝ)+2*(148279091699/91600000000000 : ℝ)*(11/100 : ℝ)=(5000259218104727/5000000000000000 : ℝ) by norm_num, show 1+2*(5367061741192857/50000000000000000000 : ℝ)=(25005367061741192857/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8824783662127219/25000000000000000000 : ℝ)+(5367061741192857/50000000000000000000 : ℝ) ≤ ((1144651593443810233/1145000000000000000 : ℝ)+(148279091699/91600000000000 : ℝ)*((1833/12500 : ℝ)+(11/100 : ℝ)))^(265/64 : ℝ) := by
    rw [show (1144651593443810233/1145000000000000000 : ℝ)+(148279091699/91600000000000 : ℝ)*((1833/12500 : ℝ)+(11/100 : ℝ))=(8000889242061/8000000000000 : ℝ) by norm_num, show 1+(8824783662127219/25000000000000000000 : ℝ)+(5367061741192857/50000000000000000000 : ℝ)=(10004603325813089459/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8824783662127219/25000000000000000000 : ℝ) ≤ ((1144651593443810233/1145000000000000000 : ℝ)+2*(148279091699/91600000000000 : ℝ)*(1833/12500 : ℝ))^(265/64 : ℝ) := by
    rw [show (1144651593443810233/1145000000000000000 : ℝ)+2*(148279091699/91600000000000 : ℝ)*(1833/12500 : ℝ)=(5000852334471523/5000000000000000 : ℝ) by norm_num, show 1+2*(8824783662127219/25000000000000000000 : ℝ)=(12508824783662127219/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1144651593443810233/1145000000000000000 : ℝ)*(X 1 0+X 2 0)+(148279091699/91600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (11/100 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (1144651593443810233/1145000000000000000 : ℝ)) (alpha := (148279091699/91600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1144651593443810233/1145000000000000000 : ℝ)*(X 0 1+X 2 1)+(148279091699/91600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (11/100 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (1144651593443810233/1145000000000000000 : ℝ)) (alpha := (148279091699/91600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1144651593443810233/1145000000000000000 : ℝ)*(X 0 2+X 1 2)+(148279091699/91600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (265/64 : ℝ)) (lo := (11/100 : ℝ)) (hi := (1833/12500 : ℝ)) (c := (1144651593443810233/1145000000000000000 : ℝ)) (alpha := (148279091699/91600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1925596673/10000000000 : ℝ)*X 0 0+(337028903/625000000 : ℝ)*X 0 1+(5392462741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((660520587/1250000000 : ℝ)*X 1 0+(-103681949/500000000 : ℝ)*X 1 1+(5392462399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((165130139/312500000 : ℝ)*X 2 0+(5392462469/10000000000 : ℝ)*X 2 1+(-103681961/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1123134957/2500000000 : ℝ)*X 0 0+(4272005473/10000000000 : ℝ)*X 0 1+(4272005601/10000000000 : ℝ)*X 0 2+(1123134957/2500000000 : ℝ)*X 1 0+(4272005473/10000000000 : ℝ)*X 1 1+(4272005601/10000000000 : ℝ)*X 1 2+(1123134957/2500000000 : ℝ)*X 2 0+(4272005473/10000000000 : ℝ)*X 2 1+(4272005601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-56822751/250000000 : ℝ)*X 0 0+(1052678069/2000000000 : ℝ)*X 0 1+(5263390703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5375059479/10000000000 : ℝ)*X 1 0+(-265622221/1250000000 : ℝ)*X 1 1+(5263390581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5375059809/10000000000 : ℝ)*X 2 0+(5263390337/10000000000 : ℝ)*X 2 1+(-2124977649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4192285227/10000000000 : ℝ)*X 0 0+(2211038597/5000000000 : ℝ)*X 0 1+(1105519233/2500000000 : ℝ)*X 0 2+(4192285227/10000000000 : ℝ)*X 1 0+(2211038597/5000000000 : ℝ)*X 1 1+(1105519233/2500000000 : ℝ)*X 1 2+(4192285227/10000000000 : ℝ)*X 2 0+(2211038597/5000000000 : ℝ)*X 2 1+(1105519233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2200150109/10000000000 : ℝ)*X 0 0+(5174832483/10000000000 : ℝ)*X 0 1+(337906461/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527427053/1000000000 : ℝ)*X 1 0+(-413583383/2000000000 : ℝ)*X 1 1+(540650349/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((105485411/200000000 : ℝ)*X 2 0+(1081300677/2000000000 : ℝ)*X 2 1+(-2067917031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((565580221/1250000000 : ℝ)*X 0 0+(4255666659/10000000000 : ℝ)*X 0 1+(531958381/1250000000 : ℝ)*X 0 2+(565580221/1250000000 : ℝ)*X 1 0+(4255666659/10000000000 : ℝ)*X 1 1+(531958381/1250000000 : ℝ)*X 1 2+(565580221/1250000000 : ℝ)*X 2 0+(4255666659/10000000000 : ℝ)*X 2 1+(531958381/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-999409801/5000000000 : ℝ)*X 0 0+(5478669557/10000000000 : ℝ)*X 0 1+(5252379387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2691405487/5000000000 : ℝ)*X 1 0+(-106462539/500000000 : ℝ)*X 1 1+(1313094791/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5382810903/10000000000 : ℝ)*X 2 0+(1313094853/2500000000 : ℝ)*X 2 1+(-1064625273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2083112037/5000000000 : ℝ)*X 0 0+(2217434973/5000000000 : ℝ)*X 0 1+(1108717309/2500000000 : ℝ)*X 0 2+(2083112037/5000000000 : ℝ)*X 1 0+(2217434973/5000000000 : ℝ)*X 1 1+(1108717309/2500000000 : ℝ)*X 1 2+(2083112037/5000000000 : ℝ)*X 2 0+(2217434973/5000000000 : ℝ)*X 2 1+(1108717309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1281_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62837/100000 : ℝ) ≤ (-8993139496212636475154901936573/14312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32929219/100000000000000 : ℝ)*(upper1) + (16805723/20000000000000 : ℝ)*(lower2) + (1648081/12500000000000 : ℝ)*(lower3) + (40876559/100000000000000 : ℝ)*(upper5) + (712881502047673/25000000000000 : ℝ)*(major0) + (712881502047673/25000000000000 : ℝ)*(major1) + (712881502047673/25000000000000 : ℝ)*(major2) + (1185134839/25000000000000 : ℝ)*(sp2) + (66361793/2500000000000 : ℝ)*(sp3) + (3852057329847343/100000000000000 : ℝ)*(sp4) + (385205813015433/10000000000000 : ℝ)*(sp5) + (1926026694807487/50000000000000 : ℝ)*(sp6) + (935967976280823/50000000000000 : ℝ)*(sp7) + (800306987/100000000000000 : ℝ)*(sp12) + (935969303516683/50000000000000 : ℝ)*(f.failure) + (385205813015433/10000000000000 : ℝ)*(f.sum) + (5219524346767/1145000000000000000000000000 : ℝ)*base65 + (49902343933674691/28625000000000000000000000000000 : ℝ)*base68 + (100992628585325309/28625000000000000000000000000000 : ℝ)*base69 + (23259307274424691/28625000000000000000000000000000 : ℝ)*base72 + (5410276153047/1145000000000000000000000000 : ℝ)*base73 + (221096920005674691/28625000000000000000000000000000 : ℝ)*base76 + (66834978108575309/28625000000000000000000000000000 : ℝ)*base77 + (306042797275174691/28625000000000000000000000000000 : ℝ)*base80 + (4449270895257/1145000000000000000000000000 : ℝ)*base81 + (16391651/5000000000000000000000 : ℝ)*base90 + (16391651/5000000000000000000000 : ℝ)*base92 + (16391651/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (7353/12500 : ℝ) ≤ (33678296061907070281532222442363/57250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24873461/100000000000000 : ℝ)*(upper1) + (128249107/100000000000000 : ℝ)*(upper2) + (42782363/100000000000000 : ℝ)*(upper3) + (16771731/100000000000000 : ℝ)*(upper5) + (2918185058331463/100000000000000 : ℝ)*(major0) + (2918185058331463/100000000000000 : ℝ)*(major1) + (2918185058331463/100000000000000 : ℝ)*(major2) + (975263678920437/25000000000000 : ℝ)*(sp0) + (390103787053839/10000000000000 : ℝ)*(sp1) + (3901006029278527/100000000000000 : ℝ)*(sp2) + (957849105613571/50000000000000 : ℝ)*(sp3) + (25128893367/100000000000000 : ℝ)*(sp9) + (56970153231/100000000000000 : ℝ)*(sp10) + (828375001/10000000000000 : ℝ)*(sp12) + (957849105613571/50000000000000 : ℝ)*(f.failure) + (1950531499715879/50000000000000 : ℝ)*(f.sum) + (17336859650523/4580000000000000000000000000 : ℝ)*base66 + (703192306825723379/114500000000000000000000000000000 : ℝ)*base67 + (16074985545723379/114500000000000000000000000000000 : ℝ)*base69 + (525273884278723379/114500000000000000000000000000000 : ℝ)*base71 + (12566821348257/4580000000000000000000000000 : ℝ)*base73 + (886784132466723379/114500000000000000000000000000000 : ℝ)*base75 + (468883952663276621/114500000000000000000000000000000 : ℝ)*base78 + (323969494222276621/114500000000000000000000000000000 : ℝ)*base80 + (3303711441857/4580000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1372187/5000000000000000000000 : ℝ)*base90 + (1372187/5000000000000000000000 : ℝ)*base92 + (1372187/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (7959/10000 : ℝ) ≤ (11391610237149207209000905918443/14312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72035459/100000000000000 : ℝ)*(upper0) + (22212691/50000000000000 : ℝ)*(lower1) + (5873503/100000000000000 : ℝ)*(upper2) + (13168181/100000000000000 : ℝ)*(lower3) + (22190689/25000000000000 : ℝ)*(lower5) + (1616261014655207/50000000000000 : ℝ)*(major0) + (1616261014655207/50000000000000 : ℝ)*(major1) + (1616261014655207/50000000000000 : ℝ)*(major2) + (469353957/25000000000000 : ℝ)*(sp0) + (14661596993/100000000000000 : ℝ)*(sp1) + (2158230397137181/50000000000000 : ℝ)*(sp8) + (4316448010093197/100000000000000 : ℝ)*(sp9) + (431646267169019/10000000000000 : ℝ)*(sp10) + (2122050708066819/100000000000000 : ℝ)*(sp11) + (2122050708066819/100000000000000 : ℝ)*(f.failure) + (431646267169019/10000000000000 : ℝ)*(f.sum) + (10865027337407/2290000000000000000000000000 : ℝ)*base66 + (259934982837754269/57250000000000000000000000000000 : ℝ)*base68 + (109237322019995731/57250000000000000000000000000000 : ℝ)*base69 + (80159907925504269/57250000000000000000000000000000 : ℝ)*base72 + (12020263910153/2290000000000000000000000000 : ℝ)*base73 + (1457856226638254269/57250000000000000000000000000000 : ℝ)*base76 + (593117673000004269/57250000000000000000000000000000 : ℝ)*base78 + (560140549697754269/57250000000000000000000000000000 : ℝ)*base80 + (2909805799687/2290000000000000000000000000 : ℝ)*base82 + (69152357/10000000000000000000000 : ℝ)*base89 + (69152357/10000000000000000000000 : ℝ)*base91 + (69152357/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84111/100000 : ℝ) ≤ (-24076026077185672878524583151293/28625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13089253/12500000000000 : ℝ)*(lower0) + (85012991/100000000000000 : ℝ)*(lower2) + (8368751/100000000000000 : ℝ)*(upper3) + (1634154045633607/50000000000000 : ℝ)*(major0) + (1634154045633607/50000000000000 : ℝ)*(major1) + (1634154045633607/50000000000000 : ℝ)*(major2) + (5489004153/50000000000000 : ℝ)*(sp0) + (236752915441/100000000000000 : ℝ)*(sp5) + (86607436589/100000000000000 : ℝ)*(sp6) + (43954359489/100000000000000 : ℝ)*(sp7) + (1104774545810401/25000000000000 : ℝ)*(sp12) + (4418872408334469/100000000000000 : ℝ)*(sp13) + (110475563845333/2500000000000 : ℝ)*(sp14) + (2145499196272539/100000000000000 : ℝ)*(sp15) + (536385787658007/25000000000000 : ℝ)*(f.failure) + (441910916124991/10000000000000 : ℝ)*(f.sum) + (67679307177/2290000000000000000000000000 : ℝ)*base66 + (223788737192037069/57250000000000000000000000000000 : ℝ)*base68 + (130765541075462931/57250000000000000000000000000000 : ℝ)*base69 + (24956692887462931/57250000000000000000000000000000 : ℝ)*base71 + (89013042398787/2290000000000000000000000000 : ℝ)*base74 + (63008927013712931/57250000000000000000000000000000 : ℝ)*base75 + (463239711821462931/57250000000000000000000000000000 : ℝ)*base77 + (2032571905215287069/57250000000000000000000000000000 : ℝ)*base80 + (7784133854703/2290000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (14915279/2500000000000000000000 : ℝ)*base90 + (14915279/2500000000000000000000 : ℝ)*base92 + (14915279/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1281_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7353/12500 : ℝ) else (7959/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84111/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1281_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1281_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7353/12500 : ℝ) else (7959/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84111/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1281_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (265/64 : ℝ) ≤ p) (hpb : p ≤ (4241/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152330103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1833/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11/100 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7353/12500 : ℝ) else (7959/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84111/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1281_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1259_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:53:36.136969+00:00
-- url     : https://prove2.me/submissions/68207092-93dd-45d1-b09d-c86ed9879d60

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
theorem support_rectangle_w1259_s3_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-84378087/400000000 : ℝ)*x 0 + (1083637199/2000000000 : ℝ)*x 1 + (5241908031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84378087/400000000 : ℝ)^2113 ≤ (25648918623/200000000000 : ℝ)^1601 := by
    have hnat : (84378087 : ℕ)^2113*200000000000^1601 ≤ 25648918623^1601*400000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84378087 400000000 25648918623 200000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083637199/2000000000 : ℝ)^2113 ≤ (22269494586069/50000000000000 : ℝ)^1601 := by
    have hnat : (1083637199 : ℕ)^2113*50000000000000^1601 ≤ 22269494586069^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083637199 2000000000 22269494586069 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241908031/10000000000 : ℝ)^2113 ≤ (42636551498991/100000000000000 : ℝ)^1601 := by
    have hnat : (5241908031 : ℕ)^2113*100000000000000^1601 ≤ 42636551498991^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241908031 10000000000 42636551498991 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84378087/400000000 : ℝ), (1083637199/2000000000 : ℝ), (5241908031/10000000000 : ℝ)] ![(25648918623/200000000000 : ℝ), (22269494586069/50000000000000 : ℝ), (42636551498991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84378087/400000000 : ℝ)|^2113 ≤ (25648918623/200000000000 : ℝ)^1601
        have hw : |(-84378087/400000000 : ℝ)|=(84378087/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083637199/2000000000 : ℝ)|^2113 ≤ (22269494586069/50000000000000 : ℝ)^1601
        have hw : |(1083637199/2000000000 : ℝ)|=(1083637199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241908031/10000000000 : ℝ)|^2113 ≤ (42636551498991/100000000000000 : ℝ)^1601
        have hw : |(5241908031/10000000000 : ℝ)|=(5241908031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s3_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351117089/10000000000 : ℝ)*x 0 + (-1099675417/5000000000 : ℝ)*x 1 + (1310477033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351117089/10000000000 : ℝ)^2113 ≤ (1369149834047/3125000000000 : ℝ)^1601 := by
    have hnat : (5351117089 : ℕ)^2113*3125000000000^1601 ≤ 1369149834047^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351117089 10000000000 1369149834047 3125000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099675417/5000000000 : ℝ)^2113 ≤ (13550652717861/100000000000000 : ℝ)^1601 := by
    have hnat : (1099675417 : ℕ)^2113*100000000000000^1601 ≤ 13550652717861^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099675417 5000000000 13550652717861 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310477033/2500000000 : ℝ)^2113 ≤ (42636552583223/100000000000000 : ℝ)^1601 := by
    have hnat : (1310477033 : ℕ)^2113*100000000000000^1601 ≤ 42636552583223^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310477033 2500000000 42636552583223 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351117089/10000000000 : ℝ), (-1099675417/5000000000 : ℝ), (1310477033/2500000000 : ℝ)] ![(1369149834047/3125000000000 : ℝ), (13550652717861/100000000000000 : ℝ), (42636552583223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351117089/10000000000 : ℝ)|^2113 ≤ (1369149834047/3125000000000 : ℝ)^1601
        have hw : |(5351117089/10000000000 : ℝ)|=(5351117089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1099675417/5000000000 : ℝ)|^2113 ≤ (13550652717861/100000000000000 : ℝ)^1601
        have hw : |(-1099675417/5000000000 : ℝ)|=(1099675417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310477033/2500000000 : ℝ)|^2113 ≤ (42636552583223/100000000000000 : ℝ)^1601
        have hw : |(1310477033/2500000000 : ℝ)|=(1310477033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s3_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675558531/5000000000 : ℝ)*x 0 + (40952411/78125000 : ℝ)*x 1 + (-2199350241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675558531/5000000000 : ℝ)^2113 ≤ (21906397198871/50000000000000 : ℝ)^1601 := by
    have hnat : (2675558531 : ℕ)^2113*50000000000000^1601 ≤ 21906397198871^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675558531 5000000000 21906397198871 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40952411/78125000 : ℝ)^2113 ≤ (10659139423267/25000000000000 : ℝ)^1601 := by
    have hnat : (40952411 : ℕ)^2113*25000000000000^1601 ≤ 10659139423267^1601*78125000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40952411 78125000 10659139423267 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2199350241/10000000000 : ℝ)^2113 ≤ (6775323947923/50000000000000 : ℝ)^1601 := by
    have hnat : (2199350241 : ℕ)^2113*50000000000000^1601 ≤ 6775323947923^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199350241 10000000000 6775323947923 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675558531/5000000000 : ℝ), (40952411/78125000 : ℝ), (-2199350241/10000000000 : ℝ)] ![(21906397198871/50000000000000 : ℝ), (10659139423267/25000000000000 : ℝ), (6775323947923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675558531/5000000000 : ℝ)|^2113 ≤ (21906397198871/50000000000000 : ℝ)^1601
        have hw : |(2675558531/5000000000 : ℝ)|=(2675558531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40952411/78125000 : ℝ)|^2113 ≤ (10659139423267/25000000000000 : ℝ)^1601
        have hw : |(40952411/78125000 : ℝ)|=(40952411/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2199350241/10000000000 : ℝ)|^2113 ≤ (6775323947923/50000000000000 : ℝ)^1601
        have hw : |(-2199350241/10000000000 : ℝ)|=(2199350241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s3_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1086707231/2500000000 : ℝ)*x 0 + (2085513841/5000000000 : ℝ)*x 1 + (1132448093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086707231/2500000000 : ℝ)^2113 ≤ (33301215370759/100000000000000 : ℝ)^1601 := by
    have hnat : (1086707231 : ℕ)^2113*100000000000000^1601 ≤ 33301215370759^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086707231 2500000000 33301215370759 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085513841/5000000000 : ℝ)^2113 ≤ (3941910615061/12500000000000 : ℝ)^1601 := by
    have hnat : (2085513841 : ℕ)^2113*12500000000000^1601 ≤ 3941910615061^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085513841 5000000000 3941910615061 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132448093/2500000000 : ℝ)^2113 ≤ (7032699937967/20000000000000 : ℝ)^1601 := by
    have hnat : (1132448093 : ℕ)^2113*20000000000000^1601 ≤ 7032699937967^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132448093 2500000000 7032699937967 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086707231/2500000000 : ℝ), (2085513841/5000000000 : ℝ), (1132448093/2500000000 : ℝ)] ![(33301215370759/100000000000000 : ℝ), (3941910615061/12500000000000 : ℝ), (7032699937967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086707231/2500000000 : ℝ)|^2113 ≤ (33301215370759/100000000000000 : ℝ)^1601
        have hw : |(1086707231/2500000000 : ℝ)|=(1086707231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085513841/5000000000 : ℝ)|^2113 ≤ (3941910615061/12500000000000 : ℝ)^1601
        have hw : |(2085513841/5000000000 : ℝ)|=(2085513841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132448093/2500000000 : ℝ)|^2113 ≤ (7032699937967/20000000000000 : ℝ)^1601
        have hw : |(1132448093/2500000000 : ℝ)|=(1132448093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s3_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-527366557/2500000000 : ℝ)*x 0 + (655317749/1250000000 : ℝ)*x 1 + (5417548287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527366557/2500000000 : ℝ)^2113 ≤ (641228603471/5000000000000 : ℝ)^1601 := by
    have hnat : (527366557 : ℕ)^2113*5000000000000^1601 ≤ 641228603471^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527366557 2500000000 641228603471 5000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655317749/1250000000 : ℝ)^2113 ≤ (42643357182977/100000000000000 : ℝ)^1601 := by
    have hnat : (655317749 : ℕ)^2113*100000000000000^1601 ≤ 42643357182977^1601*1250000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655317749 1250000000 42643357182977 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417548287/10000000000 : ℝ)^2113 ≤ (890641414603/2000000000000 : ℝ)^1601 := by
    have hnat : (5417548287 : ℕ)^2113*2000000000000^1601 ≤ 890641414603^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417548287 10000000000 890641414603 2000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527366557/2500000000 : ℝ), (655317749/1250000000 : ℝ), (5417548287/10000000000 : ℝ)] ![(641228603471/5000000000000 : ℝ), (42643357182977/100000000000000 : ℝ), (890641414603/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527366557/2500000000 : ℝ)|^2113 ≤ (641228603471/5000000000000 : ℝ)^1601
        have hw : |(-527366557/2500000000 : ℝ)|=(527366557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655317749/1250000000 : ℝ)|^2113 ≤ (42643357182977/100000000000000 : ℝ)^1601
        have hw : |(655317749/1250000000 : ℝ)|=(655317749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417548287/10000000000 : ℝ)|^2113 ≤ (890641414603/2000000000000 : ℝ)^1601
        have hw : |(5417548287/10000000000 : ℝ)|=(5417548287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s3_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530609407/1000000000 : ℝ)*x 0 + (-2023710037/10000000000 : ℝ)*x 1 + (2708774063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530609407/1000000000 : ℝ)^2113 ≤ (10831733018319/25000000000000 : ℝ)^1601 := by
    have hnat : (530609407 : ℕ)^2113*25000000000000^1601 ≤ 10831733018319^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530609407 1000000000 10831733018319 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2023710037/10000000000 : ℝ)^2113 ≤ (12140998927281/100000000000000 : ℝ)^1601 := by
    have hnat : (2023710037 : ℕ)^2113*100000000000000^1601 ≤ 12140998927281^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023710037 10000000000 12140998927281 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708774063/5000000000 : ℝ)^2113 ≤ (44532068983507/100000000000000 : ℝ)^1601 := by
    have hnat : (2708774063 : ℕ)^2113*100000000000000^1601 ≤ 44532068983507^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708774063 5000000000 44532068983507 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530609407/1000000000 : ℝ), (-2023710037/10000000000 : ℝ), (2708774063/5000000000 : ℝ)] ![(10831733018319/25000000000000 : ℝ), (12140998927281/100000000000000 : ℝ), (44532068983507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530609407/1000000000 : ℝ)|^2113 ≤ (10831733018319/25000000000000 : ℝ)^1601
        have hw : |(530609407/1000000000 : ℝ)|=(530609407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2023710037/10000000000 : ℝ)|^2113 ≤ (12140998927281/100000000000000 : ℝ)^1601
        have hw : |(-2023710037/10000000000 : ℝ)|=(2023710037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708774063/5000000000 : ℝ)|^2113 ≤ (44532068983507/100000000000000 : ℝ)^1601
        have hw : |(2708774063/5000000000 : ℝ)|=(2708774063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s3_6 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2653046709/5000000000 : ℝ)*x 0 + (216701943/400000000 : ℝ)*x 1 + (-2023710309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653046709/5000000000 : ℝ)^2113 ≤ (43326925046781/100000000000000 : ℝ)^1601 := by
    have hnat : (2653046709 : ℕ)^2113*100000000000000^1601 ≤ 43326925046781^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653046709 5000000000 43326925046781 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216701943/400000000 : ℝ)^2113 ≤ (2226603692729/5000000000000 : ℝ)^1601 := by
    have hnat : (216701943 : ℕ)^2113*5000000000000^1601 ≤ 2226603692729^1601*400000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216701943 400000000 2226603692729 5000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023710309/10000000000 : ℝ)^2113 ≤ (12141001080971/100000000000000 : ℝ)^1601 := by
    have hnat : (2023710309 : ℕ)^2113*100000000000000^1601 ≤ 12141001080971^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023710309 10000000000 12141001080971 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653046709/5000000000 : ℝ), (216701943/400000000 : ℝ), (-2023710309/10000000000 : ℝ)] ![(43326925046781/100000000000000 : ℝ), (2226603692729/5000000000000 : ℝ), (12141001080971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653046709/5000000000 : ℝ)|^2113 ≤ (43326925046781/100000000000000 : ℝ)^1601
        have hw : |(2653046709/5000000000 : ℝ)|=(2653046709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216701943/400000000 : ℝ)|^2113 ≤ (2226603692729/5000000000000 : ℝ)^1601
        have hw : |(216701943/400000000 : ℝ)|=(216701943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2023710309/10000000000 : ℝ)|^2113 ≤ (12141001080971/100000000000000 : ℝ)^1601
        have hw : |(-2023710309/10000000000 : ℝ)|=(2023710309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s3_7 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2173428483/5000000000 : ℝ)*x 0 + (2264250673/5000000000 : ℝ)*x 1 + (4172324689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173428483/5000000000 : ℝ)^2113 ≤ (2081343681547/6250000000000 : ℝ)^1601 := by
    have hnat : (2173428483 : ℕ)^2113*6250000000000^1601 ≤ 2081343681547^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173428483 5000000000 2081343681547 6250000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264250673/5000000000 : ℝ)^2113 ≤ (17575136713389/50000000000000 : ℝ)^1601 := by
    have hnat : (2264250673 : ℕ)^2113*50000000000000^1601 ≤ 17575136713389^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264250673 5000000000 17575136713389 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172324689/10000000000 : ℝ)^2113 ≤ (15774113823347/50000000000000 : ℝ)^1601 := by
    have hnat : (4172324689 : ℕ)^2113*50000000000000^1601 ≤ 15774113823347^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172324689 10000000000 15774113823347 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173428483/5000000000 : ℝ), (2264250673/5000000000 : ℝ), (4172324689/10000000000 : ℝ)] ![(2081343681547/6250000000000 : ℝ), (17575136713389/50000000000000 : ℝ), (15774113823347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173428483/5000000000 : ℝ)|^2113 ≤ (2081343681547/6250000000000 : ℝ)^1601
        have hw : |(2173428483/5000000000 : ℝ)|=(2173428483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264250673/5000000000 : ℝ)|^2113 ≤ (17575136713389/50000000000000 : ℝ)^1601
        have hw : |(2264250673/5000000000 : ℝ)|=(2264250673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172324689/10000000000 : ℝ)|^2113 ≤ (15774113823347/50000000000000 : ℝ)^1601
        have hw : |(4172324689/10000000000 : ℝ)|=(4172324689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (299/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5477/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7343/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (299/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (299/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (299/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (299/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (299/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (299/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (299/3125 : ℝ) ^ (8451/2048 : ℝ) ≤ (1557164102570149/25000000000000000000 : ℝ) := by
    have hpowers : (299/3125 : ℝ)^8451 ≤ (1557164102570149/25000000000000000000 : ℝ)^2048 := by
      have hnat : (299 : ℕ)^8451*25000000000000000000^2048 ≤ 1557164102570149^2048*3125^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        299 3125 1557164102570149 25000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (299/3125 : ℝ)) (X := (1557164102570149/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16179/100000 : ℝ) ^ (8451/2048 : ℝ) ≤ (27210523772476533/50000000000000000000 : ℝ) := by
    have hpowers : (16179/100000 : ℝ)^8451 ≤ (27210523772476533/50000000000000000000 : ℝ)^2048 := by
      have hnat : (16179 : ℕ)^8451*50000000000000000000^2048 ≤ 27210523772476533^2048*100000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16179 100000 27210523772476533 50000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16179/100000 : ℝ)) (X := (27210523772476533/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501557164102570149/12500000000000000000 : ℝ) ≤ (2500075468502991/2500000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (12501557164102570149/12500000000000000000 : ℝ)^2048 ≤ (2500075468502991/2500000000000000 : ℝ)^8451 := by
      have hnat : (12501557164102570149 : ℕ)^2048*2500000000000000^8451 ≤ 2500075468502991^8451*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501557164102570149 12500000000000000000 2500075468502991 2500000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500075468502991/2500000000000000 : ℝ)) (X := (12501557164102570149/12500000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50030324851977616831/50000000000000000000 : ℝ) ≤ (200029388726833/200000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50030324851977616831/50000000000000000000 : ℝ)^2048 ≤ (200029388726833/200000000000000 : ℝ)^8451 := by
      have hnat : (50030324851977616831 : ℕ)^2048*200000000000000^8451 ≤ 200029388726833^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030324851977616831 50000000000000000000 200029388726833 200000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200029388726833/200000000000000 : ℝ)) (X := (50030324851977616831/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25027210523772476533/25000000000000000000 : ℝ) ≤ (1250329624833917/1250000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (25027210523772476533/25000000000000000000 : ℝ)^2048 ≤ (1250329624833917/1250000000000000 : ℝ)^8451 := by
      have hnat : (25027210523772476533 : ℕ)^2048*1250000000000000^8451 ≤ 1250329624833917^8451*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25027210523772476533 25000000000000000000 1250329624833917 1250000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250329624833917/1250000000000000 : ℝ)) (X := (25027210523772476533/25000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1557164102570149/25000000000000000000 : ℝ) ≤ ((16522413304088055677/16527500000000000000 : ℝ)+2*(583781164843/330550000000000 : ℝ)*(299/3125 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (16522413304088055677/16527500000000000000 : ℝ)+2*(583781164843/330550000000000 : ℝ)*(299/3125 : ℝ)=(2500075468502991/2500000000000000 : ℝ) by norm_num, show 1+2*(1557164102570149/25000000000000000000 : ℝ)=(12501557164102570149/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27210523772476533/50000000000000000000 : ℝ)+(1557164102570149/25000000000000000000 : ℝ) ≤ ((16522413304088055677/16527500000000000000 : ℝ)+(583781164843/330550000000000 : ℝ)*((16179/100000 : ℝ)+(299/3125 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (16522413304088055677/16527500000000000000 : ℝ)+(583781164843/330550000000000 : ℝ)*((16179/100000 : ℝ)+(299/3125 : ℝ))=(200029388726833/200000000000000 : ℝ) by norm_num, show 1+(27210523772476533/50000000000000000000 : ℝ)+(1557164102570149/25000000000000000000 : ℝ)=(50030324851977616831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27210523772476533/50000000000000000000 : ℝ) ≤ ((16522413304088055677/16527500000000000000 : ℝ)+2*(583781164843/330550000000000 : ℝ)*(16179/100000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (16522413304088055677/16527500000000000000 : ℝ)+2*(583781164843/330550000000000 : ℝ)*(16179/100000 : ℝ)=(1250329624833917/1250000000000000 : ℝ) by norm_num, show 1+2*(27210523772476533/50000000000000000000 : ℝ)=(25027210523772476533/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16522413304088055677/16527500000000000000 : ℝ)*(X 1 0+X 2 0)+(583781164843/330550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (299/3125 : ℝ)) (hi := (16179/100000 : ℝ)) (c := (16522413304088055677/16527500000000000000 : ℝ)) (alpha := (583781164843/330550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16522413304088055677/16527500000000000000 : ℝ)*(X 0 1+X 2 1)+(583781164843/330550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (299/3125 : ℝ)) (hi := (16179/100000 : ℝ)) (c := (16522413304088055677/16527500000000000000 : ℝ)) (alpha := (583781164843/330550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16522413304088055677/16527500000000000000 : ℝ)*(X 0 2+X 1 2)+(583781164843/330550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (299/3125 : ℝ)) (hi := (16179/100000 : ℝ)) (c := (16522413304088055677/16527500000000000000 : ℝ)) (alpha := (583781164843/330550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-84378087/400000000 : ℝ)*X 0 0+(1083637199/2000000000 : ℝ)*X 0 1+(5241908031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351117089/10000000000 : ℝ)*X 1 0+(-1099675417/5000000000 : ℝ)*X 1 1+(1310477033/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675558531/5000000000 : ℝ)*X 2 0+(40952411/78125000 : ℝ)*X 2 1+(-2199350241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086707231/2500000000 : ℝ)*X 0 0+(2085513841/5000000000 : ℝ)*X 0 1+(1132448093/2500000000 : ℝ)*X 0 2+(1086707231/2500000000 : ℝ)*X 1 0+(2085513841/5000000000 : ℝ)*X 1 1+(1132448093/2500000000 : ℝ)*X 1 2+(1086707231/2500000000 : ℝ)*X 2 0+(2085513841/5000000000 : ℝ)*X 2 1+(1132448093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-527366557/2500000000 : ℝ)*X 0 0+(655317749/1250000000 : ℝ)*X 0 1+(5417548287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530609407/1000000000 : ℝ)*X 1 0+(-2023710037/10000000000 : ℝ)*X 1 1+(2708774063/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2653046709/5000000000 : ℝ)*X 2 0+(216701943/400000000 : ℝ)*X 2 1+(-2023710309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173428483/5000000000 : ℝ)*X 0 0+(2264250673/5000000000 : ℝ)*X 0 1+(4172324689/10000000000 : ℝ)*X 0 2+(2173428483/5000000000 : ℝ)*X 1 0+(2264250673/5000000000 : ℝ)*X 1 1+(4172324689/10000000000 : ℝ)*X 1 2+(2173428483/5000000000 : ℝ)*X 2 0+(2264250673/5000000000 : ℝ)*X 2 1+(4172324689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15003246978967116391779/1652750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1220942183/100000000000000 : ℝ)*(base19) + (385261737/50000000000000 : ℝ)*(base23) + (256640061/100000000000000 : ℝ)*(lower2) + (1137417/1250000000000 : ℝ)*(upper5) + (423015156449587/10000000000000 : ℝ)*(major0) + (423015156449587/10000000000000 : ℝ)*(major1) + (423015156449587/10000000000000 : ℝ)*(major2) + (5672892853354737/100000000000000 : ℝ)*(sp0) + (709115996233391/12500000000000 : ℝ)*(sp1) + (2836467645348179/50000000000000 : ℝ)*(sp2) + (1393677067253839/50000000000000 : ℝ)*(sp3) + (8641573019/20000000000000 : ℝ)*(sp4) + (171760263/2500000000000 : ℝ)*(sp5) + (3157668161/25000000000000 : ℝ)*(sp7) + (1393683382590161/50000000000000 : ℝ)*(f.failure) + (709117007652479/12500000000000 : ℝ)*(f.sum) + (44862260447413/6611000000000000000000000000 : ℝ)*base65 + (360880071746419601/165275000000000000000000000000000 : ℝ)*base68 + (595219572105394601/165275000000000000000000000000000 : ℝ)*base70 + (1716182982145505399/165275000000000000000000000000000 : ℝ)*base71 + (2143923790309/413187500000000000000000000 : ℝ)*base74 + (1853687323026005399/165275000000000000000000000000000 : ℝ)*base75 + (1063295185200594601/165275000000000000000000000000000 : ℝ)*base78 + (1072785997938605399/165275000000000000000000000000000 : ℝ)*base79 + (3283674756877/661100000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8723/500000000000000000000 : ℝ)*base90 + (8723/500000000000000000000 : ℝ)*base92 + (8723/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (812276970094919956440240747/103296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3287245361/100000000000000 : ℝ)*(base19) + (1294471991/50000000000000 : ℝ)*(base23) + (102478353/100000000000000 : ℝ)*(upper3) + (92552617/100000000000000 : ℝ)*(lower4) + (126209751/25000000000000 : ℝ)*(upper5) + (532604544663369/12500000000000 : ℝ)*(major0) + (532604544663369/12500000000000 : ℝ)*(major1) + (532604544663369/12500000000000 : ℝ)*(major2) + (37345970859/50000000000000 : ℝ)*(sp1) + (6823249689/12500000000000 : ℝ)*(sp2) + (178565206487621/3125000000000 : ℝ)*(sp4) + (2857004314208397/50000000000000 : ℝ)*(sp5) + (2857014716331189/50000000000000 : ℝ)*(sp6) + (2807585844892717/100000000000000 : ℝ)*(sp7) + (2807585844892717/100000000000000 : ℝ)*(f.failure) + (178565206487621/3125000000000 : ℝ)*(f.sum) + (11227939839871/16527500000000000000000000000 : ℝ)*base65 + (1235821741536308313/206593750000000000000000000000000 : ℝ)*base67 + (1092369823802527063/206593750000000000000000000000000 : ℝ)*base69 + (1230748419230745813/206593750000000000000000000000000 : ℝ)*base71 + (7827323745503/8263750000000000000000000000 : ℝ)*base73 + (842864164530152063/206593750000000000000000000000000 : ℝ)*base75 + (1445368901245558313/206593750000000000000000000000000 : ℝ)*base77 + (1521709331058754187/206593750000000000000000000000000 : ℝ)*base80 + (55211900664973/33055000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1348569/1000000000000000000000 : ℝ)*base89 + (1348569/1000000000000000000000 : ℝ)*base91 + (1348569/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1259_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (299/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1259_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1259_s4_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-105582011/500000000 : ℝ)*x 0 + (2698410463/5000000000 : ℝ)*x 1 + (5261838851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105582011/500000000 : ℝ)^2113 ≤ (513680742203/4000000000000 : ℝ)^1601 := by
    have hnat : (105582011 : ℕ)^2113*4000000000000^1601 ≤ 513680742203^1601*500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105582011 500000000 513680742203 4000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698410463/5000000000 : ℝ)^2113 ≤ (11076835800593/25000000000000 : ℝ)^1601 := by
    have hnat : (2698410463 : ℕ)^2113*25000000000000^1601 ≤ 11076835800593^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698410463 5000000000 11076835800593 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261838851/10000000000 : ℝ)^2113 ≤ (42850638223819/100000000000000 : ℝ)^1601 := by
    have hnat : (5261838851 : ℕ)^2113*100000000000000^1601 ≤ 42850638223819^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261838851 10000000000 42850638223819 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105582011/500000000 : ℝ), (2698410463/5000000000 : ℝ), (5261838851/10000000000 : ℝ)] ![(513680742203/4000000000000 : ℝ), (11076835800593/25000000000000 : ℝ), (42850638223819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105582011/500000000 : ℝ)|^2113 ≤ (513680742203/4000000000000 : ℝ)^1601
        have hw : |(-105582011/500000000 : ℝ)|=(105582011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698410463/5000000000 : ℝ)|^2113 ≤ (11076835800593/25000000000000 : ℝ)^1601
        have hw : |(2698410463/5000000000 : ℝ)|=(2698410463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261838851/10000000000 : ℝ)|^2113 ≤ (42850638223819/100000000000000 : ℝ)^1601
        have hw : |(5261838851/10000000000 : ℝ)|=(5261838851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s4_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672861467/5000000000 : ℝ)*x 0 + (-2180163321/10000000000 : ℝ)*x 1 + (328864931/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672861467/5000000000 : ℝ)^2113 ≤ (43754514887807/100000000000000 : ℝ)^1601 := by
    have hnat : (2672861467 : ℕ)^2113*100000000000000^1601 ≤ 43754514887807^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672861467 5000000000 43754514887807 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180163321/10000000000 : ℝ)^2113 ≤ (13394846391149/100000000000000 : ℝ)^1601 := by
    have hnat : (2180163321 : ℕ)^2113*100000000000000^1601 ≤ 13394846391149^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180163321 10000000000 13394846391149 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328864931/625000000 : ℝ)^2113 ≤ (42850638707479/100000000000000 : ℝ)^1601 := by
    have hnat : (328864931 : ℕ)^2113*100000000000000^1601 ≤ 42850638707479^1601*625000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328864931 625000000 42850638707479 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672861467/5000000000 : ℝ), (-2180163321/10000000000 : ℝ), (328864931/625000000 : ℝ)] ![(43754514887807/100000000000000 : ℝ), (13394846391149/100000000000000 : ℝ), (42850638707479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672861467/5000000000 : ℝ)|^2113 ≤ (43754514887807/100000000000000 : ℝ)^1601
        have hw : |(2672861467/5000000000 : ℝ)|=(2672861467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180163321/10000000000 : ℝ)|^2113 ≤ (13394846391149/100000000000000 : ℝ)^1601
        have hw : |(-2180163321/10000000000 : ℝ)|=(2180163321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328864931/625000000 : ℝ)|^2113 ≤ (42850638707479/100000000000000 : ℝ)^1601
        have hw : |(328864931/625000000 : ℝ)|=(328864931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s4_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345723021/10000000000 : ℝ)*x 0 + (210473553/400000000 : ℝ)*x 1 + (-21801633/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345723021/10000000000 : ℝ)^2113 ≤ (350036126621/800000000000 : ℝ)^1601 := by
    have hnat : (5345723021 : ℕ)^2113*800000000000^1601 ≤ 350036126621^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345723021 10000000000 350036126621 800000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210473553/400000000 : ℝ)^2113 ≤ (4285063794437/10000000000000 : ℝ)^1601 := by
    have hnat : (210473553 : ℕ)^2113*10000000000000^1601 ≤ 4285063794437^1601*400000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210473553 400000000 4285063794437 10000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21801633/100000000 : ℝ)^2113 ≤ (209294472201/1562500000000 : ℝ)^1601 := by
    have hnat : (21801633 : ℕ)^2113*1562500000000^1601 ≤ 209294472201^1601*100000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21801633 100000000 209294472201 1562500000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345723021/10000000000 : ℝ), (210473553/400000000 : ℝ), (-21801633/100000000 : ℝ)] ![(350036126621/800000000000 : ℝ), (4285063794437/10000000000000 : ℝ), (209294472201/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345723021/10000000000 : ℝ)|^2113 ≤ (350036126621/800000000000 : ℝ)^1601
        have hw : |(5345723021/10000000000 : ℝ)|=(5345723021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210473553/400000000 : ℝ)|^2113 ≤ (4285063794437/10000000000000 : ℝ)^1601
        have hw : |(210473553/400000000 : ℝ)|=(210473553/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21801633/100000000 : ℝ)|^2113 ≤ (209294472201/1562500000000 : ℝ)^1601
        have hw : |(-21801633/100000000 : ℝ)|=(21801633/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s4_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (27175889/62500000 : ℝ)*x 0 + (1053220747/2500000000 : ℝ)*x 1 + (448760269/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27175889/62500000 : ℝ)^2113 ≤ (33314494998941/100000000000000 : ℝ)^1601 := by
    have hnat : (27175889 : ℕ)^2113*100000000000000^1601 ≤ 33314494998941^1601*62500000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27175889 62500000 33314494998941 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053220747/2500000000 : ℝ)^2113 ≤ (31953603438741/100000000000000 : ℝ)^1601 := by
    have hnat : (1053220747 : ℕ)^2113*100000000000000^1601 ≤ 31953603438741^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053220747 2500000000 31953603438741 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448760269/1000000000 : ℝ)^2113 ≤ (17365950771433/50000000000000 : ℝ)^1601 := by
    have hnat : (448760269 : ℕ)^2113*50000000000000^1601 ≤ 17365950771433^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448760269 1000000000 17365950771433 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27175889/62500000 : ℝ), (1053220747/2500000000 : ℝ), (448760269/1000000000 : ℝ)] ![(33314494998941/100000000000000 : ℝ), (31953603438741/100000000000000 : ℝ), (17365950771433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27175889/62500000 : ℝ)|^2113 ≤ (33314494998941/100000000000000 : ℝ)^1601
        have hw : |(27175889/62500000 : ℝ)|=(27175889/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053220747/2500000000 : ℝ)|^2113 ≤ (31953603438741/100000000000000 : ℝ)^1601
        have hw : |(1053220747/2500000000 : ℝ)|=(1053220747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448760269/1000000000 : ℝ)|^2113 ≤ (17365950771433/50000000000000 : ℝ)^1601
        have hw : |(448760269/1000000000 : ℝ)|=(448760269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s4_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-527911499/2500000000 : ℝ)*x 0 + (2631105619/5000000000 : ℝ)*x 1 + (5396447257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527911499/2500000000 : ℝ)^2113 ≤ (642103245783/5000000000000 : ℝ)^1601 := by
    have hnat : (527911499 : ℕ)^2113*5000000000000^1601 ≤ 642103245783^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527911499 2500000000 642103245783 5000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631105619/5000000000 : ℝ)^2113 ≤ (10713660171743/25000000000000 : ℝ)^1601 := by
    have hnat : (2631105619 : ℕ)^2113*25000000000000^1601 ≤ 10713660171743^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631105619 5000000000 10713660171743 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396447257/10000000000 : ℝ)^2113 ≤ (11075823596389/25000000000000 : ℝ)^1601 := by
    have hnat : (5396447257 : ℕ)^2113*25000000000000^1601 ≤ 11075823596389^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396447257 10000000000 11075823596389 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527911499/2500000000 : ℝ), (2631105619/5000000000 : ℝ), (5396447257/10000000000 : ℝ)] ![(642103245783/5000000000000 : ℝ), (10713660171743/25000000000000 : ℝ), (11075823596389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527911499/2500000000 : ℝ)|^2113 ≤ (642103245783/5000000000000 : ℝ)^1601
        have hw : |(-527911499/2500000000 : ℝ)|=(527911499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631105619/5000000000 : ℝ)|^2113 ≤ (10713660171743/25000000000000 : ℝ)^1601
        have hw : |(2631105619/5000000000 : ℝ)|=(2631105619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396447257/10000000000 : ℝ)|^2113 ≤ (11075823596389/25000000000000 : ℝ)^1601
        have hw : |(5396447257/10000000000 : ℝ)|=(5396447257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s4_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311244147/10000000000 : ℝ)*x 0 + (-2045554877/10000000000 : ℝ)*x 1 + (5396447227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311244147/10000000000 : ℝ)^2113 ≤ (21691221102783/50000000000000 : ℝ)^1601 := by
    have hnat : (5311244147 : ℕ)^2113*50000000000000^1601 ≤ 21691221102783^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311244147 10000000000 21691221102783 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045554877/10000000000 : ℝ)^2113 ≤ (492570548519/4000000000000 : ℝ)^1601 := by
    have hnat : (2045554877 : ℕ)^2113*4000000000000^1601 ≤ 492570548519^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045554877 10000000000 492570548519 4000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396447227/10000000000 : ℝ)^2113 ≤ (44303294060501/100000000000000 : ℝ)^1601 := by
    have hnat : (5396447227 : ℕ)^2113*100000000000000^1601 ≤ 44303294060501^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396447227 10000000000 44303294060501 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311244147/10000000000 : ℝ), (-2045554877/10000000000 : ℝ), (5396447227/10000000000 : ℝ)] ![(21691221102783/50000000000000 : ℝ), (492570548519/4000000000000 : ℝ), (44303294060501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311244147/10000000000 : ℝ)|^2113 ≤ (21691221102783/50000000000000 : ℝ)^1601
        have hw : |(5311244147/10000000000 : ℝ)|=(5311244147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045554877/10000000000 : ℝ)|^2113 ≤ (492570548519/4000000000000 : ℝ)^1601
        have hw : |(-2045554877/10000000000 : ℝ)|=(2045554877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396447227/10000000000 : ℝ)|^2113 ≤ (44303294060501/100000000000000 : ℝ)^1601
        have hw : |(5396447227/10000000000 : ℝ)|=(5396447227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s4_6 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311243951/10000000000 : ℝ)*x 0 + (2698223693/5000000000 : ℝ)*x 1 + (-2045554927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311243951/10000000000 : ℝ)^2113 ≤ (43382440092651/100000000000000 : ℝ)^1601 := by
    have hnat : (5311243951 : ℕ)^2113*100000000000000^1601 ≤ 43382440092651^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311243951 10000000000 43382440092651 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698223693/5000000000 : ℝ)^2113 ≤ (8860659156659/20000000000000 : ℝ)^1601 := by
    have hnat : (2698223693 : ℕ)^2113*20000000000000^1601 ≤ 8860659156659^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698223693 5000000000 8860659156659 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045554927/10000000000 : ℝ)^2113 ≤ (2462852822047/20000000000000 : ℝ)^1601 := by
    have hnat : (2045554927 : ℕ)^2113*20000000000000^1601 ≤ 2462852822047^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045554927 10000000000 2462852822047 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311243951/10000000000 : ℝ), (2698223693/5000000000 : ℝ), (-2045554927/10000000000 : ℝ)] ![(43382440092651/100000000000000 : ℝ), (8860659156659/20000000000000 : ℝ), (2462852822047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311243951/10000000000 : ℝ)|^2113 ≤ (43382440092651/100000000000000 : ℝ)^1601
        have hw : |(5311243951/10000000000 : ℝ)|=(5311243951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698223693/5000000000 : ℝ)|^2113 ≤ (8860659156659/20000000000000 : ℝ)^1601
        have hw : |(2698223693/5000000000 : ℝ)|=(2698223693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045554927/10000000000 : ℝ)|^2113 ≤ (2462852822047/20000000000000 : ℝ)^1601
        have hw : |(-2045554927/10000000000 : ℝ)|=(2045554927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s4_7 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (543519287/1250000000 : ℝ)*x 0 + (897369051/2000000000 : ℝ)*x 1 + (210682183/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543519287/1250000000 : ℝ)^2113 ≤ (16657308454717/50000000000000 : ℝ)^1601 := by
    have hnat : (543519287 : ℕ)^2113*50000000000000^1601 ≤ 16657308454717^1601*1250000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543519287 1250000000 16657308454717 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897369051/2000000000 : ℝ)^2113 ≤ (3472416483899/10000000000000 : ℝ)^1601 := by
    have hnat : (897369051 : ℕ)^2113*10000000000000^1601 ≤ 3472416483899^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897369051 2000000000 3472416483899 10000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210682183/500000000 : ℝ)^2113 ≤ (15980609120041/50000000000000 : ℝ)^1601 := by
    have hnat : (210682183 : ℕ)^2113*50000000000000^1601 ≤ 15980609120041^1601*500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210682183 500000000 15980609120041 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543519287/1250000000 : ℝ), (897369051/2000000000 : ℝ), (210682183/500000000 : ℝ)] ![(16657308454717/50000000000000 : ℝ), (3472416483899/10000000000000 : ℝ), (15980609120041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543519287/1250000000 : ℝ)|^2113 ≤ (16657308454717/50000000000000 : ℝ)^1601
        have hw : |(543519287/1250000000 : ℝ)|=(543519287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897369051/2000000000 : ℝ)|^2113 ≤ (3472416483899/10000000000000 : ℝ)^1601
        have hw : |(897369051/2000000000 : ℝ)|=(897369051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210682183/500000000 : ℝ)|^2113 ≤ (15980609120041/50000000000000 : ℝ)^1601
        have hw : |(210682183/500000000 : ℝ)|=(210682183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11379/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5477/50000 : ℝ) ^ (8451/2048 : ℝ) ≤ (10885055871854393/100000000000000000000 : ℝ) := by
    have hpowers : (5477/50000 : ℝ)^8451 ≤ (10885055871854393/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5477 : ℕ)^8451*100000000000000000000^2048 ≤ 10885055871854393^2048*50000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5477 50000 10885055871854393 100000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5477/50000 : ℝ)) (X := (10885055871854393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7343/50000 : ℝ) ^ (8451/2048 : ℝ) ≤ (1824847950547821/5000000000000000000 : ℝ) := by
    have hpowers : (7343/50000 : ℝ)^8451 ≤ (1824847950547821/5000000000000000000 : ℝ)^2048 := by
      have hnat : (7343 : ℕ)^8451*5000000000000000000^2048 ≤ 1824847950547821^2048*50000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7343 50000 1824847950547821 5000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7343/50000 : ℝ)) (X := (1824847950547821/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010885055871854393/50000000000000000000 : ℝ) ≤ (10000527529431953/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50010885055871854393/50000000000000000000 : ℝ)^2048 ≤ (10000527529431953/10000000000000000 : ℝ)^8451 := by
      have hnat : (50010885055871854393 : ℕ)^2048*10000000000000000^8451 ≤ 10000527529431953^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010885055871854393 50000000000000000000 10000527529431953 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000527529431953/10000000000000000 : ℝ)) (X := (50010885055871854393/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047382014882810813/100000000000000000000 : ℝ) ≤ (10001148041097487/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (100047382014882810813/100000000000000000000 : ℝ)^2048 ≤ (10001148041097487/10000000000000000 : ℝ)^8451 := by
      have hnat : (100047382014882810813 : ℕ)^2048*10000000000000000^8451 ≤ 10001148041097487^8451*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047382014882810813 100000000000000000000 10001148041097487 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001148041097487/10000000000000000 : ℝ)) (X := (100047382014882810813/100000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501824847950547821/2500000000000000000 : ℝ) ≤ (10001768552763021/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (2501824847950547821/2500000000000000000 : ℝ)^2048 ≤ (10001768552763021/10000000000000000 : ℝ)^8451 := by
      have hnat : (2501824847950547821 : ℕ)^2048*10000000000000000^8451 ≤ 10001768552763021^8451*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501824847950547821 2500000000000000000 10001768552763021 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001768552763021/10000000000000000 : ℝ)) (X := (2501824847950547821/2500000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10885055871854393/100000000000000000000 : ℝ) ≤ ((9327093642567882431/9330000000000000000 : ℝ)+2*(310255832767/186600000000000 : ℝ)*(5477/50000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (9327093642567882431/9330000000000000000 : ℝ)+2*(310255832767/186600000000000 : ℝ)*(5477/50000 : ℝ)=(10000527529431953/10000000000000000 : ℝ) by norm_num, show 1+2*(10885055871854393/100000000000000000000 : ℝ)=(50010885055871854393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1824847950547821/5000000000000000000 : ℝ)+(10885055871854393/100000000000000000000 : ℝ) ≤ ((9327093642567882431/9330000000000000000 : ℝ)+(310255832767/186600000000000 : ℝ)*((7343/50000 : ℝ)+(5477/50000 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (9327093642567882431/9330000000000000000 : ℝ)+(310255832767/186600000000000 : ℝ)*((7343/50000 : ℝ)+(5477/50000 : ℝ))=(10001148041097487/10000000000000000 : ℝ) by norm_num, show 1+(1824847950547821/5000000000000000000 : ℝ)+(10885055871854393/100000000000000000000 : ℝ)=(100047382014882810813/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1824847950547821/5000000000000000000 : ℝ) ≤ ((9327093642567882431/9330000000000000000 : ℝ)+2*(310255832767/186600000000000 : ℝ)*(7343/50000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (9327093642567882431/9330000000000000000 : ℝ)+2*(310255832767/186600000000000 : ℝ)*(7343/50000 : ℝ)=(10001768552763021/10000000000000000 : ℝ) by norm_num, show 1+2*(1824847950547821/5000000000000000000 : ℝ)=(2501824847950547821/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9327093642567882431/9330000000000000000 : ℝ)*(X 1 0+X 2 0)+(310255832767/186600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (9327093642567882431/9330000000000000000 : ℝ)) (alpha := (310255832767/186600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9327093642567882431/9330000000000000000 : ℝ)*(X 0 1+X 2 1)+(310255832767/186600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (9327093642567882431/9330000000000000000 : ℝ)) (alpha := (310255832767/186600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9327093642567882431/9330000000000000000 : ℝ)*(X 0 2+X 1 2)+(310255832767/186600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (9327093642567882431/9330000000000000000 : ℝ)) (alpha := (310255832767/186600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-105582011/500000000 : ℝ)*X 0 0+(2698410463/5000000000 : ℝ)*X 0 1+(5261838851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672861467/5000000000 : ℝ)*X 1 0+(-2180163321/10000000000 : ℝ)*X 1 1+(328864931/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345723021/10000000000 : ℝ)*X 2 0+(210473553/400000000 : ℝ)*X 2 1+(-21801633/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((27175889/62500000 : ℝ)*X 0 0+(1053220747/2500000000 : ℝ)*X 0 1+(448760269/1000000000 : ℝ)*X 0 2+(27175889/62500000 : ℝ)*X 1 0+(1053220747/2500000000 : ℝ)*X 1 1+(448760269/1000000000 : ℝ)*X 1 2+(27175889/62500000 : ℝ)*X 2 0+(1053220747/2500000000 : ℝ)*X 2 1+(448760269/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-527911499/2500000000 : ℝ)*X 0 0+(2631105619/5000000000 : ℝ)*X 0 1+(5396447257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311244147/10000000000 : ℝ)*X 1 0+(-2045554877/10000000000 : ℝ)*X 1 1+(5396447227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311243951/10000000000 : ℝ)*X 2 0+(2698223693/5000000000 : ℝ)*X 2 1+(-2045554927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543519287/1250000000 : ℝ)*X 0 0+(897369051/2000000000 : ℝ)*X 0 1+(210682183/500000000 : ℝ)*X 0 2+(543519287/1250000000 : ℝ)*X 1 0+(897369051/2000000000 : ℝ)*X 1 1+(210682183/500000000 : ℝ)*X 1 2+(543519287/1250000000 : ℝ)*X 2 0+(897369051/2000000000 : ℝ)*X 2 1+(210682183/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (570756383292681482617398131/77750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1854174083/100000000000000 : ℝ)*(base19) + (904563837/50000000000000 : ℝ)*(base23) + (58062273/20000000000000 : ℝ)*(upper3) + (88534343/100000000000000 : ℝ)*(upper4) + (112801781/50000000000000 : ℝ)*(upper5) + (2762150217918433/50000000000000 : ℝ)*(major0) + (2762150217918433/50000000000000 : ℝ)*(major1) + (2762150217918433/50000000000000 : ℝ)*(major2) + (7408436313392869/100000000000000 : ℝ)*(sp0) + (7408480634964921/100000000000000 : ℝ)*(sp1) + (740848068001133/10000000000000 : ℝ)*(sp2) + (455011830101859/12500000000000 : ℝ)*(sp3) + (5771968267/12500000000000 : ℝ)*(sp4) + (23497022569/100000000000000 : ℝ)*(sp7) + (1820059068918721/50000000000000 : ℝ)*(f.failure) + (1852120622284751/25000000000000 : ℝ)*(f.sum) + (1119526228109/4665000000000000000000000000 : ℝ)*base66 + (9201332331912800623/466500000000000000000000000000000 : ℝ)*base67 + (7181079442845800623/466500000000000000000000000000000 : ℝ)*base69 + (6281281541450300623/466500000000000000000000000000000 : ℝ)*base71 + (36971794565761/4665000000000000000000000000 : ℝ)*base73 + (10149295439303300623/466500000000000000000000000000000 : ℝ)*base75 + (1221328778936300623/466500000000000000000000000000000 : ℝ)*base77 + (24007466583210800623/466500000000000000000000000000000 : ℝ)*base79 + (12975820367189/4665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (135197/500000000000000000000 : ℝ)*base89 + (135197/500000000000000000000 : ℝ)*base91 + (135197/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13474086501742902571777/3110000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126196693/20000000000000 : ℝ)*(base19) + (346695917/100000000000000 : ℝ)*(base23) + (30977/6250000000000 : ℝ)*(upper2) + (45885363/50000000000000 : ℝ)*(upper3) + (9639/62500000000 : ℝ)*(upper5) + (5554929997213979/100000000000000 : ℝ)*(major0) + (5554929997213979/100000000000000 : ℝ)*(major1) + (5554929997213979/100000000000000 : ℝ)*(major2) + (13101504341/100000000000000 : ℝ)*(sp1) + (2878272103/25000000000000 : ℝ)*(sp2) + (931194878252331/12500000000000 : ℝ)*(sp4) + (3724772646765421/50000000000000 : ℝ)*(sp5) + (7449547166234319/100000000000000 : ℝ)*(sp6) + (915075205998129/25000000000000 : ℝ)*(sp7) + (915075205998129/25000000000000 : ℝ)*(f.failure) + (931194878252331/12500000000000 : ℝ)*(f.sum) + (40476684639653/9330000000000000000000000000 : ℝ)*base65 + (2857693356984352949/933000000000000000000000000000000 : ℝ)*base67 + (14233930957548352949/933000000000000000000000000000000 : ℝ)*base69 + (1176140726615647051/933000000000000000000000000000000 : ℝ)*base72 + (11303913681157/9330000000000000000000000000 : ℝ)*base74 + (979636209473647051/933000000000000000000000000000000 : ℝ)*base76 + (733384886835352949/933000000000000000000000000000000 : ℝ)*base77 + (2970822775745647051/933000000000000000000000000000000 : ℝ)*base80 + (80413619775383/9330000000000000000000000000 : ℝ)*base81 + (89747/250000000000000000000 : ℝ)*base90 + (89747/250000000000000000000 : ℝ)*base92 + (89747/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1259_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1259_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1259_s5_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112065691/10000000000 : ℝ)*x 0 + (5392003103/10000000000 : ℝ)*x 1 + (1053275359/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112065691/10000000000 : ℝ)^2113 ≤ (6422716835649/50000000000000 : ℝ)^1601 := by
    have hnat : (2112065691 : ℕ)^2113*50000000000000^1601 ≤ 6422716835649^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112065691 10000000000 6422716835649 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392003103/10000000000 : ℝ)^2113 ≤ (44255147505927/100000000000000 : ℝ)^1601 := by
    have hnat : (5392003103 : ℕ)^2113*100000000000000^1601 ≤ 44255147505927^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392003103 10000000000 44255147505927 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053275359/2000000000 : ℝ)^2113 ≤ (8579883759939/20000000000000 : ℝ)^1601 := by
    have hnat : (1053275359 : ℕ)^2113*20000000000000^1601 ≤ 8579883759939^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053275359 2000000000 8579883759939 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112065691/10000000000 : ℝ), (5392003103/10000000000 : ℝ), (1053275359/2000000000 : ℝ)] ![(6422716835649/50000000000000 : ℝ), (44255147505927/100000000000000 : ℝ), (8579883759939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112065691/10000000000 : ℝ)|^2113 ≤ (6422716835649/50000000000000 : ℝ)^1601
        have hw : |(-2112065691/10000000000 : ℝ)|=(2112065691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392003103/10000000000 : ℝ)|^2113 ≤ (44255147505927/100000000000000 : ℝ)^1601
        have hw : |(5392003103/10000000000 : ℝ)|=(5392003103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053275359/2000000000 : ℝ)|^2113 ≤ (8579883759939/20000000000000 : ℝ)^1601
        have hw : |(1053275359/2000000000 : ℝ)|=(1053275359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s5_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344501483/10000000000 : ℝ)*x 0 + (-21757733/100000000 : ℝ)*x 1 + (5266376843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344501483/10000000000 : ℝ)^2113 ≤ (43741320635837/100000000000000 : ℝ)^1601 := by
    have hnat : (5344501483 : ℕ)^2113*100000000000000^1601 ≤ 43741320635837^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344501483 10000000000 43741320635837 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21757733/100000000 : ℝ)^2113 ≤ (6679630016227/50000000000000 : ℝ)^1601 := by
    have hnat : (21757733 : ℕ)^2113*50000000000000^1601 ≤ 6679630016227^1601*100000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21757733 100000000 6679630016227 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266376843/10000000000 : ℝ)^2113 ≤ (42899419315741/100000000000000 : ℝ)^1601 := by
    have hnat : (5266376843 : ℕ)^2113*100000000000000^1601 ≤ 42899419315741^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266376843 10000000000 42899419315741 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344501483/10000000000 : ℝ), (-21757733/100000000 : ℝ), (5266376843/10000000000 : ℝ)] ![(43741320635837/100000000000000 : ℝ), (6679630016227/50000000000000 : ℝ), (42899419315741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344501483/10000000000 : ℝ)|^2113 ≤ (43741320635837/100000000000000 : ℝ)^1601
        have hw : |(5344501483/10000000000 : ℝ)|=(5344501483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21757733/100000000 : ℝ)|^2113 ≤ (6679630016227/50000000000000 : ℝ)^1601
        have hw : |(-21757733/100000000 : ℝ)|=(21757733/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266376843/10000000000 : ℝ)|^2113 ≤ (42899419315741/100000000000000 : ℝ)^1601
        have hw : |(5266376843/10000000000 : ℝ)|=(5266376843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s5_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672250993/5000000000 : ℝ)*x 0 + (5266376731/10000000000 : ℝ)*x 1 + (-1087886389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672250993/5000000000 : ℝ)^2113 ≤ (21870663034551/50000000000000 : ℝ)^1601 := by
    have hnat : (2672250993 : ℕ)^2113*50000000000000^1601 ≤ 21870663034551^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672250993 5000000000 21870663034551 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266376731/10000000000 : ℝ)^2113 ≤ (42899418111633/100000000000000 : ℝ)^1601 := by
    have hnat : (5266376731 : ℕ)^2113*100000000000000^1601 ≤ 42899418111633^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266376731 10000000000 42899418111633 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087886389/5000000000 : ℝ)^2113 ≤ (6679627901193/50000000000000 : ℝ)^1601 := by
    have hnat : (1087886389 : ℕ)^2113*50000000000000^1601 ≤ 6679627901193^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087886389 5000000000 6679627901193 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672250993/5000000000 : ℝ), (5266376731/10000000000 : ℝ), (-1087886389/5000000000 : ℝ)] ![(21870663034551/50000000000000 : ℝ), (42899418111633/100000000000000 : ℝ), (6679627901193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672250993/5000000000 : ℝ)|^2113 ≤ (21870663034551/50000000000000 : ℝ)^1601
        have hw : |(2672250993/5000000000 : ℝ)|=(2672250993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266376731/10000000000 : ℝ)|^2113 ≤ (42899418111633/100000000000000 : ℝ)^1601
        have hw : |(5266376731/10000000000 : ℝ)|=(5266376731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087886389/5000000000 : ℝ)|^2113 ≤ (6679627901193/50000000000000 : ℝ)^1601
        have hw : |(-1087886389/5000000000 : ℝ)|=(1087886389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s5_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4348391293/10000000000 : ℝ)*x 0 + (2111186187/5000000000 : ℝ)*x 1 + (4478049933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348391293/10000000000 : ℝ)^2113 ≤ (16658506724699/50000000000000 : ℝ)^1601 := by
    have hnat : (4348391293 : ℕ)^2113*50000000000000^1601 ≤ 16658506724699^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348391293 10000000000 16658506724699 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111186187/5000000000 : ℝ)^2113 ≤ (32048629566833/100000000000000 : ℝ)^1601 := by
    have hnat : (2111186187 : ℕ)^2113*100000000000000^1601 ≤ 32048629566833^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111186187 5000000000 32048629566833 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478049933/10000000000 : ℝ)^2113 ≤ (1385374278581/4000000000000 : ℝ)^1601 := by
    have hnat : (4478049933 : ℕ)^2113*4000000000000^1601 ≤ 1385374278581^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478049933 10000000000 1385374278581 4000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348391293/10000000000 : ℝ), (2111186187/5000000000 : ℝ), (4478049933/10000000000 : ℝ)] ![(16658506724699/50000000000000 : ℝ), (32048629566833/100000000000000 : ℝ), (1385374278581/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348391293/10000000000 : ℝ)|^2113 ≤ (16658506724699/50000000000000 : ℝ)^1601
        have hw : |(4348391293/10000000000 : ℝ)|=(4348391293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111186187/5000000000 : ℝ)|^2113 ≤ (32048629566833/100000000000000 : ℝ)^1601
        have hw : |(2111186187/5000000000 : ℝ)|=(2111186187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478049933/10000000000 : ℝ)|^2113 ≤ (1385374278581/4000000000000 : ℝ)^1601
        have hw : |(4478049933/10000000000 : ℝ)|=(4478049933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s5_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056035303/5000000000 : ℝ)*x 0 + (41146091/78125000 : ℝ)*x 1 + (1347919757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056035303/5000000000 : ℝ)^2113 ≤ (12845473123677/100000000000000 : ℝ)^1601 := by
    have hnat : (1056035303 : ℕ)^2113*100000000000000^1601 ≤ 12845473123677^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056035303 5000000000 12845473123677 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41146091/78125000 : ℝ)^2113 ≤ (42902889816597/100000000000000 : ℝ)^1601 := by
    have hnat : (41146091 : ℕ)^2113*100000000000000^1601 ≤ 42902889816597^1601*78125000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41146091 78125000 42902889816597 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347919757/2500000000 : ℝ)^2113 ≤ (44251637052787/100000000000000 : ℝ)^1601 := by
    have hnat : (1347919757 : ℕ)^2113*100000000000000^1601 ≤ 44251637052787^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347919757 2500000000 44251637052787 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056035303/5000000000 : ℝ), (41146091/78125000 : ℝ), (1347919757/2500000000 : ℝ)] ![(12845473123677/100000000000000 : ℝ), (42902889816597/100000000000000 : ℝ), (44251637052787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056035303/5000000000 : ℝ)|^2113 ≤ (12845473123677/100000000000000 : ℝ)^1601
        have hw : |(-1056035303/5000000000 : ℝ)|=(1056035303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41146091/78125000 : ℝ)|^2113 ≤ (42902889816597/100000000000000 : ℝ)^1601
        have hw : |(41146091/78125000 : ℝ)|=(41146091/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347919757/2500000000 : ℝ)|^2113 ≤ (44251637052787/100000000000000 : ℝ)^1601
        have hw : |(1347919757/2500000000 : ℝ)|=(1347919757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s5_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312411399/10000000000 : ℝ)*x 0 + (-2050470611/10000000000 : ℝ)*x 1 + (2695839599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312411399/10000000000 : ℝ)^2113 ≤ (21697512915519/50000000000000 : ℝ)^1601 := by
    have hnat : (5312411399 : ℕ)^2113*50000000000000^1601 ≤ 21697512915519^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312411399 10000000000 21697512915519 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050470611/10000000000 : ℝ)^2113 ≤ (6176667630289/50000000000000 : ℝ)^1601 := by
    have hnat : (2050470611 : ℕ)^2113*50000000000000^1601 ≤ 6176667630289^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050470611 10000000000 6176667630289 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695839599/5000000000 : ℝ)^2113 ≤ (44251638894247/100000000000000 : ℝ)^1601 := by
    have hnat : (2695839599 : ℕ)^2113*100000000000000^1601 ≤ 44251638894247^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695839599 5000000000 44251638894247 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312411399/10000000000 : ℝ), (-2050470611/10000000000 : ℝ), (2695839599/5000000000 : ℝ)] ![(21697512915519/50000000000000 : ℝ), (6176667630289/50000000000000 : ℝ), (44251638894247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312411399/10000000000 : ℝ)|^2113 ≤ (21697512915519/50000000000000 : ℝ)^1601
        have hw : |(5312411399/10000000000 : ℝ)|=(5312411399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050470611/10000000000 : ℝ)|^2113 ≤ (6176667630289/50000000000000 : ℝ)^1601
        have hw : |(-2050470611/10000000000 : ℝ)|=(2050470611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695839599/5000000000 : ℝ)|^2113 ≤ (44251638894247/100000000000000 : ℝ)^1601
        have hw : |(2695839599/5000000000 : ℝ)|=(2695839599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s5_6 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312411173/10000000000 : ℝ)*x 0 + (1347919847/2500000000 : ℝ)*x 1 + (-2050470659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312411173/10000000000 : ℝ)^2113 ≤ (43395023394547/100000000000000 : ℝ)^1601 := by
    have hnat : (5312411173 : ℕ)^2113*100000000000000^1601 ≤ 43395023394547^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312411173 10000000000 43395023394547 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347919847/2500000000 : ℝ)^2113 ≤ (885032819047/2000000000000 : ℝ)^1601 := by
    have hnat : (1347919847 : ℕ)^2113*2000000000000^1601 ≤ 885032819047^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347919847 2500000000 885032819047 2000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050470659/10000000000 : ℝ)^2113 ≤ (12353335642241/100000000000000 : ℝ)^1601 := by
    have hnat : (2050470659 : ℕ)^2113*100000000000000^1601 ≤ 12353335642241^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050470659 10000000000 12353335642241 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312411173/10000000000 : ℝ), (1347919847/2500000000 : ℝ), (-2050470659/10000000000 : ℝ)] ![(43395023394547/100000000000000 : ℝ), (885032819047/2000000000000 : ℝ), (12353335642241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312411173/10000000000 : ℝ)|^2113 ≤ (43395023394547/100000000000000 : ℝ)^1601
        have hw : |(5312411173/10000000000 : ℝ)|=(5312411173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347919847/2500000000 : ℝ)|^2113 ≤ (885032819047/2000000000000 : ℝ)^1601
        have hw : |(1347919847/2500000000 : ℝ)|=(1347919847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050470659/10000000000 : ℝ)|^2113 ≤ (12353335642241/100000000000000 : ℝ)^1601
        have hw : |(-2050470659/10000000000 : ℝ)|=(2050470659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s5_7 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4348401119/10000000000 : ℝ)*x 0 + (559674209/1250000000 : ℝ)*x 1 + (211151557/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348401119/10000000000 : ℝ)^2113 ≤ (16658556405951/50000000000000 : ℝ)^1601 := by
    have hnat : (4348401119 : ℕ)^2113*50000000000000^1601 ≤ 16658556405951^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348401119 10000000000 16658556405951 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559674209/1250000000 : ℝ)^2113 ≤ (34627658229789/100000000000000 : ℝ)^1601 := by
    have hnat : (559674209 : ℕ)^2113*100000000000000^1601 ≤ 34627658229789^1601*1250000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559674209 1250000000 34627658229789 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211151557/500000000 : ℝ)^2113 ≤ (8013807236599/25000000000000 : ℝ)^1601 := by
    have hnat : (211151557 : ℕ)^2113*25000000000000^1601 ≤ 8013807236599^1601*500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211151557 500000000 8013807236599 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348401119/10000000000 : ℝ), (559674209/1250000000 : ℝ), (211151557/500000000 : ℝ)] ![(16658556405951/50000000000000 : ℝ), (34627658229789/100000000000000 : ℝ), (8013807236599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348401119/10000000000 : ℝ)|^2113 ≤ (16658556405951/50000000000000 : ℝ)^1601
        have hw : |(4348401119/10000000000 : ℝ)|=(4348401119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559674209/1250000000 : ℝ)|^2113 ≤ (34627658229789/100000000000000 : ℝ)^1601
        have hw : |(559674209/1250000000 : ℝ)|=(559674209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211151557/500000000 : ℝ)|^2113 ≤ (8013807236599/25000000000000 : ℝ)^1601
        have hw : |(211151557/500000000 : ℝ)|=(211151557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2869/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14137/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11379/100000 : ℝ) ^ (8451/2048 : ℝ) ≤ (3184100379579211/25000000000000000000 : ℝ) := by
    have hpowers : (11379/100000 : ℝ)^8451 ≤ (3184100379579211/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11379 : ℕ)^8451*25000000000000000000^2048 ≤ 3184100379579211^2048*100000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11379 100000 3184100379579211 25000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11379/100000 : ℝ)) (X := (3184100379579211/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (8451/2048 : ℝ) ≤ (32117150959209463/100000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^8451 ≤ (32117150959209463/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7119 : ℕ)^8451*100000000000000000000^2048 ≤ 32117150959209463^2048*50000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 32117150959209463 100000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (32117150959209463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503184100379579211/12500000000000000000 : ℝ) ≤ (80004937949799/80000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (12503184100379579211/12500000000000000000 : ℝ)^2048 ≤ (80004937949799/80000000000000 : ℝ)^8451 := by
      have hnat : (12503184100379579211 : ℕ)^2048*80000000000000^8451 ≤ 80004937949799^8451*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503184100379579211 12500000000000000000 80004937949799 80000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80004937949799/80000000000000 : ℝ)) (X := (12503184100379579211/12500000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044853552477526307/100000000000000000000 : ℝ) ≤ (10001086788200111/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (100044853552477526307/100000000000000000000 : ℝ)^2048 ≤ (10001086788200111/10000000000000000 : ℝ)^8451 := by
      have hnat : (100044853552477526307 : ℕ)^2048*10000000000000000^8451 ≤ 10001086788200111^8451*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044853552477526307 100000000000000000000 10001086788200111 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001086788200111/10000000000000000 : ℝ)) (X := (100044853552477526307/100000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032117150959209463/50000000000000000000 : ℝ) ≤ (10001556332675347/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50032117150959209463/50000000000000000000 : ℝ)^2048 ≤ (10001556332675347/10000000000000000 : ℝ)^8451 := by
      have hnat : (50032117150959209463 : ℕ)^2048*10000000000000000^8451 ≤ 10001556332675347^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032117150959209463 50000000000000000000 10001556332675347 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001556332675347/10000000000000000 : ℝ)) (X := (50032117150959209463/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3184100379579211/25000000000000000000 : ℝ) ≤ ((9527026268880665579/9530000000000000000 : ℝ)+2*(117386118809/71475000000000 : ℝ)*(11379/100000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (9527026268880665579/9530000000000000000 : ℝ)+2*(117386118809/71475000000000 : ℝ)*(11379/100000 : ℝ)=(80004937949799/80000000000000 : ℝ) by norm_num, show 1+2*(3184100379579211/25000000000000000000 : ℝ)=(12503184100379579211/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32117150959209463/100000000000000000000 : ℝ)+(3184100379579211/25000000000000000000 : ℝ) ≤ ((9527026268880665579/9530000000000000000 : ℝ)+(117386118809/71475000000000 : ℝ)*((7119/50000 : ℝ)+(11379/100000 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (9527026268880665579/9530000000000000000 : ℝ)+(117386118809/71475000000000 : ℝ)*((7119/50000 : ℝ)+(11379/100000 : ℝ))=(10001086788200111/10000000000000000 : ℝ) by norm_num, show 1+(32117150959209463/100000000000000000000 : ℝ)+(3184100379579211/25000000000000000000 : ℝ)=(100044853552477526307/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32117150959209463/100000000000000000000 : ℝ) ≤ ((9527026268880665579/9530000000000000000 : ℝ)+2*(117386118809/71475000000000 : ℝ)*(7119/50000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (9527026268880665579/9530000000000000000 : ℝ)+2*(117386118809/71475000000000 : ℝ)*(7119/50000 : ℝ)=(10001556332675347/10000000000000000 : ℝ) by norm_num, show 1+2*(32117150959209463/100000000000000000000 : ℝ)=(50032117150959209463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9527026268880665579/9530000000000000000 : ℝ)*(X 1 0+X 2 0)+(117386118809/71475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (9527026268880665579/9530000000000000000 : ℝ)) (alpha := (117386118809/71475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9527026268880665579/9530000000000000000 : ℝ)*(X 0 1+X 2 1)+(117386118809/71475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (9527026268880665579/9530000000000000000 : ℝ)) (alpha := (117386118809/71475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9527026268880665579/9530000000000000000 : ℝ)*(X 0 2+X 1 2)+(117386118809/71475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (9527026268880665579/9530000000000000000 : ℝ)) (alpha := (117386118809/71475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2112065691/10000000000 : ℝ)*X 0 0+(5392003103/10000000000 : ℝ)*X 0 1+(1053275359/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344501483/10000000000 : ℝ)*X 1 0+(-21757733/100000000 : ℝ)*X 1 1+(5266376843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672250993/5000000000 : ℝ)*X 2 0+(5266376731/10000000000 : ℝ)*X 2 1+(-1087886389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348391293/10000000000 : ℝ)*X 0 0+(2111186187/5000000000 : ℝ)*X 0 1+(4478049933/10000000000 : ℝ)*X 0 2+(4348391293/10000000000 : ℝ)*X 1 0+(2111186187/5000000000 : ℝ)*X 1 1+(4478049933/10000000000 : ℝ)*X 1 2+(4348391293/10000000000 : ℝ)*X 2 0+(2111186187/5000000000 : ℝ)*X 2 1+(4478049933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1056035303/5000000000 : ℝ)*X 0 0+(41146091/78125000 : ℝ)*X 0 1+(1347919757/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312411399/10000000000 : ℝ)*X 1 0+(-2050470611/10000000000 : ℝ)*X 1 1+(2695839599/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312411173/10000000000 : ℝ)*X 2 0+(1347919847/2500000000 : ℝ)*X 2 1+(-2050470659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348401119/10000000000 : ℝ)*X 0 0+(559674209/1250000000 : ℝ)*X 0 1+(211151557/500000000 : ℝ)*X 0 2+(4348401119/10000000000 : ℝ)*X 1 0+(559674209/1250000000 : ℝ)*X 1 1+(211151557/500000000 : ℝ)*X 1 2+(4348401119/10000000000 : ℝ)*X 2 0+(559674209/1250000000 : ℝ)*X 2 1+(211151557/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26669619884703539498313/4765000000000000000000000000 : ℝ) := by norm_num
    linear_combination (633076823/100000000000000 : ℝ)*(base19) + (1392350529/100000000000000 : ℝ)*(base23) + (85069453/100000000000000 : ℝ)*(lower2) + (35955351/20000000000000 : ℝ)*(upper5) + (5935704769106151/100000000000000 : ℝ)*(major0) + (5935704769106151/100000000000000 : ℝ)*(major1) + (5935704769106151/100000000000000 : ℝ)*(major2) + (7960150081261163/100000000000000 : ℝ)*(sp0) + (7960176413708581/100000000000000 : ℝ)*(sp1) + (1990050961357667/25000000000000 : ℝ)*(sp2) + (977797304424441/25000000000000 : ℝ)*(sp3) + (27578260017/50000000000000 : ℝ)*(sp4) + (14095497897/50000000000000 : ℝ)*(sp5) + (7448083631/50000000000000 : ℝ)*(sp7) + (1955602056932513/50000000000000 : ℝ)*(f.failure) + (7960205237781197/100000000000000 : ℝ)*(f.sum) + (8060406761433/4765000000000000000000000000 : ℝ)*base66 + (19808309456808923571/953000000000000000000000000000000 : ℝ)*base68 + (4379618285367076429/953000000000000000000000000000000 : ℝ)*base69 + (18996107428422923571/953000000000000000000000000000000 : ℝ)*base72 + (3207489375889/2382500000000000000000000000 : ℝ)*base74 + (370801429893076429/953000000000000000000000000000000 : ℝ)*base75 + (5533802637870076429/953000000000000000000000000000000 : ℝ)*base77 + (9903637017919923571/953000000000000000000000000000000 : ℝ)*base80 + (360133602663/297812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (692541/500000000000000000000 : ℝ)*base89 + (692541/500000000000000000000 : ℝ)*base91 + (692541/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (447062052130238066581572327/95300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (350670657/50000000000000 : ℝ)*(base19) + (384449827/100000000000000 : ℝ)*(base23) + (35965791/25000000000000 : ℝ)*(upper3) + (232237/2500000000000 : ℝ)*(lower4) + (1193270922597357/20000000000000 : ℝ)*(major0) + (1193270922597357/20000000000000 : ℝ)*(major1) + (1193270922597357/20000000000000 : ℝ)*(major2) + (6291973989/25000000000000 : ℝ)*(sp1) + (26162717469/100000000000000 : ℝ)*(sp2) + (303924319/25000000000000 : ℝ)*(sp3) + (2000327226216731/25000000000000 : ℝ)*(sp4) + (1600256607125931/20000000000000 : ℝ)*(sp5) + (2000320589424907/25000000000000 : ℝ)*(sp6) + (1965699474519641/50000000000000 : ℝ)*(sp7) + (3931400164736557/100000000000000 : ℝ)*(f.failure) + (2000327226216731/25000000000000 : ℝ)*(f.sum) + (1337967571869/476500000000000000000000000 : ℝ)*base65 + (2008723179593325297/190600000000000000000000000000000 : ℝ)*base68 + (2125537036421325297/190600000000000000000000000000000 : ℝ)*base70 + (2895393434026725297/190600000000000000000000000000000 : ℝ)*base72 + (637268713587/190600000000000000000000000 : ℝ)*base74 + (4440468140596925297/190600000000000000000000000000000 : ℝ)*base76 + (2017946699367725297/190600000000000000000000000000000 : ℝ)*base78 + (2339230965533925297/190600000000000000000000000000000 : ℝ)*base80 + (565603112511/476500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2671449/1000000000000000000000 : ℝ)*base89 + (2671449/1000000000000000000000 : ℝ)*base91 + (2671449/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1259_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1259_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1259_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (299/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1259_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1259_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1259_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (299/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1259_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

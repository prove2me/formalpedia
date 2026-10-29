-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1297_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:35:21.342005+00:00
-- url     : https://prove2.me/submissions/dad1b51b-f4ef-409a-b481-ac6de1fb48b4

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
theorem support_rectangle_w1297_s3_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104060361/500000000 : ℝ)*x 0 + (1086668633/2000000000 : ℝ)*x 1 + (1306575629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104060361/500000000 : ℝ)^4257 ≤ (1582387480191/12500000000000 : ℝ)^3233 := by
    have hnat : (104060361 : ℕ)^4257*12500000000000^3233 ≤ 1582387480191^3233*500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104060361 500000000 1582387480191 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086668633/2000000000 : ℝ)^4257 ≤ (44787206318671/100000000000000 : ℝ)^3233 := by
    have hnat : (1086668633 : ℕ)^4257*100000000000000^3233 ≤ 44787206318671^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086668633 2000000000 44787206318671 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306575629/2500000000 : ℝ)^4257 ≤ (4255369382567/10000000000000 : ℝ)^3233 := by
    have hnat : (1306575629 : ℕ)^4257*10000000000000^3233 ≤ 4255369382567^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306575629 2500000000 4255369382567 10000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104060361/500000000 : ℝ), (1086668633/2000000000 : ℝ), (1306575629/2500000000 : ℝ)] ![(1582387480191/12500000000000 : ℝ), (44787206318671/100000000000000 : ℝ), (4255369382567/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104060361/500000000 : ℝ)|^4257 ≤ (1582387480191/12500000000000 : ℝ)^3233
        have hw : |(-104060361/500000000 : ℝ)|=(104060361/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086668633/2000000000 : ℝ)|^4257 ≤ (44787206318671/100000000000000 : ℝ)^3233
        have hw : |(1086668633/2000000000 : ℝ)|=(1086668633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306575629/2500000000 : ℝ)|^4257 ≤ (4255369382567/10000000000000 : ℝ)^3233
        have hw : |(1306575629/2500000000 : ℝ)|=(1306575629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s3_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53543603/100000000 : ℝ)*x 0 + (-1093575981/5000000000 : ℝ)*x 1 + (2613151333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53543603/100000000 : ℝ)^4257 ≤ (43931916360689/100000000000000 : ℝ)^3233 := by
    have hnat : (53543603 : ℕ)^4257*100000000000000^3233 ≤ 43931916360689^3233*100000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53543603 100000000 43931916360689 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093575981/5000000000 : ℝ)^4257 ≤ (13514388184513/100000000000000 : ℝ)^3233 := by
    have hnat : (1093575981 : ℕ)^4257*100000000000000^3233 ≤ 13514388184513^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093575981 5000000000 13514388184513 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613151333/5000000000 : ℝ)^4257 ≤ (531921192923/1250000000000 : ℝ)^3233 := by
    have hnat : (2613151333 : ℕ)^4257*1250000000000^3233 ≤ 531921192923^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613151333 5000000000 531921192923 1250000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53543603/100000000 : ℝ), (-1093575981/5000000000 : ℝ), (2613151333/5000000000 : ℝ)] ![(43931916360689/100000000000000 : ℝ), (13514388184513/100000000000000 : ℝ), (531921192923/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53543603/100000000 : ℝ)|^4257 ≤ (43931916360689/100000000000000 : ℝ)^3233
        have hw : |(53543603/100000000 : ℝ)|=(53543603/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1093575981/5000000000 : ℝ)|^4257 ≤ (13514388184513/100000000000000 : ℝ)^3233
        have hw : |(-1093575981/5000000000 : ℝ)|=(1093575981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613151333/5000000000 : ℝ)|^4257 ≤ (531921192923/1250000000000 : ℝ)^3233
        have hw : |(2613151333/5000000000 : ℝ)|=(2613151333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s3_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354360377/10000000000 : ℝ)*x 0 + (1306575573/2500000000 : ℝ)*x 1 + (-1093576177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354360377/10000000000 : ℝ)^4257 ≤ (4393191719257/10000000000000 : ℝ)^3233 := by
    have hnat : (5354360377 : ℕ)^4257*10000000000000^3233 ≤ 4393191719257^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354360377 10000000000 4393191719257 10000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306575573/2500000000 : ℝ)^4257 ≤ (42553691424137/100000000000000 : ℝ)^3233 := by
    have hnat : (1306575573 : ℕ)^4257*100000000000000^3233 ≤ 42553691424137^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306575573 2500000000 42553691424137 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093576177/5000000000 : ℝ)^4257 ≤ (6757195686929/50000000000000 : ℝ)^3233 := by
    have hnat : (1093576177 : ℕ)^4257*50000000000000^3233 ≤ 6757195686929^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093576177 5000000000 6757195686929 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354360377/10000000000 : ℝ), (1306575573/2500000000 : ℝ), (-1093576177/5000000000 : ℝ)] ![(4393191719257/10000000000000 : ℝ), (42553691424137/100000000000000 : ℝ), (6757195686929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354360377/10000000000 : ℝ)|^4257 ≤ (4393191719257/10000000000000 : ℝ)^3233
        have hw : |(5354360377/10000000000 : ℝ)|=(5354360377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306575573/2500000000 : ℝ)|^4257 ≤ (42553691424137/100000000000000 : ℝ)^3233
        have hw : |(1306575573/2500000000 : ℝ)|=(1306575573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1093576177/5000000000 : ℝ)|^4257 ≤ (6757195686929/50000000000000 : ℝ)^3233
        have hw : |(-1093576177/5000000000 : ℝ)|=(1093576177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s3_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2168573599/5000000000 : ℝ)*x 0 + (4128973621/10000000000 : ℝ)*x 1 + (2277652427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168573599/5000000000 : ℝ)^4257 ≤ (8322130241747/25000000000000 : ℝ)^3233 := by
    have hnat : (2168573599 : ℕ)^4257*25000000000000^3233 ≤ 8322130241747^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168573599 5000000000 8322130241747 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128973621/10000000000 : ℝ)^4257 ≤ (3120084557791/10000000000000 : ℝ)^3233 := by
    have hnat : (4128973621 : ℕ)^4257*10000000000000^3233 ≤ 3120084557791^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128973621 10000000000 3120084557791 10000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2277652427/5000000000 : ℝ)^4257 ≤ (7102126688421/20000000000000 : ℝ)^3233 := by
    have hnat : (2277652427 : ℕ)^4257*20000000000000^3233 ≤ 7102126688421^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277652427 5000000000 7102126688421 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168573599/5000000000 : ℝ), (4128973621/10000000000 : ℝ), (2277652427/5000000000 : ℝ)] ![(8322130241747/25000000000000 : ℝ), (3120084557791/10000000000000 : ℝ), (7102126688421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168573599/5000000000 : ℝ)|^4257 ≤ (8322130241747/25000000000000 : ℝ)^3233
        have hw : |(2168573599/5000000000 : ℝ)|=(2168573599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128973621/10000000000 : ℝ)|^4257 ≤ (3120084557791/10000000000000 : ℝ)^3233
        have hw : |(4128973621/10000000000 : ℝ)|=(4128973621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2277652427/5000000000 : ℝ)|^4257 ≤ (7102126688421/20000000000000 : ℝ)^3233
        have hw : |(2277652427/5000000000 : ℝ)|=(2277652427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s3_4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2081229441/10000000000 : ℝ)*x 0 + (5227190891/10000000000 : ℝ)*x 1 + (5432449211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081229441/10000000000 : ℝ)^4257 ≤ (12659277812749/100000000000000 : ℝ)^3233 := by
    have hnat : (2081229441 : ℕ)^4257*100000000000000^3233 ≤ 12659277812749^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081229441 10000000000 12659277812749 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227190891/10000000000 : ℝ)^4257 ≤ (42563218468183/100000000000000 : ℝ)^3233 := by
    have hnat : (5227190891 : ℕ)^4257*100000000000000^3233 ≤ 42563218468183^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227190891 10000000000 42563218468183 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432449211/10000000000 : ℝ)^4257 ≤ (179110014829/400000000000 : ℝ)^3233 := by
    have hnat : (5432449211 : ℕ)^4257*400000000000^3233 ≤ 179110014829^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432449211 10000000000 179110014829 400000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2081229441/10000000000 : ℝ), (5227190891/10000000000 : ℝ), (5432449211/10000000000 : ℝ)] ![(12659277812749/100000000000000 : ℝ), (42563218468183/100000000000000 : ℝ), (179110014829/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2081229441/10000000000 : ℝ)|^4257 ≤ (12659277812749/100000000000000 : ℝ)^3233
        have hw : |(-2081229441/10000000000 : ℝ)|=(2081229441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227190891/10000000000 : ℝ)|^4257 ≤ (42563218468183/100000000000000 : ℝ)^3233
        have hw : |(5227190891/10000000000 : ℝ)|=(5227190891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432449211/10000000000 : ℝ)|^4257 ≤ (179110014829/400000000000 : ℝ)^3233
        have hw : |(5432449211/10000000000 : ℝ)|=(5432449211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s3_5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301315461/10000000000 : ℝ)*x 0 + (-396201061/2000000000 : ℝ)*x 1 + (5432449171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301315461/10000000000 : ℝ)^4257 ≤ (4335973964009/10000000000000 : ℝ)^3233 := by
    have hnat : (5301315461 : ℕ)^4257*10000000000000^3233 ≤ 4335973964009^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301315461 10000000000 4335973964009 10000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396201061/2000000000 : ℝ)^4257 ≤ (11862757064829/100000000000000 : ℝ)^3233 := by
    have hnat : (396201061 : ℕ)^4257*100000000000000^3233 ≤ 11862757064829^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396201061 2000000000 11862757064829 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432449171/10000000000 : ℝ)^4257 ≤ (44777503273117/100000000000000 : ℝ)^3233 := by
    have hnat : (5432449171 : ℕ)^4257*100000000000000^3233 ≤ 44777503273117^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432449171 10000000000 44777503273117 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301315461/10000000000 : ℝ), (-396201061/2000000000 : ℝ), (5432449171/10000000000 : ℝ)] ![(4335973964009/10000000000000 : ℝ), (11862757064829/100000000000000 : ℝ), (44777503273117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301315461/10000000000 : ℝ)|^4257 ≤ (4335973964009/10000000000000 : ℝ)^3233
        have hw : |(5301315461/10000000000 : ℝ)|=(5301315461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396201061/2000000000 : ℝ)|^4257 ≤ (11862757064829/100000000000000 : ℝ)^3233
        have hw : |(-396201061/2000000000 : ℝ)|=(396201061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432449171/10000000000 : ℝ)|^4257 ≤ (44777503273117/100000000000000 : ℝ)^3233
        have hw : |(5432449171/10000000000 : ℝ)|=(5432449171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s3_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301315527/10000000000 : ℝ)*x 0 + (84882017/156250000 : ℝ)*x 1 + (-198100533/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301315527/10000000000 : ℝ)^4257 ≤ (8671948070177/20000000000000 : ℝ)^3233 := by
    have hnat : (5301315527 : ℕ)^4257*20000000000000^3233 ≤ 8671948070177^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301315527 10000000000 8671948070177 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84882017/156250000 : ℝ)^4257 ≤ (44777502372293/100000000000000 : ℝ)^3233 := by
    have hnat : (84882017 : ℕ)^4257*100000000000000^3233 ≤ 44777502372293^3233*156250000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84882017 156250000 44777502372293 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198100533/1000000000 : ℝ)^4257 ≤ (92677791109/781250000000 : ℝ)^3233 := by
    have hnat : (198100533 : ℕ)^4257*781250000000^3233 ≤ 92677791109^3233*1000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198100533 1000000000 92677791109 781250000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301315527/10000000000 : ℝ), (84882017/156250000 : ℝ), (-198100533/1000000000 : ℝ)] ![(8671948070177/20000000000000 : ℝ), (44777502372293/100000000000000 : ℝ), (92677791109/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301315527/10000000000 : ℝ)|^4257 ≤ (8671948070177/20000000000000 : ℝ)^3233
        have hw : |(5301315527/10000000000 : ℝ)|=(5301315527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84882017/156250000 : ℝ)|^4257 ≤ (44777502372293/100000000000000 : ℝ)^3233
        have hw : |(84882017/156250000 : ℝ)|=(84882017/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198100533/1000000000 : ℝ)|^4257 ≤ (92677791109/781250000000 : ℝ)^3233
        have hw : |(-198100533/1000000000 : ℝ)|=(198100533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s3_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4337192521/10000000000 : ℝ)*x 0 + (45534753/100000000 : ℝ)*x 1 + (516351841/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337192521/10000000000 : ℝ)^4257 ≤ (6657795802293/20000000000000 : ℝ)^3233 := by
    have hnat : (4337192521 : ℕ)^4257*20000000000000^3233 ≤ 6657795802293^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337192521 10000000000 6657795802293 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45534753/100000000 : ℝ)^4257 ≤ (35491855131251/100000000000000 : ℝ)^3233 := by
    have hnat : (45534753 : ℕ)^4257*100000000000000^3233 ≤ 35491855131251^3233*100000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45534753 100000000 35491855131251 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516351841/1250000000 : ℝ)^4257 ≤ (31219165848941/100000000000000 : ℝ)^3233 := by
    have hnat : (516351841 : ℕ)^4257*100000000000000^3233 ≤ 31219165848941^3233*1250000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516351841 1250000000 31219165848941 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337192521/10000000000 : ℝ), (45534753/100000000 : ℝ), (516351841/1250000000 : ℝ)] ![(6657795802293/20000000000000 : ℝ), (35491855131251/100000000000000 : ℝ), (31219165848941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337192521/10000000000 : ℝ)|^4257 ≤ (6657795802293/20000000000000 : ℝ)^3233
        have hw : |(4337192521/10000000000 : ℝ)|=(4337192521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45534753/100000000 : ℝ)|^4257 ≤ (35491855131251/100000000000000 : ℝ)^3233
        have hw : |(45534753/100000000 : ℝ)|=(45534753/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516351841/1250000000 : ℝ)|^4257 ≤ (31219165848941/100000000000000 : ℝ)^3233
        have hw : |(516351841/1250000000 : ℝ)|=(516351841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1297_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (267/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (753/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9541/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9541/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9541/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9541/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9541/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9541/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9541/100000 : ℝ) ^ (133/32 : ℝ) ≤ (574033356600583/10000000000000000000 : ℝ) := by
    have hpowers : (9541/100000 : ℝ)^133 ≤ (574033356600583/10000000000000000000 : ℝ)^32 := by
      have hnat : (9541 : ℕ)^133*10000000000000000000^32 ≤ 574033356600583^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9541 100000 574033356600583 10000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9541/100000 : ℝ)) (X := (574033356600583/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hpowhi : (3259/20000 : ℝ) ^ (133/32 : ℝ) ≤ (26550393252556197/50000000000000000000 : ℝ) := by
    have hpowers : (3259/20000 : ℝ)^133 ≤ (26550393252556197/50000000000000000000 : ℝ)^32 := by
      have hnat : (3259 : ℕ)^133*50000000000000000000^32 ≤ 26550393252556197^32*20000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3259 20000 26550393252556197 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3259/20000 : ℝ)) (X := (26550393252556197/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000574033356600583/5000000000000000000 : ℝ) ≤ (10000276214537153/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (5000574033356600583/5000000000000000000 : ℝ)^32 ≤ (10000276214537153/10000000000000000 : ℝ)^133 := by
      have hnat : (5000574033356600583 : ℕ)^32*10000000000000000^133 ≤ 10000276214537153^133*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000574033356600583 5000000000000000000 10000276214537153 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000276214537153/10000000000000000 : ℝ)) (X := (5000574033356600583/5000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253677570004444889/6250000000000000000 : ℝ) ≤ (2500353852501441/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (6253677570004444889/6250000000000000000 : ℝ)^32 ≤ (2500353852501441/2500000000000000 : ℝ)^133 := by
      have hnat : (6253677570004444889 : ℕ)^32*2500000000000000^133 ≤ 2500353852501441^133*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253677570004444889 6250000000000000000 2500353852501441 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500353852501441/2500000000000000 : ℝ)) (X := (6253677570004444889/6250000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (25026550393252556197/25000000000000000000 : ℝ) ≤ (16004087368759/16000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25026550393252556197/25000000000000000000 : ℝ)^32 ≤ (16004087368759/16000000000000 : ℝ)^133 := by
      have hnat : (25026550393252556197 : ℕ)^32*16000000000000^133 ≤ 16004087368759^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25026550393252556197 25000000000000000000 16004087368759 16000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (16004087368759/16000000000000 : ℝ)) (X := (25026550393252556197/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(574033356600583/10000000000000000000 : ℝ) ≤ ((3376006371252594813/3377000000000000000 : ℝ)+2*(1139195468611/675400000000000 : ℝ)*(9541/100000 : ℝ))^(133/32 : ℝ) := by
    rw [show (3376006371252594813/3377000000000000000 : ℝ)+2*(1139195468611/675400000000000 : ℝ)*(9541/100000 : ℝ)=(10000276214537153/10000000000000000 : ℝ) by norm_num, show 1+2*(574033356600583/10000000000000000000 : ℝ)=(5000574033356600583/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26550393252556197/50000000000000000000 : ℝ)+(574033356600583/10000000000000000000 : ℝ) ≤ ((3376006371252594813/3377000000000000000 : ℝ)+(1139195468611/675400000000000 : ℝ)*((3259/20000 : ℝ)+(9541/100000 : ℝ)))^(133/32 : ℝ) := by
    rw [show (3376006371252594813/3377000000000000000 : ℝ)+(1139195468611/675400000000000 : ℝ)*((3259/20000 : ℝ)+(9541/100000 : ℝ))=(2500353852501441/2500000000000000 : ℝ) by norm_num, show 1+(26550393252556197/50000000000000000000 : ℝ)+(574033356600583/10000000000000000000 : ℝ)=(6253677570004444889/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26550393252556197/50000000000000000000 : ℝ) ≤ ((3376006371252594813/3377000000000000000 : ℝ)+2*(1139195468611/675400000000000 : ℝ)*(3259/20000 : ℝ))^(133/32 : ℝ) := by
    rw [show (3376006371252594813/3377000000000000000 : ℝ)+2*(1139195468611/675400000000000 : ℝ)*(3259/20000 : ℝ)=(16004087368759/16000000000000 : ℝ) by norm_num, show 1+2*(26550393252556197/50000000000000000000 : ℝ)=(25026550393252556197/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3376006371252594813/3377000000000000000 : ℝ)*(X 1 0+X 2 0)+(1139195468611/675400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (9541/100000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (3376006371252594813/3377000000000000000 : ℝ)) (alpha := (1139195468611/675400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3376006371252594813/3377000000000000000 : ℝ)*(X 0 1+X 2 1)+(1139195468611/675400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (9541/100000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (3376006371252594813/3377000000000000000 : ℝ)) (alpha := (1139195468611/675400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3376006371252594813/3377000000000000000 : ℝ)*(X 0 2+X 1 2)+(1139195468611/675400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (9541/100000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (3376006371252594813/3377000000000000000 : ℝ)) (alpha := (1139195468611/675400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-104060361/500000000 : ℝ)*X 0 0+(1086668633/2000000000 : ℝ)*X 0 1+(1306575629/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53543603/100000000 : ℝ)*X 1 0+(-1093575981/5000000000 : ℝ)*X 1 1+(2613151333/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354360377/10000000000 : ℝ)*X 2 0+(1306575573/2500000000 : ℝ)*X 2 1+(-1093576177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2168573599/5000000000 : ℝ)*X 0 0+(4128973621/10000000000 : ℝ)*X 0 1+(2277652427/5000000000 : ℝ)*X 0 2+(2168573599/5000000000 : ℝ)*X 1 0+(4128973621/10000000000 : ℝ)*X 1 1+(2277652427/5000000000 : ℝ)*X 1 2+(2168573599/5000000000 : ℝ)*X 2 0+(4128973621/10000000000 : ℝ)*X 2 1+(2277652427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2081229441/10000000000 : ℝ)*X 0 0+(5227190891/10000000000 : ℝ)*X 0 1+(5432449211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301315461/10000000000 : ℝ)*X 1 0+(-396201061/2000000000 : ℝ)*X 1 1+(5432449171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301315527/10000000000 : ℝ)*X 2 0+(84882017/156250000 : ℝ)*X 2 1+(-198100533/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4337192521/10000000000 : ℝ)*X 0 0+(45534753/100000000 : ℝ)*X 0 1+(516351841/1250000000 : ℝ)*X 0 2+(4337192521/10000000000 : ℝ)*X 1 0+(45534753/100000000 : ℝ)*X 1 1+(516351841/1250000000 : ℝ)*X 1 2+(4337192521/10000000000 : ℝ)*X 2 0+(45534753/100000000 : ℝ)*X 2 1+(516351841/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11350441140568921254320163/2638281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (812948839/100000000000000 : ℝ)*(base19) + (523800193/50000000000000 : ℝ)*(base23) + (6775209/50000000000000 : ℝ)*(lower2) + (256949261/100000000000000 : ℝ)*(upper3) + (25500083/25000000000000 : ℝ)*(lower4) + (224237782611631/6250000000000 : ℝ)*(major0) + (224237782611631/6250000000000 : ℝ)*(major1) + (224237782611631/6250000000000 : ℝ)*(major2) + (965997658010561/20000000000000 : ℝ)*(sp0) + (60374966906163/1250000000000 : ℝ)*(sp1) + (4829997117841493/100000000000000 : ℝ)*(sp2) + (1172800475662517/50000000000000 : ℝ)*(sp3) + (4937694537/50000000000000 : ℝ)*(sp4) + (9783398257/100000000000000 : ℝ)*(sp7) + (234561073472329/10000000000000 : ℝ)*(f.failure) + (4829998165441879/100000000000000 : ℝ)*(f.sum) + (49625759154253/16885000000000000000000000000 : ℝ)*base65 + (219223555904606247/21106250000000000000000000000000 : ℝ)*base68 + (277320390715112497/21106250000000000000000000000000 : ℝ)*base70 + (225305736706556247/21106250000000000000000000000000 : ℝ)*base72 + (8355379876131/8442500000000000000000000000 : ℝ)*base74 + (293883871737249997/21106250000000000000000000000000 : ℝ)*base76 + (24446227191537497/21106250000000000000000000000000 : ℝ)*base78 + (23548550518787497/21106250000000000000000000000000 : ℝ)*base80 + (29757825499261/8442500000000000000000000000 : ℝ)*base82 + (188519/62500000000000000000 : ℝ)*base90 + (188519/62500000000000000000 : ℝ)*base92 + (188519/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138537744371254202675457/16885000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1954480103/100000000000000 : ℝ)*(base19) + (1049290569/50000000000000 : ℝ)*(base23) + (25052809/12500000000000 : ℝ)*(upper3) + (40735553/100000000000000 : ℝ)*(lower4) + (213131433/100000000000000 : ℝ)*(upper5) + (904734312276093/25000000000000 : ℝ)*(major0) + (904734312276093/25000000000000 : ℝ)*(major1) + (904734312276093/25000000000000 : ℝ)*(major2) + (4079675107/12500000000000 : ℝ)*(sp1) + (33297658273/100000000000000 : ℝ)*(sp2) + (1217977436174827/25000000000000 : ℝ)*(sp4) + (4871875152818349/100000000000000 : ℝ)*(sp5) + (608984293557487/12500000000000 : ℝ)*(sp6) + (473192896003339/20000000000000 : ℝ)*(sp7) + (473192896003339/20000000000000 : ℝ)*(f.failure) + (1217977436174827/25000000000000 : ℝ)*(f.sum) + (26128532190351/16885000000000000000000000000 : ℝ)*base65 + (442806137746579391/84425000000000000000000000000000 : ℝ)*base68 + (371449538460079391/84425000000000000000000000000000 : ℝ)*base70 + (495830011310620609/84425000000000000000000000000000 : ℝ)*base71 + (14593044530309/16885000000000000000000000000 : ℝ)*base74 + (794858637647445609/84425000000000000000000000000000 : ℝ)*base75 + (562657175239420609/84425000000000000000000000000000 : ℝ)*base77 + (301886725253379391/84425000000000000000000000000000 : ℝ)*base80 + (2015159416001/1055312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (530629/125000000000000000000 : ℝ)*base90 + (530629/125000000000000000000 : ℝ)*base92 + (530629/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1297_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (753/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1297_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1297_s4_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-32548067/156250000 : ℝ)*x 0 + (169329661/312500000 : ℝ)*x 1 + (523987119/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32548067/156250000 : ℝ)^4257 ≤ (3168517895577/25000000000000 : ℝ)^3233 := by
    have hnat : (32548067 : ℕ)^4257*25000000000000^3233 ≤ 3168517895577^3233*156250000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32548067 156250000 3168517895577 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169329661/312500000 : ℝ)^4257 ≤ (1785068129809/4000000000000 : ℝ)^3233 := by
    have hnat : (169329661 : ℕ)^4257*4000000000000^3233 ≤ 1785068129809^3233*312500000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169329661 312500000 1785068129809 4000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523987119/1000000000 : ℝ)^4257 ≤ (10674806288607/25000000000000 : ℝ)^3233 := by
    have hnat : (523987119 : ℕ)^4257*25000000000000^3233 ≤ 10674806288607^3233*1000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523987119 1000000000 10674806288607 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32548067/156250000 : ℝ), (169329661/312500000 : ℝ), (523987119/1000000000 : ℝ)] ![(3168517895577/25000000000000 : ℝ), (1785068129809/4000000000000 : ℝ), (10674806288607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32548067/156250000 : ℝ)|^4257 ≤ (3168517895577/25000000000000 : ℝ)^3233
        have hw : |(-32548067/156250000 : ℝ)|=(32548067/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169329661/312500000 : ℝ)|^4257 ≤ (1785068129809/4000000000000 : ℝ)^3233
        have hw : |(169329661/312500000 : ℝ)|=(169329661/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523987119/1000000000 : ℝ)|^4257 ≤ (10674806288607/25000000000000 : ℝ)^3233
        have hw : |(523987119/1000000000 : ℝ)|=(523987119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s4_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070123601/2000000000 : ℝ)*x 0 + (-217422157/1000000000 : ℝ)*x 1 + (654983903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070123601/2000000000 : ℝ)^4257 ≤ (21945745195769/50000000000000 : ℝ)^3233 := by
    have hnat : (1070123601 : ℕ)^4257*50000000000000^3233 ≤ 21945745195769^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070123601 2000000000 21945745195769 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217422157/1000000000 : ℝ)^4257 ≤ (838080254421/6250000000000 : ℝ)^3233 := by
    have hnat : (217422157 : ℕ)^4257*6250000000000^3233 ≤ 838080254421^3233*1000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217422157 1000000000 838080254421 6250000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654983903/1250000000 : ℝ)^4257 ≤ (21349612759623/50000000000000 : ℝ)^3233 := by
    have hnat : (654983903 : ℕ)^4257*50000000000000^3233 ≤ 21349612759623^3233*1250000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654983903 1250000000 21349612759623 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070123601/2000000000 : ℝ), (-217422157/1000000000 : ℝ), (654983903/1250000000 : ℝ)] ![(21945745195769/50000000000000 : ℝ), (838080254421/6250000000000 : ℝ), (21349612759623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070123601/2000000000 : ℝ)|^4257 ≤ (21945745195769/50000000000000 : ℝ)^3233
        have hw : |(1070123601/2000000000 : ℝ)|=(1070123601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217422157/1000000000 : ℝ)|^4257 ≤ (838080254421/6250000000000 : ℝ)^3233
        have hw : |(-217422157/1000000000 : ℝ)|=(217422157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654983903/1250000000 : ℝ)|^4257 ≤ (21349612759623/50000000000000 : ℝ)^3233
        have hw : |(654983903/1250000000 : ℝ)|=(654983903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s4_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675309021/5000000000 : ℝ)*x 0 + (5239871177/10000000000 : ℝ)*x 1 + (-135888849/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675309021/5000000000 : ℝ)^4257 ≤ (8778298158237/20000000000000 : ℝ)^3233 := by
    have hnat : (2675309021 : ℕ)^4257*20000000000000^3233 ≤ 8778298158237^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675309021 5000000000 8778298158237 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239871177/10000000000 : ℝ)^4257 ≤ (42699225014939/100000000000000 : ℝ)^3233 := by
    have hnat : (5239871177 : ℕ)^4257*100000000000000^3233 ≤ 42699225014939^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239871177 10000000000 42699225014939 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135888849/625000000 : ℝ)^4257 ≤ (3352321046107/25000000000000 : ℝ)^3233 := by
    have hnat : (135888849 : ℕ)^4257*25000000000000^3233 ≤ 3352321046107^3233*625000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135888849 625000000 3352321046107 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675309021/5000000000 : ℝ), (5239871177/10000000000 : ℝ), (-135888849/625000000 : ℝ)] ![(8778298158237/20000000000000 : ℝ), (42699225014939/100000000000000 : ℝ), (3352321046107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675309021/5000000000 : ℝ)|^4257 ≤ (8778298158237/20000000000000 : ℝ)^3233
        have hw : |(2675309021/5000000000 : ℝ)|=(2675309021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239871177/10000000000 : ℝ)|^4257 ≤ (42699225014939/100000000000000 : ℝ)^3233
        have hw : |(5239871177/10000000000 : ℝ)|=(5239871177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135888849/625000000 : ℝ)|^4257 ≤ (3352321046107/25000000000000 : ℝ)^3233
        have hw : |(-135888849/625000000 : ℝ)|=(135888849/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s4_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4338277827/10000000000 : ℝ)*x 0 + (1039508393/2500000000 : ℝ)*x 1 + (2262980427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338277827/10000000000 : ℝ)^4257 ≤ (8324986952967/25000000000000 : ℝ)^3233 := by
    have hnat : (4338277827 : ℕ)^4257*25000000000000^3233 ≤ 8324986952967^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338277827 10000000000 8324986952967 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039508393/2500000000 : ℝ)^4257 ≤ (15745156635169/50000000000000 : ℝ)^3233 := by
    have hnat : (1039508393 : ℕ)^4257*50000000000000^3233 ≤ 15745156635169^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039508393 2500000000 15745156635169 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262980427/5000000000 : ℝ)^4257 ≤ (137538042589/390625000000 : ℝ)^3233 := by
    have hnat : (2262980427 : ℕ)^4257*390625000000^3233 ≤ 137538042589^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262980427 5000000000 137538042589 390625000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338277827/10000000000 : ℝ), (1039508393/2500000000 : ℝ), (2262980427/5000000000 : ℝ)] ![(8324986952967/25000000000000 : ℝ), (15745156635169/50000000000000 : ℝ), (137538042589/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338277827/10000000000 : ℝ)|^4257 ≤ (8324986952967/25000000000000 : ℝ)^3233
        have hw : |(4338277827/10000000000 : ℝ)|=(4338277827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039508393/2500000000 : ℝ)|^4257 ≤ (15745156635169/50000000000000 : ℝ)^3233
        have hw : |(1039508393/2500000000 : ℝ)|=(1039508393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262980427/5000000000 : ℝ)|^4257 ≤ (137538042589/390625000000 : ℝ)^3233
        have hw : |(2262980427/5000000000 : ℝ)|=(2262980427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s4_4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083090551/10000000000 : ℝ)*x 0 + (1048106743/2000000000 : ℝ)*x 1 + (5417883063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083090551/10000000000 : ℝ)^4257 ≤ (3168546462291/25000000000000 : ℝ)^3233 := by
    have hnat : (2083090551 : ℕ)^4257*25000000000000^3233 ≤ 3168546462291^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083090551 10000000000 3168546462291 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048106743/2000000000 : ℝ)^4257 ≤ (8541266830169/20000000000000 : ℝ)^3233 := by
    have hnat : (1048106743 : ℕ)^4257*20000000000000^3233 ≤ 8541266830169^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048106743 2000000000 8541266830169 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417883063/10000000000 : ℝ)^4257 ≤ (44619479980361/100000000000000 : ℝ)^3233 := by
    have hnat : (5417883063 : ℕ)^4257*100000000000000^3233 ≤ 44619479980361^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417883063 10000000000 44619479980361 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083090551/10000000000 : ℝ), (1048106743/2000000000 : ℝ), (5417883063/10000000000 : ℝ)] ![(3168546462291/25000000000000 : ℝ), (8541266830169/20000000000000 : ℝ), (44619479980361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083090551/10000000000 : ℝ)|^4257 ≤ (3168546462291/25000000000000 : ℝ)^3233
        have hw : |(-2083090551/10000000000 : ℝ)|=(2083090551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048106743/2000000000 : ℝ)|^4257 ≤ (8541266830169/20000000000000 : ℝ)^3233
        have hw : |(1048106743/2000000000 : ℝ)|=(1048106743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417883063/10000000000 : ℝ)|^4257 ≤ (44619479980361/100000000000000 : ℝ)^3233
        have hw : |(5417883063/10000000000 : ℝ)|=(5417883063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s4_5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652421523/5000000000 : ℝ)*x 0 + (-998104777/5000000000 : ℝ)*x 1 + (5417882931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652421523/5000000000 : ℝ)^4257 ≤ (21698867221977/50000000000000 : ℝ)^3233 := by
    have hnat : (2652421523 : ℕ)^4257*50000000000000^3233 ≤ 21698867221977^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652421523 5000000000 21698867221977 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998104777/5000000000 : ℝ)^4257 ≤ (599139349689/5000000000000 : ℝ)^3233 := by
    have hnat : (998104777 : ℕ)^4257*5000000000000^3233 ≤ 599139349689^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998104777 5000000000 599139349689 5000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417882931/10000000000 : ℝ)^4257 ≤ (22309739274471/50000000000000 : ℝ)^3233 := by
    have hnat : (5417882931 : ℕ)^4257*50000000000000^3233 ≤ 22309739274471^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417882931 10000000000 22309739274471 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652421523/5000000000 : ℝ), (-998104777/5000000000 : ℝ), (5417882931/10000000000 : ℝ)] ![(21698867221977/50000000000000 : ℝ), (599139349689/5000000000000 : ℝ), (22309739274471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652421523/5000000000 : ℝ)|^4257 ≤ (21698867221977/50000000000000 : ℝ)^3233
        have hw : |(2652421523/5000000000 : ℝ)|=(2652421523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-998104777/5000000000 : ℝ)|^4257 ≤ (599139349689/5000000000000 : ℝ)^3233
        have hw : |(-998104777/5000000000 : ℝ)|=(998104777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417882931/10000000000 : ℝ)|^4257 ≤ (22309739274471/50000000000000 : ℝ)^3233
        have hw : |(5417882931/10000000000 : ℝ)|=(5417882931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s4_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304842699/10000000000 : ℝ)*x 0 + (338617707/625000000 : ℝ)*x 1 + (-399241901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304842699/10000000000 : ℝ)^4257 ≤ (43397730706103/100000000000000 : ℝ)^3233 := by
    have hnat : (5304842699 : ℕ)^4257*100000000000000^3233 ≤ 43397730706103^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304842699 10000000000 43397730706103 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338617707/625000000 : ℝ)^4257 ≤ (22309741340269/50000000000000 : ℝ)^3233 := by
    have hnat : (338617707 : ℕ)^4257*50000000000000^3233 ≤ 22309741340269^3233*625000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338617707 625000000 22309741340269 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399241901/2000000000 : ℝ)^4257 ≤ (11982786606481/100000000000000 : ℝ)^3233 := by
    have hnat : (399241901 : ℕ)^4257*100000000000000^3233 ≤ 11982786606481^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399241901 2000000000 11982786606481 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304842699/10000000000 : ℝ), (338617707/625000000 : ℝ), (-399241901/2000000000 : ℝ)] ![(43397730706103/100000000000000 : ℝ), (22309741340269/50000000000000 : ℝ), (11982786606481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304842699/10000000000 : ℝ)|^4257 ≤ (43397730706103/100000000000000 : ℝ)^3233
        have hw : |(5304842699/10000000000 : ℝ)|=(5304842699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338617707/625000000 : ℝ)|^4257 ≤ (22309741340269/50000000000000 : ℝ)^3233
        have hw : |(338617707/625000000 : ℝ)|=(338617707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-399241901/2000000000 : ℝ)|^4257 ≤ (11982786606481/100000000000000 : ℝ)^3233
        have hw : |(-399241901/2000000000 : ℝ)|=(399241901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s4_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4338306997/10000000000 : ℝ)*x 0 + (4524596929/10000000000 : ℝ)*x 1 + (2079702459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338306997/10000000000 : ℝ)^4257 ≤ (16650121317321/50000000000000 : ℝ)^3233 := by
    have hnat : (4338306997 : ℕ)^4257*50000000000000^3233 ≤ 16650121317321^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338306997 10000000000 16650121317321 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524596929/10000000000 : ℝ)^4257 ≤ (8798942038221/25000000000000 : ℝ)^3233 := by
    have hnat : (4524596929 : ℕ)^4257*25000000000000^3233 ≤ 8798942038221^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524596929 10000000000 8798942038221 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079702459/5000000000 : ℝ)^4257 ≤ (196899932461/625000000000 : ℝ)^3233 := by
    have hnat : (2079702459 : ℕ)^4257*625000000000^3233 ≤ 196899932461^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079702459 5000000000 196899932461 625000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338306997/10000000000 : ℝ), (4524596929/10000000000 : ℝ), (2079702459/5000000000 : ℝ)] ![(16650121317321/50000000000000 : ℝ), (8798942038221/25000000000000 : ℝ), (196899932461/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338306997/10000000000 : ℝ)|^4257 ≤ (16650121317321/50000000000000 : ℝ)^3233
        have hw : |(4338306997/10000000000 : ℝ)|=(4338306997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524596929/10000000000 : ℝ)|^4257 ≤ (8798942038221/25000000000000 : ℝ)^3233
        have hw : |(4524596929/10000000000 : ℝ)|=(4524596929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2079702459/5000000000 : ℝ)|^4257 ≤ (196899932461/625000000000 : ℝ)^3233
        have hw : |(2079702459/5000000000 : ℝ)|=(2079702459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1297_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (753/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (1097/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (753/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (267/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (753/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (267/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (753/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (267/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (753/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (267/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (753/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (267/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (753/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (267/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (267/2500 : ℝ) ^ (133/32 : ℝ) ≤ (9172743914487653/100000000000000000000 : ℝ) := by
    have hpowers : (267/2500 : ℝ)^133 ≤ (9172743914487653/100000000000000000000 : ℝ)^32 := by
      have hnat : (267 : ℕ)^133*100000000000000000000^32 ≤ 9172743914487653^32*2500^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        267 2500 9172743914487653 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (267/2500 : ℝ)) (X := (9172743914487653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hpowhi : (753/5000 : ℝ) ^ (133/32 : ℝ) ≤ (38267936030265047/100000000000000000000 : ℝ) := by
    have hpowers : (753/5000 : ℝ)^133 ≤ (38267936030265047/100000000000000000000 : ℝ)^32 := by
      have hnat : (753 : ℕ)^133*100000000000000000000^32 ≤ 38267936030265047^32*5000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        753 5000 38267936030265047 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (753/5000 : ℝ)) (X := (38267936030265047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009172743914487653/50000000000000000000 : ℝ) ≤ (2500110341113157/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50009172743914487653/50000000000000000000 : ℝ)^32 ≤ (2500110341113157/2500000000000000 : ℝ)^133 := by
      have hnat : (50009172743914487653 : ℕ)^32*2500000000000000^133 ≤ 2500110341113157^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009172743914487653 50000000000000000000 2500110341113157 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500110341113157/2500000000000000 : ℝ)) (X := (50009172743914487653/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000474406799447527/1000000000000000000 : ℝ) ≤ (10001141224342653/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (1000474406799447527/1000000000000000000 : ℝ)^32 ≤ (10001141224342653/10000000000000000 : ℝ)^133 := by
      have hnat : (1000474406799447527 : ℕ)^32*10000000000000000^133 ≤ 10001141224342653^133*1000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000474406799447527 1000000000000000000 10001141224342653 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001141224342653/10000000000000000 : ℝ)) (X := (1000474406799447527/1000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038267936030265047/50000000000000000000 : ℝ) ≤ (5000920542116339/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50038267936030265047/50000000000000000000 : ℝ)^32 ≤ (5000920542116339/5000000000000000 : ℝ)^133 := by
      have hnat : (50038267936030265047 : ℕ)^32*5000000000000000^133 ≤ 5000920542116339^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038267936030265047 50000000000000000000 5000920542116339 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000920542116339/5000000000000000 : ℝ)) (X := (50038267936030265047/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9172743914487653/100000000000000000000 : ℝ) ≤ ((45611441842762059/45625000000000000 : ℝ)+2*(27994395601/17520000000000 : ℝ)*(267/2500 : ℝ))^(133/32 : ℝ) := by
    rw [show (45611441842762059/45625000000000000 : ℝ)+2*(27994395601/17520000000000 : ℝ)*(267/2500 : ℝ)=(2500110341113157/2500000000000000 : ℝ) by norm_num, show 1+2*(9172743914487653/100000000000000000000 : ℝ)=(50009172743914487653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38267936030265047/100000000000000000000 : ℝ)+(9172743914487653/100000000000000000000 : ℝ) ≤ ((45611441842762059/45625000000000000 : ℝ)+(27994395601/17520000000000 : ℝ)*((753/5000 : ℝ)+(267/2500 : ℝ)))^(133/32 : ℝ) := by
    rw [show (45611441842762059/45625000000000000 : ℝ)+(27994395601/17520000000000 : ℝ)*((753/5000 : ℝ)+(267/2500 : ℝ))=(10001141224342653/10000000000000000 : ℝ) by norm_num, show 1+(38267936030265047/100000000000000000000 : ℝ)+(9172743914487653/100000000000000000000 : ℝ)=(1000474406799447527/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38267936030265047/100000000000000000000 : ℝ) ≤ ((45611441842762059/45625000000000000 : ℝ)+2*(27994395601/17520000000000 : ℝ)*(753/5000 : ℝ))^(133/32 : ℝ) := by
    rw [show (45611441842762059/45625000000000000 : ℝ)+2*(27994395601/17520000000000 : ℝ)*(753/5000 : ℝ)=(5000920542116339/5000000000000000 : ℝ) by norm_num, show 1+2*(38267936030265047/100000000000000000000 : ℝ)=(50038267936030265047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45611441842762059/45625000000000000 : ℝ)*(X 1 0+X 2 0)+(27994395601/17520000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (267/2500 : ℝ)) (hi := (753/5000 : ℝ)) (c := (45611441842762059/45625000000000000 : ℝ)) (alpha := (27994395601/17520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45611441842762059/45625000000000000 : ℝ)*(X 0 1+X 2 1)+(27994395601/17520000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (267/2500 : ℝ)) (hi := (753/5000 : ℝ)) (c := (45611441842762059/45625000000000000 : ℝ)) (alpha := (27994395601/17520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45611441842762059/45625000000000000 : ℝ)*(X 0 2+X 1 2)+(27994395601/17520000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (267/2500 : ℝ)) (hi := (753/5000 : ℝ)) (c := (45611441842762059/45625000000000000 : ℝ)) (alpha := (27994395601/17520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-32548067/156250000 : ℝ)*X 0 0+(169329661/312500000 : ℝ)*X 0 1+(523987119/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070123601/2000000000 : ℝ)*X 1 0+(-217422157/1000000000 : ℝ)*X 1 1+(654983903/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675309021/5000000000 : ℝ)*X 2 0+(5239871177/10000000000 : ℝ)*X 2 1+(-135888849/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4338277827/10000000000 : ℝ)*X 0 0+(1039508393/2500000000 : ℝ)*X 0 1+(2262980427/5000000000 : ℝ)*X 0 2+(4338277827/10000000000 : ℝ)*X 1 0+(1039508393/2500000000 : ℝ)*X 1 1+(2262980427/5000000000 : ℝ)*X 1 2+(4338277827/10000000000 : ℝ)*X 2 0+(1039508393/2500000000 : ℝ)*X 2 1+(2262980427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2083090551/10000000000 : ℝ)*X 0 0+(1048106743/2000000000 : ℝ)*X 0 1+(5417883063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652421523/5000000000 : ℝ)*X 1 0+(-998104777/5000000000 : ℝ)*X 1 1+(5417882931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304842699/10000000000 : ℝ)*X 2 0+(338617707/625000000 : ℝ)*X 2 1+(-399241901/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4338306997/10000000000 : ℝ)*X 0 0+(4524596929/10000000000 : ℝ)*X 0 1+(2079702459/5000000000 : ℝ)*X 0 2+(4338306997/10000000000 : ℝ)*X 1 0+(4524596929/10000000000 : ℝ)*X 1 1+(2079702459/5000000000 : ℝ)*X 1 2+(4338306997/10000000000 : ℝ)*X 2 0+(4524596929/10000000000 : ℝ)*X 2 1+(2079702459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89991677821621486899/29200000000000000000000000 : ℝ) := by norm_num
    linear_combination (309797371/50000000000000 : ℝ)*(base19) + (539598963/100000000000000 : ℝ)*(base23) + (63510423/100000000000000 : ℝ)*(lower2) + (27090697/25000000000000 : ℝ)*(upper3) + (1356047/12500000000000 : ℝ)*(upper5) + (2078656587513507/50000000000000 : ℝ)*(major0) + (2078656587513507/50000000000000 : ℝ)*(major1) + (831462635005403/20000000000000 : ℝ)*(major2) + (5596674421817227/100000000000000 : ℝ)*(sp0) + (1119337070414233/20000000000000 : ℝ)*(sp1) + (43724104938023/781250000000 : ℝ)*(sp2) + (1358966658775011/50000000000000 : ℝ)*(sp3) + (288746217/2500000000000 : ℝ)*(sp4) + (6958107869/100000000000000 : ℝ)*(sp7) + (2717940275657891/100000000000000 : ℝ)*(f.failure) + (5596685971665907/100000000000000 : ℝ)*(f.sum) + (4120279276117/1752000000000000000000000000 : ℝ)*base65 + (115287825087555331/27375000000000000000000000000000 : ℝ)*base67 + (906204800403951/456250000000000000000000000000 : ℝ)*base69 + (171662039192069669/27375000000000000000000000000000 : ℝ)*base72 + (4162227672491/1752000000000000000000000000 : ℝ)*base74 + (2513735238783549/456250000000000000000000000000 : ℝ)*base76 + (33239565495339951/4562500000000000000000000000000 : ℝ)*base77 + (3907947871785049/4562500000000000000000000000000 : ℝ)*base80 + (140438723881/29200000000000000000000000 : ℝ)*base81 + (2434099/625000000000000000000 : ℝ)*base89 + (2434099/625000000000000000000 : ℝ)*base91 + (3815901/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101010410476950546879/14600000000000000000000000 : ℝ) := by norm_num
    linear_combination (831642809/50000000000000 : ℝ)*(base19) + (702287039/50000000000000 : ℝ)*(base23) + (9594601/5000000000000 : ℝ)*(upper3) + (35733801/100000000000000 : ℝ)*(lower4) + (16198889/25000000000000 : ℝ)*(upper5) + (104710838509917/2500000000000 : ℝ)*(major0) + (104710838509917/2500000000000 : ℝ)*(major1) + (104710838509917/2500000000000 : ℝ)*(major2) + (2785298017/10000000000000 : ℝ)*(sp1) + (32807924493/100000000000000 : ℝ)*(sp2) + (2819290455568193/50000000000000 : ℝ)*(sp4) + (2819275697435299/50000000000000 : ℝ)*(sp5) + (704818337329727/12500000000000 : ℝ)*(sp6) + (273828593903959/10000000000000 : ℝ)*(sp7) + (273828593903959/10000000000000 : ℝ)*(f.failure) + (2819290455568193/50000000000000 : ℝ)*(f.sum) + (211869652339/36500000000000000000000000 : ℝ)*base65 + (890231000975081/228125000000000000000000000000 : ℝ)*base67 + (699221002693669/228125000000000000000000000000 : ℝ)*base70 + (128872827150081/228125000000000000000000000000 : ℝ)*base71 + (485258349/71289062500000000000000 : ℝ)*base73 + (329358008243831/228125000000000000000000000000 : ℝ)*base75 + (2584054855462419/228125000000000000000000000000 : ℝ)*base78 + (1232209019823397/114062500000000000000000000000 : ℝ)*base80 + (260776619773/36500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (299449/62500000000000000000 : ℝ)*base90 + (299449/62500000000000000000 : ℝ)*base92 + (299449/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1297_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (753/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (267/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1297_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1297_s5_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083422711/10000000000 : ℝ)*x 0 + (5415605163/10000000000 : ℝ)*x 1 + (2621293737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083422711/10000000000 : ℝ)^4257 ≤ (12676846991879/100000000000000 : ℝ)^3233 := by
    have hnat : (2083422711 : ℕ)^4257*100000000000000^3233 ≤ 12676846991879^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083422711 10000000000 12676846991879 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415605163/10000000000 : ℝ)^4257 ≤ (2787173743073/6250000000000 : ℝ)^3233 := by
    have hnat : (5415605163 : ℕ)^4257*6250000000000^3233 ≤ 2787173743073^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415605163 10000000000 2787173743073 6250000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621293737/5000000000 : ℝ)^4257 ≤ (42728373113569/100000000000000 : ℝ)^3233 := by
    have hnat : (2621293737 : ℕ)^4257*100000000000000^3233 ≤ 42728373113569^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621293737 5000000000 42728373113569 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083422711/10000000000 : ℝ), (5415605163/10000000000 : ℝ), (2621293737/5000000000 : ℝ)] ![(12676846991879/100000000000000 : ℝ), (2787173743073/6250000000000 : ℝ), (42728373113569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083422711/10000000000 : ℝ)|^4257 ≤ (12676846991879/100000000000000 : ℝ)^3233
        have hw : |(-2083422711/10000000000 : ℝ)|=(2083422711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415605163/10000000000 : ℝ)|^4257 ≤ (2787173743073/6250000000000 : ℝ)^3233
        have hw : |(5415605163/10000000000 : ℝ)|=(5415605163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621293737/5000000000 : ℝ)|^4257 ≤ (42728373113569/100000000000000 : ℝ)^3233
        have hw : |(2621293737/5000000000 : ℝ)|=(2621293737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s5_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349871019/10000000000 : ℝ)*x 0 + (-67863293/312500000 : ℝ)*x 1 + (262129373/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349871019/10000000000 : ℝ)^4257 ≤ (21941711090829/50000000000000 : ℝ)^3233 := by
    have hnat : (5349871019 : ℕ)^4257*50000000000000^3233 ≤ 21941711090829^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349871019 10000000000 21941711090829 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67863293/312500000 : ℝ)^4257 ≤ (2677640968343/20000000000000 : ℝ)^3233 := by
    have hnat : (67863293 : ℕ)^4257*20000000000000^3233 ≤ 2677640968343^3233*312500000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67863293 312500000 2677640968343 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262129373/500000000 : ℝ)^4257 ≤ (1709134918533/4000000000000 : ℝ)^3233 := by
    have hnat : (262129373 : ℕ)^4257*4000000000000^3233 ≤ 1709134918533^3233*500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262129373 500000000 1709134918533 4000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349871019/10000000000 : ℝ), (-67863293/312500000 : ℝ), (262129373/500000000 : ℝ)] ![(21941711090829/50000000000000 : ℝ), (2677640968343/20000000000000 : ℝ), (1709134918533/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349871019/10000000000 : ℝ)|^4257 ≤ (21941711090829/50000000000000 : ℝ)^3233
        have hw : |(5349871019/10000000000 : ℝ)|=(5349871019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67863293/312500000 : ℝ)|^4257 ≤ (2677640968343/20000000000000 : ℝ)^3233
        have hw : |(-67863293/312500000 : ℝ)|=(67863293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262129373/500000000 : ℝ)|^4257 ≤ (1709134918533/4000000000000 : ℝ)^3233
        have hw : |(262129373/500000000 : ℝ)|=(262129373/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s5_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349871067/10000000000 : ℝ)*x 0 + (1310646859/2500000000 : ℝ)*x 1 + (-16965823/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349871067/10000000000 : ℝ)^4257 ≤ (685678479689/1562500000000 : ℝ)^3233 := by
    have hnat : (5349871067 : ℕ)^4257*1562500000000^3233 ≤ 685678479689^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349871067 10000000000 685678479689 1562500000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310646859/2500000000 : ℝ)^4257 ≤ (8545674541153/20000000000000 : ℝ)^3233 := by
    have hnat : (1310646859 : ℕ)^4257*20000000000000^3233 ≤ 8545674541153^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310646859 2500000000 8545674541153 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16965823/78125000 : ℝ)^4257 ≤ (13388204581947/100000000000000 : ℝ)^3233 := by
    have hnat : (16965823 : ℕ)^4257*100000000000000^3233 ≤ 13388204581947^3233*78125000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16965823 78125000 13388204581947 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349871067/10000000000 : ℝ), (1310646859/2500000000 : ℝ), (-16965823/78125000 : ℝ)] ![(685678479689/1562500000000 : ℝ), (8545674541153/20000000000000 : ℝ), (13388204581947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349871067/10000000000 : ℝ)|^4257 ≤ (685678479689/1562500000000 : ℝ)^3233
        have hw : |(5349871067/10000000000 : ℝ)|=(5349871067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310646859/2500000000 : ℝ)|^4257 ≤ (8545674541153/20000000000000 : ℝ)^3233
        have hw : |(1310646859/2500000000 : ℝ)|=(1310646859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16965823/78125000 : ℝ)|^4257 ≤ (13388204581947/100000000000000 : ℝ)^3233
        have hw : |(-16965823/78125000 : ℝ)|=(16965823/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s5_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1084620877/2500000000 : ℝ)*x 0 + (4163835339/10000000000 : ℝ)*x 1 + (4520107431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084620877/2500000000 : ℝ)^4257 ≤ (16651013327151/50000000000000 : ℝ)^3233 := by
    have hnat : (1084620877 : ℕ)^4257*50000000000000^3233 ≤ 16651013327151^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084620877 2500000000 16651013327151 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4163835339/10000000000 : ℝ)^4257 ≤ (15774090946401/50000000000000 : ℝ)^3233 := by
    have hnat : (4163835339 : ℕ)^4257*50000000000000^3233 ≤ 15774090946401^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163835339 10000000000 15774090946401 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520107431/10000000000 : ℝ)^4257 ≤ (8787447857443/25000000000000 : ℝ)^3233 := by
    have hnat : (4520107431 : ℕ)^4257*25000000000000^3233 ≤ 8787447857443^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520107431 10000000000 8787447857443 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084620877/2500000000 : ℝ), (4163835339/10000000000 : ℝ), (4520107431/10000000000 : ℝ)] ![(16651013327151/50000000000000 : ℝ), (15774090946401/50000000000000 : ℝ), (8787447857443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084620877/2500000000 : ℝ)|^4257 ≤ (16651013327151/50000000000000 : ℝ)^3233
        have hw : |(1084620877/2500000000 : ℝ)|=(1084620877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4163835339/10000000000 : ℝ)|^4257 ≤ (15774090946401/50000000000000 : ℝ)^3233
        have hw : |(4163835339/10000000000 : ℝ)|=(4163835339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520107431/10000000000 : ℝ)|^4257 ≤ (8787447857443/25000000000000 : ℝ)^3233
        have hw : |(4520107431/10000000000 : ℝ)|=(4520107431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s5_4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083435631/10000000000 : ℝ)*x 0 + (1310802167/2500000000 : ℝ)*x 1 + (2707490377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083435631/10000000000 : ℝ)^4257 ≤ (6338475252421/50000000000000 : ℝ)^3233 := by
    have hnat : (2083435631 : ℕ)^4257*50000000000000^3233 ≤ 6338475252421^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083435631 10000000000 6338475252421 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310802167/2500000000 : ℝ)^4257 ≤ (170940158831/400000000000 : ℝ)^3233 := by
    have hnat : (1310802167 : ℕ)^4257*400000000000^3233 ≤ 170940158831^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310802167 2500000000 170940158831 400000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707490377/5000000000 : ℝ)^4257 ≤ (11147002442939/25000000000000 : ℝ)^3233 := by
    have hnat : (2707490377 : ℕ)^4257*25000000000000^3233 ≤ 11147002442939^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707490377 5000000000 11147002442939 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083435631/10000000000 : ℝ), (1310802167/2500000000 : ℝ), (2707490377/5000000000 : ℝ)] ![(6338475252421/50000000000000 : ℝ), (170940158831/400000000000 : ℝ), (11147002442939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083435631/10000000000 : ℝ)|^4257 ≤ (6338475252421/50000000000000 : ℝ)^3233
        have hw : |(-2083435631/10000000000 : ℝ)|=(2083435631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310802167/2500000000 : ℝ)|^4257 ≤ (170940158831/400000000000 : ℝ)^3233
        have hw : |(1310802167/2500000000 : ℝ)|=(1310802167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707490377/5000000000 : ℝ)|^4257 ≤ (11147002442939/25000000000000 : ℝ)^3233
        have hw : |(2707490377/5000000000 : ℝ)|=(2707490377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s5_5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305546061/10000000000 : ℝ)*x 0 + (-1999232059/10000000000 : ℝ)*x 1 + (5414980759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305546061/10000000000 : ℝ)^4257 ≤ (21702653706401/50000000000000 : ℝ)^3233 := by
    have hnat : (5305546061 : ℕ)^4257*50000000000000^3233 ≤ 21702653706401^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305546061 10000000000 21702653706401 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1999232059/10000000000 : ℝ)^4257 ≤ (2401336549931/20000000000000 : ℝ)^3233 := by
    have hnat : (1999232059 : ℕ)^4257*20000000000000^3233 ≤ 2401336549931^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999232059 10000000000 2401336549931 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414980759/10000000000 : ℝ)^4257 ≤ (44588009825967/100000000000000 : ℝ)^3233 := by
    have hnat : (5414980759 : ℕ)^4257*100000000000000^3233 ≤ 44588009825967^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414980759 10000000000 44588009825967 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305546061/10000000000 : ℝ), (-1999232059/10000000000 : ℝ), (5414980759/10000000000 : ℝ)] ![(21702653706401/50000000000000 : ℝ), (2401336549931/20000000000000 : ℝ), (44588009825967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305546061/10000000000 : ℝ)|^4257 ≤ (21702653706401/50000000000000 : ℝ)^3233
        have hw : |(5305546061/10000000000 : ℝ)|=(5305546061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1999232059/10000000000 : ℝ)|^4257 ≤ (2401336549931/20000000000000 : ℝ)^3233
        have hw : |(-1999232059/10000000000 : ℝ)|=(1999232059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414980759/10000000000 : ℝ)|^4257 ≤ (44588009825967/100000000000000 : ℝ)^3233
        have hw : |(5414980759/10000000000 : ℝ)|=(5414980759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s5_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305546077/10000000000 : ℝ)*x 0 + (1082996149/2000000000 : ℝ)*x 1 + (-1999232057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305546077/10000000000 : ℝ)^4257 ≤ (1085132689629/2500000000000 : ℝ)^3233 := by
    have hnat : (5305546077 : ℕ)^4257*2500000000000^3233 ≤ 1085132689629^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305546077 10000000000 1085132689629 2500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082996149/2000000000 : ℝ)^4257 ≤ (696687651159/1562500000000 : ℝ)^3233 := by
    have hnat : (1082996149 : ℕ)^4257*1562500000000^3233 ≤ 696687651159^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082996149 2000000000 696687651159 1562500000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999232057/10000000000 : ℝ)^4257 ≤ (12006682733839/100000000000000 : ℝ)^3233 := by
    have hnat : (1999232057 : ℕ)^4257*100000000000000^3233 ≤ 12006682733839^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999232057 10000000000 12006682733839 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305546077/10000000000 : ℝ), (1082996149/2000000000 : ℝ), (-1999232057/10000000000 : ℝ)] ![(1085132689629/2500000000000 : ℝ), (696687651159/1562500000000 : ℝ), (12006682733839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305546077/10000000000 : ℝ)|^4257 ≤ (1085132689629/2500000000000 : ℝ)^3233
        have hw : |(5305546077/10000000000 : ℝ)|=(5305546077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082996149/2000000000 : ℝ)|^4257 ≤ (696687651159/1562500000000 : ℝ)^3233
        have hw : |(1082996149/2000000000 : ℝ)|=(1082996149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1999232057/10000000000 : ℝ)|^4257 ≤ (12006682733839/100000000000000 : ℝ)^3233
        have hw : |(-1999232057/10000000000 : ℝ)|=(1999232057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s5_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2169255089/5000000000 : ℝ)*x 0 + (4518828151/10000000000 : ℝ)*x 1 + (4165121181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169255089/5000000000 : ℝ)^4257 ≤ (4162787026683/12500000000000 : ℝ)^3233 := by
    have hnat : (2169255089 : ℕ)^4257*12500000000000^3233 ≤ 4162787026683^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169255089 5000000000 4162787026683 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518828151/10000000000 : ℝ)^4257 ≤ (17568346517371/50000000000000 : ℝ)^3233 := by
    have hnat : (4518828151 : ℕ)^4257*50000000000000^3233 ≤ 17568346517371^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518828151 10000000000 17568346517371 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4165121181/10000000000 : ℝ)^4257 ≤ (15780505369219/50000000000000 : ℝ)^3233 := by
    have hnat : (4165121181 : ℕ)^4257*50000000000000^3233 ≤ 15780505369219^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165121181 10000000000 15780505369219 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169255089/5000000000 : ℝ), (4518828151/10000000000 : ℝ), (4165121181/10000000000 : ℝ)] ![(4162787026683/12500000000000 : ℝ), (17568346517371/50000000000000 : ℝ), (15780505369219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169255089/5000000000 : ℝ)|^4257 ≤ (4162787026683/12500000000000 : ℝ)^3233
        have hw : |(2169255089/5000000000 : ℝ)|=(2169255089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518828151/10000000000 : ℝ)|^4257 ≤ (17568346517371/50000000000000 : ℝ)^3233
        have hw : |(4518828151/10000000000 : ℝ)|=(4518828151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4165121181/10000000000 : ℝ)|^4257 ≤ (15780505369219/50000000000000 : ℝ)^3233
        have hw : |(4165121181/10000000000 : ℝ)|=(4165121181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1297_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2757/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14689/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1097/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1097/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1097/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1097/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1097/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1097/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1097/10000 : ℝ) ^ (133/32 : ℝ) ≤ (5126592527881019/50000000000000000000 : ℝ) := by
    have hpowers : (1097/10000 : ℝ)^133 ≤ (5126592527881019/50000000000000000000 : ℝ)^32 := by
      have hnat : (1097 : ℕ)^133*50000000000000000000^32 ≤ 5126592527881019^32*10000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1097 10000 5126592527881019 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1097/10000 : ℝ)) (X := (5126592527881019/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (133/32 : ℝ) ≤ (35108656092692507/100000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^133 ≤ (35108656092692507/100000000000000000000 : ℝ)^32 := by
      have hnat : (14751 : ℕ)^133*100000000000000000000^32 ≤ 35108656092692507^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 35108656092692507 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (35108656092692507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005126592527881019/25000000000000000000 : ℝ) ≤ (10000493347936857/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25005126592527881019/25000000000000000000 : ℝ)^32 ≤ (10000493347936857/10000000000000000 : ℝ)^133 := by
      have hnat : (25005126592527881019 : ℕ)^32*10000000000000000^133 ≤ 10000493347936857^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005126592527881019 25000000000000000000 10000493347936857 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000493347936857/10000000000000000 : ℝ)) (X := (25005126592527881019/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009072368229690909/20000000000000000000 : ℝ) ≤ (1000109122478599/1000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (20009072368229690909/20000000000000000000 : ℝ)^32 ≤ (1000109122478599/1000000000000000 : ℝ)^133 := by
      have hnat : (20009072368229690909 : ℕ)^32*1000000000000000^133 ≤ 1000109122478599^133*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009072368229690909 20000000000000000000 1000109122478599 1000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000109122478599/1000000000000000 : ℝ)) (X := (20009072368229690909/20000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035108656092692507/50000000000000000000 : ℝ) ≤ (10001689101635123/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50035108656092692507/50000000000000000000 : ℝ)^32 ≤ (10001689101635123/10000000000000000 : ℝ)^133 := by
      have hnat : (50035108656092692507 : ℕ)^32*10000000000000000^133 ≤ 10001689101635123^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035108656092692507 50000000000000000000 10001689101635123 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001689101635123/10000000000000000 : ℝ)) (X := (50035108656092692507/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5126592527881019/50000000000000000000 : ℝ) ≤ ((37798747930479278297/37810000000000000000 : ℝ)+2*(597876849133/378100000000000 : ℝ)*(1097/10000 : ℝ))^(133/32 : ℝ) := by
    rw [show (37798747930479278297/37810000000000000000 : ℝ)+2*(597876849133/378100000000000 : ℝ)*(1097/10000 : ℝ)=(10000493347936857/10000000000000000 : ℝ) by norm_num, show 1+2*(5126592527881019/50000000000000000000 : ℝ)=(25005126592527881019/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35108656092692507/100000000000000000000 : ℝ)+(5126592527881019/50000000000000000000 : ℝ) ≤ ((37798747930479278297/37810000000000000000 : ℝ)+(597876849133/378100000000000 : ℝ)*((14751/100000 : ℝ)+(1097/10000 : ℝ)))^(133/32 : ℝ) := by
    rw [show (37798747930479278297/37810000000000000000 : ℝ)+(597876849133/378100000000000 : ℝ)*((14751/100000 : ℝ)+(1097/10000 : ℝ))=(1000109122478599/1000000000000000 : ℝ) by norm_num, show 1+(35108656092692507/100000000000000000000 : ℝ)+(5126592527881019/50000000000000000000 : ℝ)=(20009072368229690909/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35108656092692507/100000000000000000000 : ℝ) ≤ ((37798747930479278297/37810000000000000000 : ℝ)+2*(597876849133/378100000000000 : ℝ)*(14751/100000 : ℝ))^(133/32 : ℝ) := by
    rw [show (37798747930479278297/37810000000000000000 : ℝ)+2*(597876849133/378100000000000 : ℝ)*(14751/100000 : ℝ)=(10001689101635123/10000000000000000 : ℝ) by norm_num, show 1+2*(35108656092692507/100000000000000000000 : ℝ)=(50035108656092692507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37798747930479278297/37810000000000000000 : ℝ)*(X 1 0+X 2 0)+(597876849133/378100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (37798747930479278297/37810000000000000000 : ℝ)) (alpha := (597876849133/378100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37798747930479278297/37810000000000000000 : ℝ)*(X 0 1+X 2 1)+(597876849133/378100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (37798747930479278297/37810000000000000000 : ℝ)) (alpha := (597876849133/378100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37798747930479278297/37810000000000000000 : ℝ)*(X 0 2+X 1 2)+(597876849133/378100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (37798747930479278297/37810000000000000000 : ℝ)) (alpha := (597876849133/378100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2083422711/10000000000 : ℝ)*X 0 0+(5415605163/10000000000 : ℝ)*X 0 1+(2621293737/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349871019/10000000000 : ℝ)*X 1 0+(-67863293/312500000 : ℝ)*X 1 1+(262129373/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349871067/10000000000 : ℝ)*X 2 0+(1310646859/2500000000 : ℝ)*X 2 1+(-16965823/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1084620877/2500000000 : ℝ)*X 0 0+(4163835339/10000000000 : ℝ)*X 0 1+(4520107431/10000000000 : ℝ)*X 0 2+(1084620877/2500000000 : ℝ)*X 1 0+(4163835339/10000000000 : ℝ)*X 1 1+(4520107431/10000000000 : ℝ)*X 1 2+(1084620877/2500000000 : ℝ)*X 2 0+(4163835339/10000000000 : ℝ)*X 2 1+(4520107431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2083435631/10000000000 : ℝ)*X 0 0+(1310802167/2500000000 : ℝ)*X 0 1+(2707490377/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305546061/10000000000 : ℝ)*X 1 0+(-1999232059/10000000000 : ℝ)*X 1 1+(5414980759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305546077/10000000000 : ℝ)*X 2 0+(1082996149/2000000000 : ℝ)*X 2 1+(-1999232057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2169255089/5000000000 : ℝ)*X 0 0+(4518828151/10000000000 : ℝ)*X 0 1+(4165121181/10000000000 : ℝ)*X 0 2+(2169255089/5000000000 : ℝ)*X 1 0+(4518828151/10000000000 : ℝ)*X 1 1+(4165121181/10000000000 : ℝ)*X 1 2+(2169255089/5000000000 : ℝ)*X 2 0+(4518828151/10000000000 : ℝ)*X 2 1+(4165121181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5655559787154553756308301791/1890500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127144553/25000000000000 : ℝ)*(base19) + (558743233/100000000000000 : ℝ)*(base23) + (15519939/50000000000000 : ℝ)*(upper3) + (905289/100000000000000 : ℝ)*(upper4) + (77394551/100000000000000 : ℝ)*(upper5) + (4293316431815901/100000000000000 : ℝ)*(major0) + (4293316431815901/100000000000000 : ℝ)*(major1) + (2146658215907951/50000000000000 : ℝ)*(major2) + (2889882713919241/50000000000000 : ℝ)*(sp0) + (2889888342111997/50000000000000 : ℝ)*(sp1) + (5779776634058973/100000000000000 : ℝ)*(sp2) + (2806849744731493/100000000000000 : ℝ)*(sp3) + (470598549/4000000000000 : ℝ)*(sp4) + (5826379153/100000000000000 : ℝ)*(sp7) + (1403427785555323/50000000000000 : ℝ)*(f.failure) + (5779777192802207/100000000000000 : ℝ)*(f.sum) + (201428440173989/37810000000000000000000000000 : ℝ)*base65 + (44463642818030599403/3781000000000000000000000000000000 : ℝ)*base68 + (17242087394948689447/1890500000000000000000000000000000 : ℝ)*base69 + (3699352675538599403/3781000000000000000000000000000000 : ℝ)*base72 + (140257088548861/37810000000000000000000000000 : ℝ)*base74 + (4997739711692310553/1890500000000000000000000000000000 : ℝ)*base76 + (9779091962343100597/3781000000000000000000000000000000 : ℝ)*base77 + (17519575243665899403/3781000000000000000000000000000000 : ℝ)*base80 + (50722242131913/18905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (614147/312500000000000000000 : ℝ)*base89 + (614147/312500000000000000000 : ℝ)*base91 + (2510853/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (642400780296646249504943271/236312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (485654213/100000000000000 : ℝ)*(base19) + (538462541/100000000000000 : ℝ)*(base23) + (55968049/100000000000000 : ℝ)*(upper3) + (15585517/100000000000000 : ℝ)*(lower4) + (29054369/50000000000000 : ℝ)*(upper5) + (540554163059773/12500000000000 : ℝ)*(major0) + (540554163059773/12500000000000 : ℝ)*(major1) + (540554163059773/12500000000000 : ℝ)*(major2) + (4919453849/50000000000000 : ℝ)*(sp1) + (10542232709/100000000000000 : ℝ)*(sp2) + (2910833783644093/50000000000000 : ℝ)*(sp4) + (232866289709051/4000000000000 : ℝ)*(sp5) + (1164331297318587/20000000000000 : ℝ)*(sp6) + (1413599475526789/50000000000000 : ℝ)*(sp7) + (1413599475526789/50000000000000 : ℝ)*(f.failure) + (2910833783644093/50000000000000 : ℝ)*(f.sum) + (91605876158341/9452500000000000000000000000 : ℝ)*base65 + (172638966142796581/472625000000000000000000000000000 : ℝ)*base67 + (5137357895215796581/472625000000000000000000000000000 : ℝ)*base69 + (8223804236580921581/472625000000000000000000000000000 : ℝ)*base71 + (34515584118053/18905000000000000000000000000 : ℝ)*base74 + (4050586217948171581/472625000000000000000000000000000 : ℝ)*base75 + (3747270636325796581/472625000000000000000000000000000 : ℝ)*base77 + (9067212502488921581/472625000000000000000000000000000 : ℝ)*base79 + (84845636137037/18905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5633579/312500000000000000000 : ℝ)*base90 + (5633579/312500000000000000000 : ℝ)*base92 + (5633579/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1297_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1297_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1297_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1297_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1297_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1297_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9541/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1297_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

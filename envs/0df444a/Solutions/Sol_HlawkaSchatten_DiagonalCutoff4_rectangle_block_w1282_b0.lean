-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1282_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:23:37.687254+00:00
-- url     : https://prove2.me/submissions/83a17d36-9929-42db-b7e8-b3d564690bda

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
theorem support_rectangle_w1282_s0_0 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-461288651/2500000000 : ℝ)*x 0 + (1505809089/2500000000 : ℝ)*x 1 + (299774579/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (461288651/2500000000 : ℝ)^2121 ≤ (10776481705051/100000000000000 : ℝ)^1609 := by
    have hnat : (461288651 : ℕ)^2121*100000000000000^1609 ≤ 10776481705051^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461288651 2500000000 10776481705051 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1505809089/2500000000 : ℝ)^2121 ≤ (3203683334553/6250000000000 : ℝ)^1609 := by
    have hnat : (1505809089 : ℕ)^2121*6250000000000^1609 ≤ 3203683334553^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505809089 2500000000 3203683334553 6250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299774579/625000000 : ℝ)^2121 ≤ (18982292467381/50000000000000 : ℝ)^1609 := by
    have hnat : (299774579 : ℕ)^2121*50000000000000^1609 ≤ 18982292467381^1609*625000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299774579 625000000 18982292467381 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-461288651/2500000000 : ℝ), (1505809089/2500000000 : ℝ), (299774579/625000000 : ℝ)] ![(10776481705051/100000000000000 : ℝ), (3203683334553/6250000000000 : ℝ), (18982292467381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-461288651/2500000000 : ℝ)|^2121 ≤ (10776481705051/100000000000000 : ℝ)^1609
        have hw : |(-461288651/2500000000 : ℝ)|=(461288651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1505809089/2500000000 : ℝ)|^2121 ≤ (3203683334553/6250000000000 : ℝ)^1609
        have hw : |(1505809089/2500000000 : ℝ)|=(1505809089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299774579/625000000 : ℝ)|^2121 ≤ (18982292467381/50000000000000 : ℝ)^1609
        have hw : |(299774579/625000000 : ℝ)|=(299774579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s0_1 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5508540991/10000000000 : ℝ)*x 0 + (-2545585383/10000000000 : ℝ)*x 1 + (1199098307/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5508540991/10000000000 : ℝ)^2121 ≤ (11391261674237/25000000000000 : ℝ)^1609 := by
    have hnat : (5508540991 : ℕ)^2121*25000000000000^1609 ≤ 11391261674237^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508540991 10000000000 11391261674237 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2545585383/10000000000 : ℝ)^2121 ≤ (8235184363051/50000000000000 : ℝ)^1609 := by
    have hnat : (2545585383 : ℕ)^2121*50000000000000^1609 ≤ 8235184363051^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545585383 10000000000 8235184363051 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199098307/2500000000 : ℝ)^2121 ≤ (1898229227957/5000000000000 : ℝ)^1609 := by
    have hnat : (1199098307 : ℕ)^2121*5000000000000^1609 ≤ 1898229227957^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199098307 2500000000 1898229227957 5000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5508540991/10000000000 : ℝ), (-2545585383/10000000000 : ℝ), (1199098307/2500000000 : ℝ)] ![(11391261674237/25000000000000 : ℝ), (8235184363051/50000000000000 : ℝ), (1898229227957/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5508540991/10000000000 : ℝ)|^2121 ≤ (11391261674237/25000000000000 : ℝ)^1609
        have hw : |(5508540991/10000000000 : ℝ)|=(5508540991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2545585383/10000000000 : ℝ)|^2121 ≤ (8235184363051/50000000000000 : ℝ)^1609
        have hw : |(-2545585383/10000000000 : ℝ)|=(2545585383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199098307/2500000000 : ℝ)|^2121 ≤ (1898229227957/5000000000000 : ℝ)^1609
        have hw : |(1199098307/2500000000 : ℝ)|=(1199098307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s0_2 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (550854101/1000000000 : ℝ)*x 0 + (4796393237/10000000000 : ℝ)*x 1 + (-2545585349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550854101/1000000000 : ℝ)^2121 ≤ (45565046904121/100000000000000 : ℝ)^1609 := by
    have hnat : (550854101 : ℕ)^2121*100000000000000^1609 ≤ 45565046904121^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550854101 1000000000 45565046904121 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4796393237/10000000000 : ℝ)^2121 ≤ (7592916930609/20000000000000 : ℝ)^1609 := by
    have hnat : (4796393237 : ℕ)^2121*20000000000000^1609 ≤ 7592916930609^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796393237 10000000000 7592916930609 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2545585349/10000000000 : ℝ)^2121 ≤ (8235184218057/50000000000000 : ℝ)^1609 := by
    have hnat : (2545585349 : ℕ)^2121*50000000000000^1609 ≤ 8235184218057^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545585349 10000000000 8235184218057 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(550854101/1000000000 : ℝ), (4796393237/10000000000 : ℝ), (-2545585349/10000000000 : ℝ)] ![(45565046904121/100000000000000 : ℝ), (7592916930609/20000000000000 : ℝ), (8235184218057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(550854101/1000000000 : ℝ)|^2121 ≤ (45565046904121/100000000000000 : ℝ)^1609
        have hw : |(550854101/1000000000 : ℝ)|=(550854101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4796393237/10000000000 : ℝ)|^2121 ≤ (7592916930609/20000000000000 : ℝ)^1609
        have hw : |(4796393237/10000000000 : ℝ)|=(4796393237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2545585349/10000000000 : ℝ)|^2121 ≤ (8235184218057/50000000000000 : ℝ)^1609
        have hw : |(-2545585349/10000000000 : ℝ)|=(2545585349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s0_3 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4187873139/10000000000 : ℝ)*x 0 + (3110103403/10000000000 : ℝ)*x 1 + (1124385109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187873139/10000000000 : ℝ)^2121 ≤ (31747391576687/100000000000000 : ℝ)^1609 := by
    have hnat : (4187873139 : ℕ)^2121*100000000000000^1609 ≤ 31747391576687^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187873139 10000000000 31747391576687 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3110103403/10000000000 : ℝ)^2121 ≤ (4289440693699/20000000000000 : ℝ)^1609 := by
    have hnat : (3110103403 : ℕ)^2121*20000000000000^1609 ≤ 4289440693699^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110103403 10000000000 4289440693699 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124385109/2000000000 : ℝ)^2121 ≤ (46805404940829/100000000000000 : ℝ)^1609 := by
    have hnat : (1124385109 : ℕ)^2121*100000000000000^1609 ≤ 46805404940829^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124385109 2000000000 46805404940829 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187873139/10000000000 : ℝ), (3110103403/10000000000 : ℝ), (1124385109/2000000000 : ℝ)] ![(31747391576687/100000000000000 : ℝ), (4289440693699/20000000000000 : ℝ), (46805404940829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187873139/10000000000 : ℝ)|^2121 ≤ (31747391576687/100000000000000 : ℝ)^1609
        have hw : |(4187873139/10000000000 : ℝ)|=(4187873139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3110103403/10000000000 : ℝ)|^2121 ≤ (4289440693699/20000000000000 : ℝ)^1609
        have hw : |(3110103403/10000000000 : ℝ)|=(3110103403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124385109/2000000000 : ℝ)|^2121 ≤ (46805404940829/100000000000000 : ℝ)^1609
        have hw : |(1124385109/2000000000 : ℝ)|=(1124385109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s0_4 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1479947/8000000 : ℝ)*x 0 + (75438627/156250000 : ℝ)*x 1 + (5990431627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1479947/8000000 : ℝ)^2121 ≤ (1081329104141/10000000000000 : ℝ)^1609 := by
    have hnat : (1479947 : ℕ)^2121*10000000000000^1609 ≤ 1081329104141^1609*8000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479947 8000000 1081329104141 10000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75438627/156250000 : ℝ)^2121 ≤ (7659093449071/20000000000000 : ℝ)^1609 := by
    have hnat : (75438627 : ℕ)^2121*20000000000000^1609 ≤ 7659093449071^1609*156250000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75438627 156250000 7659093449071 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5990431627/10000000000 : ℝ)^2121 ≤ (50891241698669/100000000000000 : ℝ)^1609 := by
    have hnat : (5990431627 : ℕ)^2121*100000000000000^1609 ≤ 50891241698669^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5990431627 10000000000 50891241698669 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1479947/8000000 : ℝ), (75438627/156250000 : ℝ), (5990431627/10000000000 : ℝ)] ![(1081329104141/10000000000000 : ℝ), (7659093449071/20000000000000 : ℝ), (50891241698669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1479947/8000000 : ℝ)|^2121 ≤ (1081329104141/10000000000000 : ℝ)^1609
        have hw : |(-1479947/8000000 : ℝ)|=(1479947/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(75438627/156250000 : ℝ)|^2121 ≤ (7659093449071/20000000000000 : ℝ)^1609
        have hw : |(75438627/156250000 : ℝ)|=(75438627/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5990431627/10000000000 : ℝ)|^2121 ≤ (50891241698669/100000000000000 : ℝ)^1609
        have hw : |(5990431627/10000000000 : ℝ)|=(5990431627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s0_5 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5174618767/10000000000 : ℝ)*x 0 + (-1351544527/10000000000 : ℝ)*x 1 + (5990434153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174618767/10000000000 : ℝ)^2121 ≤ (839192450167/2000000000000 : ℝ)^1609 := by
    have hnat : (5174618767 : ℕ)^2121*2000000000000^1609 ≤ 839192450167^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174618767 10000000000 839192450167 2000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351544527/10000000000 : ℝ)^2121 ≤ (7149107492671/100000000000000 : ℝ)^1609 := by
    have hnat : (1351544527 : ℕ)^2121*100000000000000^1609 ≤ 7149107492671^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351544527 10000000000 7149107492671 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5990434153/10000000000 : ℝ)^2121 ≤ (50891269986713/100000000000000 : ℝ)^1609 := by
    have hnat : (5990434153 : ℕ)^2121*100000000000000^1609 ≤ 50891269986713^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5990434153 10000000000 50891269986713 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174618767/10000000000 : ℝ), (-1351544527/10000000000 : ℝ), (5990434153/10000000000 : ℝ)] ![(839192450167/2000000000000 : ℝ), (7149107492671/100000000000000 : ℝ), (50891269986713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174618767/10000000000 : ℝ)|^2121 ≤ (839192450167/2000000000000 : ℝ)^1609
        have hw : |(5174618767/10000000000 : ℝ)|=(5174618767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1351544527/10000000000 : ℝ)|^2121 ≤ (7149107492671/100000000000000 : ℝ)^1609
        have hw : |(-1351544527/10000000000 : ℝ)|=(1351544527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5990434153/10000000000 : ℝ)|^2121 ≤ (50891269986713/100000000000000 : ℝ)^1609
        have hw : |(5990434153/10000000000 : ℝ)|=(5990434153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s0_6 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2587309993/5000000000 : ℝ)*x 0 + (2995216023/5000000000 : ℝ)*x 1 + (-1351546043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587309993/5000000000 : ℝ)^2121 ≤ (5244954442283/12500000000000 : ℝ)^1609 := by
    have hnat : (2587309993 : ℕ)^2121*12500000000000^1609 ≤ 5244954442283^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587309993 5000000000 5244954442283 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2995216023/5000000000 : ℝ)^2121 ≤ (10178249278189/20000000000000 : ℝ)^1609 := by
    have hnat : (2995216023 : ℕ)^2121*20000000000000^1609 ≤ 10178249278189^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995216023 5000000000 10178249278189 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351546043/10000000000 : ℝ)^2121 ≤ (7149118063411/100000000000000 : ℝ)^1609 := by
    have hnat : (1351546043 : ℕ)^2121*100000000000000^1609 ≤ 7149118063411^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351546043 10000000000 7149118063411 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587309993/5000000000 : ℝ), (2995216023/5000000000 : ℝ), (-1351546043/10000000000 : ℝ)] ![(5244954442283/12500000000000 : ℝ), (10178249278189/20000000000000 : ℝ), (7149118063411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587309993/5000000000 : ℝ)|^2121 ≤ (5244954442283/12500000000000 : ℝ)^1609
        have hw : |(2587309993/5000000000 : ℝ)|=(2587309993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2995216023/5000000000 : ℝ)|^2121 ≤ (10178249278189/20000000000000 : ℝ)^1609
        have hw : |(2995216023/5000000000 : ℝ)|=(2995216023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1351546043/10000000000 : ℝ)|^2121 ≤ (7149118063411/100000000000000 : ℝ)^1609
        have hw : |(-1351546043/10000000000 : ℝ)|=(1351546043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s0_7 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4197662003/10000000000 : ℝ)*x 0 + (5557073371/10000000000 : ℝ)*x 1 + (1588630383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197662003/10000000000 : ℝ)^2121 ≤ (15922624395387/50000000000000 : ℝ)^1609 := by
    have hnat : (4197662003 : ℕ)^2121*50000000000000^1609 ≤ 15922624395387^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197662003 10000000000 15922624395387 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5557073371/10000000000 : ℝ)^2121 ≤ (11523744200707/25000000000000 : ℝ)^1609 := by
    have hnat : (5557073371 : ℕ)^2121*25000000000000^1609 ≤ 11523744200707^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557073371 10000000000 11523744200707 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1588630383/5000000000 : ℝ)^2121 ≤ (1102988719451/5000000000000 : ℝ)^1609 := by
    have hnat : (1588630383 : ℕ)^2121*5000000000000^1609 ≤ 1102988719451^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588630383 5000000000 1102988719451 5000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197662003/10000000000 : ℝ), (5557073371/10000000000 : ℝ), (1588630383/5000000000 : ℝ)] ![(15922624395387/50000000000000 : ℝ), (11523744200707/25000000000000 : ℝ), (1102988719451/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197662003/10000000000 : ℝ)|^2121 ≤ (15922624395387/50000000000000 : ℝ)^1609
        have hw : |(4197662003/10000000000 : ℝ)|=(4197662003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5557073371/10000000000 : ℝ)|^2121 ≤ (11523744200707/25000000000000 : ℝ)^1609
        have hw : |(5557073371/10000000000 : ℝ)|=(5557073371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1588630383/5000000000 : ℝ)|^2121 ≤ (1102988719451/5000000000000 : ℝ)^1609
        have hw : |(1588630383/5000000000 : ℝ)|=(1588630383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1282_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (477/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27309/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4241/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4241 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4241*1^1024 ≤ 0^1024*1^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4241/1024 : ℝ) ≤ (44969808065085713/2000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4241 ≤ (44969808065085713/2000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4241*2000000000000000000^1024 ≤ 44969808065085713^1024*5^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 44969808065085713 2000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (44969808065085713/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4241 := by
      have hnat : (1 : ℕ)^1024*1^4241 ≤ 1^4241*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2044969808065085713/2000000000000000000 : ℝ) ≤ (10053833384720697/10000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (2044969808065085713/2000000000000000000 : ℝ)^1024 ≤ (10053833384720697/10000000000000000 : ℝ)^4241 := by
      have hnat : (2044969808065085713 : ℕ)^1024*10000000000000000^4241 ≤ 10053833384720697^4241*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2044969808065085713 2000000000000000000 10053833384720697 10000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10053833384720697/10000000000000000 : ℝ)) (X := (2044969808065085713/2000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1044969808065085713/1000000000000000000 : ℝ) ≤ (5053833384720697/5000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (1044969808065085713/1000000000000000000 : ℝ)^1024 ≤ (5053833384720697/5000000000000000 : ℝ)^4241 := by
      have hnat : (1044969808065085713 : ℕ)^1024*5000000000000000^4241 ≤ 5053833384720697^4241*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1044969808065085713 1000000000000000000 5053833384720697 5000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5053833384720697/5000000000000000 : ℝ)) (X := (1044969808065085713/1000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(53833384720697/4000000000000000 : ℝ)*(0 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(53833384720697/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44969808065085713/2000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(53833384720697/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4241/1024 : ℝ) := by
    rw [show (1 : ℝ)+(53833384720697/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10053833384720697/10000000000000000 : ℝ) by norm_num, show 1+(44969808065085713/2000000000000000000 : ℝ)+(0 : ℝ)=(2044969808065085713/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44969808065085713/2000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(53833384720697/4000000000000000 : ℝ)*(2/5 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(53833384720697/4000000000000000 : ℝ)*(2/5 : ℝ)=(5053833384720697/5000000000000000 : ℝ) by norm_num, show 1+2*(44969808065085713/2000000000000000000 : ℝ)=(1044969808065085713/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(53833384720697/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (53833384720697/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(53833384720697/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (53833384720697/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(53833384720697/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (53833384720697/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-461288651/2500000000 : ℝ)*X 0 0+(1505809089/2500000000 : ℝ)*X 0 1+(299774579/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5508540991/10000000000 : ℝ)*X 1 0+(-2545585383/10000000000 : ℝ)*X 1 1+(1199098307/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((550854101/1000000000 : ℝ)*X 2 0+(4796393237/10000000000 : ℝ)*X 2 1+(-2545585349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4187873139/10000000000 : ℝ)*X 0 0+(3110103403/10000000000 : ℝ)*X 0 1+(1124385109/2000000000 : ℝ)*X 0 2+(4187873139/10000000000 : ℝ)*X 1 0+(3110103403/10000000000 : ℝ)*X 1 1+(1124385109/2000000000 : ℝ)*X 1 2+(4187873139/10000000000 : ℝ)*X 2 0+(3110103403/10000000000 : ℝ)*X 2 1+(1124385109/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1479947/8000000 : ℝ)*X 0 0+(75438627/156250000 : ℝ)*X 0 1+(5990431627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174618767/10000000000 : ℝ)*X 1 0+(-1351544527/10000000000 : ℝ)*X 1 1+(5990434153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587309993/5000000000 : ℝ)*X 2 0+(2995216023/5000000000 : ℝ)*X 2 1+(-1351546043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4197662003/10000000000 : ℝ)*X 0 0+(5557073371/10000000000 : ℝ)*X 0 1+(1588630383/5000000000 : ℝ)*X 0 2+(4197662003/10000000000 : ℝ)*X 1 0+(5557073371/10000000000 : ℝ)*X 1 1+(1588630383/5000000000 : ℝ)*X 1 2+(4197662003/10000000000 : ℝ)*X 2 0+(5557073371/10000000000 : ℝ)*X 2 1+(1588630383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (170835394113183429516099/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97997/125000000000 : ℝ)*(base1) + (41407039/2500000000000 : ℝ)*(base19) + (51846657/3125000000000 : ℝ)*(base23) + (1513539/800000000000 : ℝ)*(upper3) + (198665083/100000000000000 : ℝ)*(upper5) + (303308242434911/50000000000000 : ℝ)*(major0) + (303308242434911/50000000000000 : ℝ)*(major1) + (303308242434911/50000000000000 : ℝ)*(major2) + (815105116044011/100000000000000 : ℝ)*(sp0) + (815108675453131/100000000000000 : ℝ)*(sp1) + (815108672641667/100000000000000 : ℝ)*(sp2) + (398119791070743/100000000000000 : ℝ)*(sp3) + (132352207/2500000000000 : ℝ)*(sp4) + (31759451/1250000000000 : ℝ)*(sp7) + (398122410224423/100000000000000 : ℝ)*(f.failure) + (815110331734691/100000000000000 : ℝ)*(f.sum) + (324169549752967/100000000000000000000000000000 : ℝ)*base65 + (2645364052967/200000000000000000000000000000 : ℝ)*base67 + (746514801252967/200000000000000000000000000000 : ℝ)*base69 + (963568269452967/200000000000000000000000000000 : ℝ)*base71 + (2453056547033/100000000000000000000000000000 : ℝ)*base74 + (1540550120452967/200000000000000000000000000000 : ℝ)*base75 + (945274099652967/200000000000000000000000000000 : ℝ)*base77 + (1056148899452967/200000000000000000000000000000 : ℝ)*base79 + (270101893852967/100000000000000000000000000000 : ℝ)*base81 + (25833603/10000000000000000000000 : ℝ)*base90 + (25833603/10000000000000000000000 : ℝ)*base92 + (25833603/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (667907086910261476156047/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40920027/12500000000000 : ℝ)*(base1) + (264509737/50000000000000 : ℝ)*(base19) + (68351277/10000000000000 : ℝ)*(base23) + (84316829/100000000000000 : ℝ)*(upper3) + (640260744901839/100000000000000 : ℝ)*(major0) + (640260744901839/100000000000000 : ℝ)*(major1) + (640260744901839/100000000000000 : ℝ)*(major2) + (124795137/10000000000000 : ℝ)*(sp1) + (501422461/100000000000000 : ℝ)*(sp2) + (67625167/10000000000000 : ℝ)*(sp3) + (215079641785297/25000000000000 : ℝ)*(sp4) + (860316462810127/100000000000000 : ℝ)*(sp5) + (43015852742287/5000000000000 : ℝ)*(sp6) + (52525266886621/12500000000000 : ℝ)*(sp7) + (210101569352427/50000000000000 : ℝ)*(f.failure) + (215079559945243/25000000000000 : ℝ)*(f.sum) + (50076710138217/200000000000000000000000000000 : ℝ)*base66 + (2323616784138217/400000000000000000000000000000 : ℝ)*base68 + (452880908938217/400000000000000000000000000000 : ℝ)*base70 + (1578517548538217/400000000000000000000000000000 : ℝ)*base72 + (236686003138217/200000000000000000000000000000 : ℝ)*base74 + (2144384325061783/400000000000000000000000000000 : ℝ)*base75 + (359767216938217/400000000000000000000000000000 : ℝ)*base78 + (275325677338217/400000000000000000000000000000 : ℝ)*base80 + (107807110861783/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10035753/5000000000000000000000 : ℝ)*base89 + (10035753/5000000000000000000000 : ℝ)*base91 + (10035753/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1282_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (477/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27309/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1282_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1282_s1_0 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-127415591/625000000 : ℝ)*x 0 + (708766019/1250000000 : ℝ)*x 1 + (5025627363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127415591/625000000 : ℝ)^2121 ≤ (12290467509281/100000000000000 : ℝ)^1609 := by
    have hnat : (127415591 : ℕ)^2121*100000000000000^1609 ≤ 12290467509281^1609*625000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127415591 625000000 12290467509281 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708766019/1250000000 : ℝ)^2121 ≤ (47335137868719/100000000000000 : ℝ)^1609 := by
    have hnat : (708766019 : ℕ)^2121*100000000000000^1609 ≤ 47335137868719^1609*1250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708766019 1250000000 47335137868719 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5025627363/10000000000 : ℝ)^2121 ≤ (10093598652403/25000000000000 : ℝ)^1609 := by
    have hnat : (5025627363 : ℕ)^2121*25000000000000^1609 ≤ 10093598652403^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025627363 10000000000 10093598652403 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127415591/625000000 : ℝ), (708766019/1250000000 : ℝ), (5025627363/10000000000 : ℝ)] ![(12290467509281/100000000000000 : ℝ), (47335137868719/100000000000000 : ℝ), (10093598652403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127415591/625000000 : ℝ)|^2121 ≤ (12290467509281/100000000000000 : ℝ)^1609
        have hw : |(-127415591/625000000 : ℝ)|=(127415591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708766019/1250000000 : ℝ)|^2121 ≤ (47335137868719/100000000000000 : ℝ)^1609
        have hw : |(708766019/1250000000 : ℝ)|=(708766019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5025627363/10000000000 : ℝ)|^2121 ≤ (10093598652403/25000000000000 : ℝ)^1609
        have hw : |(5025627363/10000000000 : ℝ)|=(5025627363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s1_1 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (135301233/250000000 : ℝ)*x 0 + (-1192204597/5000000000 : ℝ)*x 1 + (1005125511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135301233/250000000 : ℝ)^2121 ≤ (8903172012699/20000000000000 : ℝ)^1609 := by
    have hnat : (135301233 : ℕ)^2121*20000000000000^1609 ≤ 8903172012699^1609*250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135301233 250000000 8903172012699 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1192204597/5000000000 : ℝ)^2121 ≤ (15109743282481/100000000000000 : ℝ)^1609 := by
    have hnat : (1192204597 : ℕ)^2121*100000000000000^1609 ≤ 15109743282481^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192204597 5000000000 15109743282481 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005125511/2000000000 : ℝ)^2121 ≤ (1261699895091/3125000000000 : ℝ)^1609 := by
    have hnat : (1005125511 : ℕ)^2121*3125000000000^1609 ≤ 1261699895091^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005125511 2000000000 1261699895091 3125000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135301233/250000000 : ℝ), (-1192204597/5000000000 : ℝ), (1005125511/2000000000 : ℝ)] ![(8903172012699/20000000000000 : ℝ), (15109743282481/100000000000000 : ℝ), (1261699895091/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135301233/250000000 : ℝ)|^2121 ≤ (8903172012699/20000000000000 : ℝ)^1609
        have hw : |(135301233/250000000 : ℝ)|=(135301233/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1192204597/5000000000 : ℝ)|^2121 ≤ (15109743282481/100000000000000 : ℝ)^1609
        have hw : |(-1192204597/5000000000 : ℝ)|=(1192204597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005125511/2000000000 : ℝ)|^2121 ≤ (1261699895091/3125000000000 : ℝ)^1609
        have hw : |(1005125511/2000000000 : ℝ)|=(1005125511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s1_2 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1353012371/2500000000 : ℝ)*x 0 + (201025099/400000000 : ℝ)*x 1 + (-2384409081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353012371/2500000000 : ℝ)^2121 ≤ (22257930920849/50000000000000 : ℝ)^1609 := by
    have hnat : (1353012371 : ℕ)^2121*50000000000000^1609 ≤ 22257930920849^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353012371 2500000000 22257930920849 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201025099/400000000 : ℝ)^2121 ≤ (5046799474463/12500000000000 : ℝ)^1609 := by
    have hnat : (201025099 : ℕ)^2121*12500000000000^1609 ≤ 5046799474463^1609*400000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201025099 400000000 5046799474463 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2384409081/10000000000 : ℝ)^2121 ≤ (1888717792319/12500000000000 : ℝ)^1609 := by
    have hnat : (2384409081 : ℕ)^2121*12500000000000^1609 ≤ 1888717792319^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384409081 10000000000 1888717792319 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353012371/2500000000 : ℝ), (201025099/400000000 : ℝ), (-2384409081/10000000000 : ℝ)] ![(22257930920849/50000000000000 : ℝ), (5046799474463/12500000000000 : ℝ), (1888717792319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353012371/2500000000 : ℝ)|^2121 ≤ (22257930920849/50000000000000 : ℝ)^1609
        have hw : |(1353012371/2500000000 : ℝ)|=(1353012371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201025099/400000000 : ℝ)|^2121 ≤ (5046799474463/12500000000000 : ℝ)^1609
        have hw : |(201025099/400000000 : ℝ)|=(201025099/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2384409081/10000000000 : ℝ)|^2121 ≤ (1888717792319/12500000000000 : ℝ)^1609
        have hw : |(-2384409081/10000000000 : ℝ)|=(2384409081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s1_3 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (86057769/200000000 : ℝ)*x 0 + (922812457/2500000000 : ℝ)*x 1 + (6263491/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86057769/200000000 : ℝ)^2121 ≤ (32901739518517/100000000000000 : ℝ)^1609 := by
    have hnat : (86057769 : ℕ)^2121*100000000000000^1609 ≤ 32901739518517^1609*200000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86057769 200000000 32901739518517 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922812457/2500000000 : ℝ)^2121 ≤ (1344044582689/5000000000000 : ℝ)^1609 := by
    have hnat : (922812457 : ℕ)^2121*5000000000000^1609 ≤ 1344044582689^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922812457 2500000000 1344044582689 5000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6263491/12500000 : ℝ)^2121 ≤ (20108684412367/50000000000000 : ℝ)^1609 := by
    have hnat : (6263491 : ℕ)^2121*50000000000000^1609 ≤ 20108684412367^1609*12500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6263491 12500000 20108684412367 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86057769/200000000 : ℝ), (922812457/2500000000 : ℝ), (6263491/12500000 : ℝ)] ![(32901739518517/100000000000000 : ℝ), (1344044582689/5000000000000 : ℝ), (20108684412367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86057769/200000000 : ℝ)|^2121 ≤ (32901739518517/100000000000000 : ℝ)^1609
        have hw : |(86057769/200000000 : ℝ)|=(86057769/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922812457/2500000000 : ℝ)|^2121 ≤ (1344044582689/5000000000000 : ℝ)^1609
        have hw : |(922812457/2500000000 : ℝ)|=(922812457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6263491/12500000 : ℝ)|^2121 ≤ (20108684412367/50000000000000 : ℝ)^1609
        have hw : |(6263491/12500000 : ℝ)|=(6263491/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s1_4 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019654173/5000000000 : ℝ)*x 0 + (5034094199/10000000000 : ℝ)*x 1 + (5661500121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019654173/5000000000 : ℝ)^2121 ≤ (12295704064873/100000000000000 : ℝ)^1609 := by
    have hnat : (1019654173 : ℕ)^2121*100000000000000^1609 ≤ 12295704064873^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019654173 5000000000 12295704064873 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5034094199/10000000000 : ℝ)^2121 ≤ (1011602083437/2500000000000 : ℝ)^1609 := by
    have hnat : (5034094199 : ℕ)^2121*2500000000000^1609 ≤ 1011602083437^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5034094199 10000000000 1011602083437 2500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5661500121/10000000000 : ℝ)^2121 ≤ (47240212586001/100000000000000 : ℝ)^1609 := by
    have hnat : (5661500121 : ℕ)^2121*100000000000000^1609 ≤ 47240212586001^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661500121 10000000000 47240212586001 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019654173/5000000000 : ℝ), (5034094199/10000000000 : ℝ), (5661500121/10000000000 : ℝ)] ![(12295704064873/100000000000000 : ℝ), (1011602083437/2500000000000 : ℝ), (47240212586001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019654173/5000000000 : ℝ)|^2121 ≤ (12295704064873/100000000000000 : ℝ)^1609
        have hw : |(-1019654173/5000000000 : ℝ)|=(1019654173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5034094199/10000000000 : ℝ)|^2121 ≤ (1011602083437/2500000000000 : ℝ)^1609
        have hw : |(5034094199/10000000000 : ℝ)|=(5034094199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5661500121/10000000000 : ℝ)|^2121 ≤ (47240212586001/100000000000000 : ℝ)^1609
        have hw : |(5661500121/10000000000 : ℝ)|=(5661500121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s1_5 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5245682897/10000000000 : ℝ)*x 0 + (-17485363/100000000 : ℝ)*x 1 + (2830750291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245682897/10000000000 : ℝ)^2121 ≤ (427208829297/1000000000000 : ℝ)^1609 := by
    have hnat : (5245682897 : ℕ)^2121*1000000000000^1609 ≤ 427208829297^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245682897 10000000000 427208829297 1000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17485363/100000000 : ℝ)^2121 ≤ (2509724850557/25000000000000 : ℝ)^1609 := by
    have hnat : (17485363 : ℕ)^2121*25000000000000^1609 ≤ 2509724850557^1609*100000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17485363 100000000 2509724850557 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2830750291/5000000000 : ℝ)^2121 ≤ (47240217656677/100000000000000 : ℝ)^1609 := by
    have hnat : (2830750291 : ℕ)^2121*100000000000000^1609 ≤ 47240217656677^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830750291 5000000000 47240217656677 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245682897/10000000000 : ℝ), (-17485363/100000000 : ℝ), (2830750291/5000000000 : ℝ)] ![(427208829297/1000000000000 : ℝ), (2509724850557/25000000000000 : ℝ), (47240217656677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245682897/10000000000 : ℝ)|^2121 ≤ (427208829297/1000000000000 : ℝ)^1609
        have hw : |(5245682897/10000000000 : ℝ)|=(5245682897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17485363/100000000 : ℝ)|^2121 ≤ (2509724850557/25000000000000 : ℝ)^1609
        have hw : |(-17485363/100000000 : ℝ)|=(17485363/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2830750291/5000000000 : ℝ)|^2121 ≤ (47240217656677/100000000000000 : ℝ)^1609
        have hw : |(2830750291/5000000000 : ℝ)|=(2830750291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s1_6 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2622841403/5000000000 : ℝ)*x 0 + (2830750131/5000000000 : ℝ)*x 1 + (-1748536893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622841403/5000000000 : ℝ)^2121 ≤ (42720881952769/100000000000000 : ℝ)^1609 := by
    have hnat : (2622841403 : ℕ)^2121*100000000000000^1609 ≤ 42720881952769^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622841403 5000000000 42720881952769 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2830750131/5000000000 : ℝ)^2121 ≤ (23620107068451/50000000000000 : ℝ)^1609 := by
    have hnat : (2830750131 : ℕ)^2121*50000000000000^1609 ≤ 23620107068451^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830750131 5000000000 23620107068451 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1748536893/10000000000 : ℝ)^2121 ≤ (10038903890207/100000000000000 : ℝ)^1609 := by
    have hnat : (1748536893 : ℕ)^2121*100000000000000^1609 ≤ 10038903890207^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748536893 10000000000 10038903890207 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622841403/5000000000 : ℝ), (2830750131/5000000000 : ℝ), (-1748536893/10000000000 : ℝ)] ![(42720881952769/100000000000000 : ℝ), (23620107068451/50000000000000 : ℝ), (10038903890207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622841403/5000000000 : ℝ)|^2121 ≤ (42720881952769/100000000000000 : ℝ)^1609
        have hw : |(2622841403/5000000000 : ℝ)|=(2622841403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2830750131/5000000000 : ℝ)|^2121 ≤ (23620107068451/50000000000000 : ℝ)^1609
        have hw : |(2830750131/5000000000 : ℝ)|=(2830750131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1748536893/10000000000 : ℝ)|^2121 ≤ (10038903890207/100000000000000 : ℝ)^1609
        have hw : |(-1748536893/10000000000 : ℝ)|=(1748536893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s1_7 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (860847429/2000000000 : ℝ)*x 0 + (4993458077/10000000000 : ℝ)*x 1 + (3708914969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860847429/2000000000 : ℝ)^2121 ≤ (1028604203301/3125000000000 : ℝ)^1609 := by
    have hnat : (860847429 : ℕ)^2121*3125000000000^1609 ≤ 1028604203301^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860847429 2000000000 1028604203301 3125000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4993458077/10000000000 : ℝ)^2121 ≤ (500425823503/1250000000000 : ℝ)^1609 := by
    have hnat : (4993458077 : ℕ)^2121*1250000000000^1609 ≤ 500425823503^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993458077 10000000000 500425823503 1250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3708914969/10000000000 : ℝ)^2121 ≤ (13525299796901/50000000000000 : ℝ)^1609 := by
    have hnat : (3708914969 : ℕ)^2121*50000000000000^1609 ≤ 13525299796901^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3708914969 10000000000 13525299796901 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860847429/2000000000 : ℝ), (4993458077/10000000000 : ℝ), (3708914969/10000000000 : ℝ)] ![(1028604203301/3125000000000 : ℝ), (500425823503/1250000000000 : ℝ), (13525299796901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860847429/2000000000 : ℝ)|^2121 ≤ (1028604203301/3125000000000 : ℝ)^1609
        have hw : |(860847429/2000000000 : ℝ)|=(860847429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4993458077/10000000000 : ℝ)|^2121 ≤ (500425823503/1250000000000 : ℝ)^1609
        have hw : |(4993458077/10000000000 : ℝ)|=(4993458077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3708914969/10000000000 : ℝ)|^2121 ≤ (13525299796901/50000000000000 : ℝ)^1609
        have hw : |(3708914969/10000000000 : ℝ)|=(3708914969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1282_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27309/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1577/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19931/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27309/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27309/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27309/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27309/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27309/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27309/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (477/50000 : ℝ) ^ (4241/1024 : ℝ) ≤ (53580209173/12500000000000000000 : ℝ) := by
    have hpowers : (477/50000 : ℝ)^4241 ≤ (53580209173/12500000000000000000 : ℝ)^1024 := by
      have hnat : (477 : ℕ)^4241*12500000000000000000^1024 ≤ 53580209173^1024*50000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        477 50000 53580209173 12500000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (477/50000 : ℝ)) (X := (53580209173/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27309/100000 : ℝ) ^ (4241/1024 : ℝ) ≤ (462810506942914217/100000000000000000000 : ℝ) := by
    have hpowers : (27309/100000 : ℝ)^4241 ≤ (462810506942914217/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27309 : ℕ)^4241*100000000000000000000^1024 ≤ 462810506942914217^1024*100000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27309 100000 462810506942914217 100000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27309/100000 : ℝ)) (X := (462810506942914217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000053580209173/6250000000000000000 : ℝ) ≤ (250000000517483/250000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (6250000053580209173/6250000000000000000 : ℝ)^1024 ≤ (250000000517483/250000000000000 : ℝ)^4241 := by
      have hnat : (6250000053580209173 : ℕ)^1024*250000000000000^4241 ≤ 250000000517483^4241*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000053580209173 6250000000000000000 250000000517483 250000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000000517483/250000000000000 : ℝ)) (X := (6250000053580209173/6250000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100462810935584587601/100000000000000000000 : ℝ) ≤ (2002231024612293/2000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (100462810935584587601/100000000000000000000 : ℝ)^1024 ≤ (2002231024612293/2000000000000000 : ℝ)^4241 := by
      have hnat : (100462810935584587601 : ℕ)^1024*2000000000000000^4241 ≤ 2002231024612293^4241*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100462810935584587601 100000000000000000000 2002231024612293 2000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002231024612293/2000000000000000 : ℝ)) (X := (100462810935584587601/100000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50462810506942914217/50000000000000000000 : ℝ) ≤ (1002231022542361/1000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (50462810506942914217/50000000000000000000 : ℝ)^1024 ≤ (1002231022542361/1000000000000000 : ℝ)^4241 := by
      have hnat : (50462810506942914217 : ℕ)^1024*1000000000000000^4241 ≤ 1002231022542361^4241*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50462810506942914217 50000000000000000000 1002231022542361 1000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002231022542361/1000000000000000 : ℝ)) (X := (50462810506942914217/50000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(53580209173/12500000000000000000 : ℝ) ≤ ((627449325262437157/627500000000000000 : ℝ)+2*(318717210347/75300000000000 : ℝ)*(477/50000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (627449325262437157/627500000000000000 : ℝ)+2*(318717210347/75300000000000 : ℝ)*(477/50000 : ℝ)=(250000000517483/250000000000000 : ℝ) by norm_num, show 1+2*(53580209173/12500000000000000000 : ℝ)=(6250000053580209173/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(462810506942914217/100000000000000000000 : ℝ)+(53580209173/12500000000000000000 : ℝ) ≤ ((627449325262437157/627500000000000000 : ℝ)+(318717210347/75300000000000 : ℝ)*((27309/100000 : ℝ)+(477/50000 : ℝ)))^(4241/1024 : ℝ) := by
    rw [show (627449325262437157/627500000000000000 : ℝ)+(318717210347/75300000000000 : ℝ)*((27309/100000 : ℝ)+(477/50000 : ℝ))=(2002231024612293/2000000000000000 : ℝ) by norm_num, show 1+(462810506942914217/100000000000000000000 : ℝ)+(53580209173/12500000000000000000 : ℝ)=(100462810935584587601/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(462810506942914217/100000000000000000000 : ℝ) ≤ ((627449325262437157/627500000000000000 : ℝ)+2*(318717210347/75300000000000 : ℝ)*(27309/100000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (627449325262437157/627500000000000000 : ℝ)+2*(318717210347/75300000000000 : ℝ)*(27309/100000 : ℝ)=(1002231022542361/1000000000000000 : ℝ) by norm_num, show 1+2*(462810506942914217/100000000000000000000 : ℝ)=(50462810506942914217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (627449325262437157/627500000000000000 : ℝ)*(X 1 0+X 2 0)+(318717210347/75300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (477/50000 : ℝ)) (hi := (27309/100000 : ℝ)) (c := (627449325262437157/627500000000000000 : ℝ)) (alpha := (318717210347/75300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (627449325262437157/627500000000000000 : ℝ)*(X 0 1+X 2 1)+(318717210347/75300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (477/50000 : ℝ)) (hi := (27309/100000 : ℝ)) (c := (627449325262437157/627500000000000000 : ℝ)) (alpha := (318717210347/75300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (627449325262437157/627500000000000000 : ℝ)*(X 0 2+X 1 2)+(318717210347/75300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (477/50000 : ℝ)) (hi := (27309/100000 : ℝ)) (c := (627449325262437157/627500000000000000 : ℝ)) (alpha := (318717210347/75300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-127415591/625000000 : ℝ)*X 0 0+(708766019/1250000000 : ℝ)*X 0 1+(5025627363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((135301233/250000000 : ℝ)*X 1 0+(-1192204597/5000000000 : ℝ)*X 1 1+(1005125511/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1353012371/2500000000 : ℝ)*X 2 0+(201025099/400000000 : ℝ)*X 2 1+(-2384409081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86057769/200000000 : ℝ)*X 0 0+(922812457/2500000000 : ℝ)*X 0 1+(6263491/12500000 : ℝ)*X 0 2+(86057769/200000000 : ℝ)*X 1 0+(922812457/2500000000 : ℝ)*X 1 1+(6263491/12500000 : ℝ)*X 1 2+(86057769/200000000 : ℝ)*X 2 0+(922812457/2500000000 : ℝ)*X 2 1+(6263491/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1019654173/5000000000 : ℝ)*X 0 0+(5034094199/10000000000 : ℝ)*X 0 1+(5661500121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5245682897/10000000000 : ℝ)*X 1 0+(-17485363/100000000 : ℝ)*X 1 1+(2830750291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2622841403/5000000000 : ℝ)*X 2 0+(2830750131/5000000000 : ℝ)*X 2 1+(-1748536893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((860847429/2000000000 : ℝ)*X 0 0+(4993458077/10000000000 : ℝ)*X 0 1+(3708914969/10000000000 : ℝ)*X 0 2+(860847429/2000000000 : ℝ)*X 1 0+(4993458077/10000000000 : ℝ)*X 1 1+(3708914969/10000000000 : ℝ)*X 1 2+(860847429/2000000000 : ℝ)*X 2 0+(4993458077/10000000000 : ℝ)*X 2 1+(3708914969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64651986664868590854433959/7843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67790871/100000000000000 : ℝ)*(base1) + (1822666771/100000000000000 : ℝ)*(base19) + (1869684767/100000000000000 : ℝ)*(base23) + (47117869/25000000000000 : ℝ)*(upper3) + (121556743/50000000000000 : ℝ)*(upper5) + (577364809191579/50000000000000 : ℝ)*(major0) + (577364809191579/50000000000000 : ℝ)*(major1) + (577364809191579/50000000000000 : ℝ)*(major2) + (310319746529507/20000000000000 : ℝ)*(sp0) + (1551608069477049/100000000000000 : ℝ)*(sp1) + (1551608022459053/100000000000000 : ℝ)*(sp2) + (189460900185329/25000000000000 : ℝ)*(sp3) + (2806821789/25000000000000 : ℝ)*(sp4) + (5401340827/100000000000000 : ℝ)*(sp7) + (757849069873013/100000000000000 : ℝ)*(f.failure) + (77580494607191/5000000000000 : ℝ)*(f.sum) + (1072808867297/1255000000000000000000000000 : ℝ)*base65 + (298426704319749097/31375000000000000000000000000000 : ℝ)*base68 + (60902064545124097/31375000000000000000000000000000 : ℝ)*base70 + (149171408707749097/31375000000000000000000000000000 : ℝ)*base72 + (2149015388413/1255000000000000000000000000 : ℝ)*base74 + (53044433253125903/31375000000000000000000000000000 : ℝ)*base75 + (224588185579249097/31375000000000000000000000000000 : ℝ)*base78 + (34737644389874097/31375000000000000000000000000000 : ℝ)*base80 + (1746943713773/313750000000000000000000000 : ℝ)*base81 + (4748407/10000000000000000000000 : ℝ)*base89 + (4748407/10000000000000000000000 : ℝ)*base91 + (4748407/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14239706629291735007292789/3137500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (803465619/100000000000000 : ℝ)*(base19) + (750156773/100000000000000 : ℝ)*(base23) + (6465427/100000000000000 : ℝ)*(upper2) + (134096221/100000000000000 : ℝ)*(upper3) + (37647/39062500000 : ℝ)*(upper5) + (237235096821059/20000000000000 : ℝ)*(major0) + (237235096821059/20000000000000 : ℝ)*(major1) + (237235096821059/20000000000000 : ℝ)*(major2) + (2264323231/50000000000000 : ℝ)*(sp1) + (832739899/25000000000000 : ℝ)*(sp2) + (318772764959651/20000000000000 : ℝ)*(sp4) + (1593858492686173/100000000000000 : ℝ)*(sp5) + (318771948736377/20000000000000 : ℝ)*(sp6) + (155697398425453/20000000000000 : ℝ)*(sp7) + (155697398425453/20000000000000 : ℝ)*(f.failure) + (318772764959651/20000000000000 : ℝ)*(f.sum) + (891123457681/376500000000000000000000000 : ℝ)*base66 + (447549176625607211/37650000000000000000000000000000 : ℝ)*base68 + (47059593974107211/37650000000000000000000000000000 : ℝ)*base70 + (30329018520007211/37650000000000000000000000000000 : ℝ)*base72 + (1399367190977/188250000000000000000000000 : ℝ)*base74 + (179584963352242789/37650000000000000000000000000000 : ℝ)*base75 + (88793021070457211/37650000000000000000000000000000 : ℝ)*base78 + (97548422246857211/37650000000000000000000000000000 : ℝ)*base80 + (1083495628861/753000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14385567/2000000000000000000000 : ℝ)*base89 + (14385567/2000000000000000000000 : ℝ)*base91 + (14385567/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1282_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27309/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1577/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19931/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1282_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1282_s2_0 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1042148323/5000000000 : ℝ)*x 0 + (5497360851/10000000000 : ℝ)*x 1 + (5169255401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042148323/5000000000 : ℝ)^2121 ≤ (12654517625669/100000000000000 : ℝ)^1609 := by
    have hnat : (1042148323 : ℕ)^2121*100000000000000^1609 ≤ 12654517625669^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042148323 5000000000 12654517625669 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497360851/10000000000 : ℝ)^2121 ≤ (9088635902877/20000000000000 : ℝ)^1609 := by
    have hnat : (5497360851 : ℕ)^2121*20000000000000^1609 ≤ 9088635902877^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497360851 10000000000 9088635902877 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169255401/10000000000 : ℝ)^2121 ≤ (20951151422537/50000000000000 : ℝ)^1609 := by
    have hnat : (5169255401 : ℕ)^2121*50000000000000^1609 ≤ 20951151422537^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169255401 10000000000 20951151422537 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1042148323/5000000000 : ℝ), (5497360851/10000000000 : ℝ), (5169255401/10000000000 : ℝ)] ![(12654517625669/100000000000000 : ℝ), (9088635902877/20000000000000 : ℝ), (20951151422537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1042148323/5000000000 : ℝ)|^2121 ≤ (12654517625669/100000000000000 : ℝ)^1609
        have hw : |(-1042148323/5000000000 : ℝ)|=(1042148323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497360851/10000000000 : ℝ)|^2121 ≤ (9088635902877/20000000000000 : ℝ)^1609
        have hw : |(5497360851/10000000000 : ℝ)|=(5497360851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169255401/10000000000 : ℝ)|^2121 ≤ (20951151422537/50000000000000 : ℝ)^1609
        have hw : |(5169255401/10000000000 : ℝ)|=(5169255401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s2_1 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370336929/10000000000 : ℝ)*x 0 + (-225443387/1000000000 : ℝ)*x 1 + (646157013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370336929/10000000000 : ℝ)^2121 ≤ (1377004390471/3125000000000 : ℝ)^1609 := by
    have hnat : (5370336929 : ℕ)^2121*3125000000000^1609 ≤ 1377004390471^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370336929 10000000000 1377004390471 3125000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225443387/1000000000 : ℝ)^2121 ≤ (14033549128459/100000000000000 : ℝ)^1609 := by
    have hnat : (225443387 : ℕ)^2121*100000000000000^1609 ≤ 14033549128459^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225443387 1000000000 14033549128459 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646157013/1250000000 : ℝ)^2121 ≤ (1676092414279/4000000000000 : ℝ)^1609 := by
    have hnat : (646157013 : ℕ)^2121*4000000000000^1609 ≤ 1676092414279^1609*1250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646157013 1250000000 1676092414279 4000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370336929/10000000000 : ℝ), (-225443387/1000000000 : ℝ), (646157013/1250000000 : ℝ)] ![(1377004390471/3125000000000 : ℝ), (14033549128459/100000000000000 : ℝ), (1676092414279/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370336929/10000000000 : ℝ)|^2121 ≤ (1377004390471/3125000000000 : ℝ)^1609
        have hw : |(5370336929/10000000000 : ℝ)|=(5370336929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-225443387/1000000000 : ℝ)|^2121 ≤ (14033549128459/100000000000000 : ℝ)^1609
        have hw : |(-225443387/1000000000 : ℝ)|=(225443387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646157013/1250000000 : ℝ)|^2121 ≤ (1676092414279/4000000000000 : ℝ)^1609
        have hw : |(646157013/1250000000 : ℝ)|=(646157013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s2_2 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370337339/10000000000 : ℝ)*x 0 + (1033851101/2000000000 : ℝ)*x 1 + (-225443411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370337339/10000000000 : ℝ)^2121 ≤ (44064144929649/100000000000000 : ℝ)^1609 := by
    have hnat : (5370337339 : ℕ)^2121*100000000000000^1609 ≤ 44064144929649^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370337339 10000000000 44064144929649 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033851101/2000000000 : ℝ)^2121 ≤ (8380460791273/20000000000000 : ℝ)^1609 := by
    have hnat : (1033851101 : ℕ)^2121*20000000000000^1609 ≤ 8380460791273^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033851101 2000000000 8380460791273 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225443411/1000000000 : ℝ)^2121 ≤ (7016775548911/50000000000000 : ℝ)^1609 := by
    have hnat : (225443411 : ℕ)^2121*50000000000000^1609 ≤ 7016775548911^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225443411 1000000000 7016775548911 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370337339/10000000000 : ℝ), (1033851101/2000000000 : ℝ), (-225443411/1000000000 : ℝ)] ![(44064144929649/100000000000000 : ℝ), (8380460791273/20000000000000 : ℝ), (7016775548911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370337339/10000000000 : ℝ)|^2121 ≤ (44064144929649/100000000000000 : ℝ)^1609
        have hw : |(5370337339/10000000000 : ℝ)|=(5370337339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033851101/2000000000 : ℝ)|^2121 ≤ (8380460791273/20000000000000 : ℝ)^1609
        have hw : |(1033851101/2000000000 : ℝ)|=(1033851101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225443411/1000000000 : ℝ)|^2121 ≤ (7016775548911/50000000000000 : ℝ)^1609
        have hw : |(-225443411/1000000000 : ℝ)|=(225443411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s2_3 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1083644823/2500000000 : ℝ)*x 0 + (4011152899/10000000000 : ℝ)*x 1 + (46829179/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083644823/2500000000 : ℝ)^2121 ≤ (8305386072651/25000000000000 : ℝ)^1609 := by
    have hnat : (1083644823 : ℕ)^2121*25000000000000^1609 ≤ 8305386072651^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083644823 2500000000 8305386072651 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4011152899/10000000000 : ℝ)^2121 ≤ (29993385352833/100000000000000 : ℝ)^1609 := by
    have hnat : (4011152899 : ℕ)^2121*100000000000000^1609 ≤ 29993385352833^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011152899 10000000000 29993385352833 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46829179/100000000 : ℝ)^2121 ≤ (9196267584033/25000000000000 : ℝ)^1609 := by
    have hnat : (46829179 : ℕ)^2121*25000000000000^1609 ≤ 9196267584033^1609*100000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46829179 100000000 9196267584033 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083644823/2500000000 : ℝ), (4011152899/10000000000 : ℝ), (46829179/100000000 : ℝ)] ![(8305386072651/25000000000000 : ℝ), (29993385352833/100000000000000 : ℝ), (9196267584033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083644823/2500000000 : ℝ)|^2121 ≤ (8305386072651/25000000000000 : ℝ)^1609
        have hw : |(1083644823/2500000000 : ℝ)|=(1083644823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4011152899/10000000000 : ℝ)|^2121 ≤ (29993385352833/100000000000000 : ℝ)^1609
        have hw : |(4011152899/10000000000 : ℝ)|=(4011152899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46829179/100000000 : ℝ)|^2121 ≤ (9196267584033/25000000000000 : ℝ)^1609
        have hw : |(46829179/100000000 : ℝ)|=(46829179/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s2_4 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084382703/10000000000 : ℝ)*x 0 + (5171459403/10000000000 : ℝ)*x 1 + (5495136093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084382703/10000000000 : ℝ)^2121 ≤ (3163801593177/25000000000000 : ℝ)^1609 := by
    have hnat : (2084382703 : ℕ)^2121*25000000000000^1609 ≤ 3163801593177^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084382703 10000000000 3163801593177 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5171459403/10000000000 : ℝ)^2121 ≤ (20962927644197/50000000000000 : ℝ)^1609 := by
    have hnat : (5171459403 : ℕ)^2121*50000000000000^1609 ≤ 20962927644197^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171459403 10000000000 20962927644197 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495136093/10000000000 : ℝ)^2121 ≤ (45418938326431/100000000000000 : ℝ)^1609 := by
    have hnat : (5495136093 : ℕ)^2121*100000000000000^1609 ≤ 45418938326431^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495136093 10000000000 45418938326431 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084382703/10000000000 : ℝ), (5171459403/10000000000 : ℝ), (5495136093/10000000000 : ℝ)] ![(3163801593177/25000000000000 : ℝ), (20962927644197/50000000000000 : ℝ), (45418938326431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084382703/10000000000 : ℝ)|^2121 ≤ (3163801593177/25000000000000 : ℝ)^1609
        have hw : |(-2084382703/10000000000 : ℝ)|=(2084382703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5171459403/10000000000 : ℝ)|^2121 ≤ (20962927644197/50000000000000 : ℝ)^1609
        have hw : |(5171459403/10000000000 : ℝ)|=(5171459403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495136093/10000000000 : ℝ)|^2121 ≤ (45418938326431/100000000000000 : ℝ)^1609
        have hw : |(5495136093/10000000000 : ℝ)|=(5495136093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s2_5 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5286343213/10000000000 : ℝ)*x 0 + (-482138301/2500000000 : ℝ)*x 1 + (686892031/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286343213/10000000000 : ℝ)^2121 ≤ (43157929670841/100000000000000 : ℝ)^1609 := by
    have hnat : (5286343213 : ℕ)^2121*100000000000000^1609 ≤ 43157929670841^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286343213 10000000000 43157929670841 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482138301/2500000000 : ℝ)^2121 ≤ (1142313030401/10000000000000 : ℝ)^1609 := by
    have hnat : (482138301 : ℕ)^2121*10000000000000^1609 ≤ 1142313030401^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482138301 2500000000 1142313030401 10000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686892031/1250000000 : ℝ)^2121 ≤ (22709470007609/50000000000000 : ℝ)^1609 := by
    have hnat : (686892031 : ℕ)^2121*50000000000000^1609 ≤ 22709470007609^1609*1250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686892031 1250000000 22709470007609 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286343213/10000000000 : ℝ), (-482138301/2500000000 : ℝ), (686892031/1250000000 : ℝ)] ![(43157929670841/100000000000000 : ℝ), (1142313030401/10000000000000 : ℝ), (22709470007609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286343213/10000000000 : ℝ)|^2121 ≤ (43157929670841/100000000000000 : ℝ)^1609
        have hw : |(5286343213/10000000000 : ℝ)|=(5286343213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-482138301/2500000000 : ℝ)|^2121 ≤ (1142313030401/10000000000000 : ℝ)^1609
        have hw : |(-482138301/2500000000 : ℝ)|=(482138301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686892031/1250000000 : ℝ)|^2121 ≤ (22709470007609/50000000000000 : ℝ)^1609
        have hw : |(686892031/1250000000 : ℝ)|=(686892031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s2_6 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321585849/2500000000 : ℝ)*x 0 + (2747568051/5000000000 : ℝ)*x 1 + (-385710631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321585849/2500000000 : ℝ)^2121 ≤ (43157931640273/100000000000000 : ℝ)^1609 := by
    have hnat : (1321585849 : ℕ)^2121*100000000000000^1609 ≤ 43157931640273^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321585849 2500000000 43157931640273 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747568051/5000000000 : ℝ)^2121 ≤ (4541893842449/10000000000000 : ℝ)^1609 := by
    have hnat : (2747568051 : ℕ)^2121*10000000000000^1609 ≤ 4541893842449^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747568051 5000000000 4541893842449 10000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385710631/2000000000 : ℝ)^2121 ≤ (11423129921419/100000000000000 : ℝ)^1609 := by
    have hnat : (385710631 : ℕ)^2121*100000000000000^1609 ≤ 11423129921419^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385710631 2000000000 11423129921419 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321585849/2500000000 : ℝ), (2747568051/5000000000 : ℝ), (-385710631/2000000000 : ℝ)] ![(43157931640273/100000000000000 : ℝ), (4541893842449/10000000000000 : ℝ), (11423129921419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321585849/2500000000 : ℝ)|^2121 ≤ (43157931640273/100000000000000 : ℝ)^1609
        have hw : |(1321585849/2500000000 : ℝ)|=(1321585849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747568051/5000000000 : ℝ)|^2121 ≤ (4541893842449/10000000000000 : ℝ)^1609
        have hw : |(2747568051/5000000000 : ℝ)|=(2747568051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-385710631/2000000000 : ℝ)|^2121 ≤ (11423129921419/100000000000000 : ℝ)^1609
        have hw : |(-385710631/2000000000 : ℝ)|=(385710631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s2_7 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (433475567/1000000000 : ℝ)*x 0 + (2339202181/5000000000 : ℝ)*x 1 + (62745501/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433475567/1000000000 : ℝ)^2121 ≤ (6644665255671/20000000000000 : ℝ)^1609 := by
    have hnat : (433475567 : ℕ)^2121*20000000000000^1609 ≤ 6644665255671^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433475567 1000000000 6644665255671 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2339202181/5000000000 : ℝ)^2121 ≤ (36738340941419/100000000000000 : ℝ)^1609 := by
    have hnat : (2339202181 : ℕ)^2121*100000000000000^1609 ≤ 36738340941419^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339202181 5000000000 36738340941419 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62745501/156250000 : ℝ)^2121 ≤ (30038332767463/100000000000000 : ℝ)^1609 := by
    have hnat : (62745501 : ℕ)^2121*100000000000000^1609 ≤ 30038332767463^1609*156250000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62745501 156250000 30038332767463 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433475567/1000000000 : ℝ), (2339202181/5000000000 : ℝ), (62745501/156250000 : ℝ)] ![(6644665255671/20000000000000 : ℝ), (36738340941419/100000000000000 : ℝ), (30038332767463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433475567/1000000000 : ℝ)|^2121 ≤ (6644665255671/20000000000000 : ℝ)^1609
        have hw : |(433475567/1000000000 : ℝ)|=(433475567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2339202181/5000000000 : ℝ)|^2121 ≤ (36738340941419/100000000000000 : ℝ)^1609
        have hw : |(2339202181/5000000000 : ℝ)|=(2339202181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62745501/156250000 : ℝ)|^2121 ≤ (30038332767463/100000000000000 : ℝ)^1609
        have hw : |(62745501/156250000 : ℝ)|=(62745501/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1282_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1577/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (943/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4091/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1577/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1577/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1577/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1577/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1577/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1577/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1577/25000 : ℝ) ^ (4241/1024 : ℝ) ≤ (1070605637704407/100000000000000000000 : ℝ) := by
    have hpowers : (1577/25000 : ℝ)^4241 ≤ (1070605637704407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1577 : ℕ)^4241*100000000000000000000^1024 ≤ 1070605637704407^1024*25000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1577 25000 1070605637704407 100000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1577/25000 : ℝ)) (X := (1070605637704407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19931/100000 : ℝ) ^ (4241/1024 : ℝ) ≤ (125582342900945477/100000000000000000000 : ℝ) := by
    have hpowers : (19931/100000 : ℝ)^4241 ≤ (125582342900945477/100000000000000000000 : ℝ)^1024 := by
      have hnat : (19931 : ℕ)^4241*100000000000000000000^1024 ≤ 125582342900945477^1024*100000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19931 100000 125582342900945477 100000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19931/100000 : ℝ)) (X := (125582342900945477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001070605637704407/50000000000000000000 : ℝ) ≤ (2500012924914761/2500000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (50001070605637704407/50000000000000000000 : ℝ)^1024 ≤ (2500012924914761/2500000000000000 : ℝ)^4241 := by
      have hnat : (50001070605637704407 : ℕ)^1024*2500000000000000^4241 ≤ 2500012924914761^4241*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001070605637704407 50000000000000000000 2500012924914761 2500000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500012924914761/2500000000000000 : ℝ)) (X := (50001070605637704407/50000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25031663237134662471/25000000000000000000 : ℝ) ≤ (5001528299530627/5000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (25031663237134662471/25000000000000000000 : ℝ)^1024 ≤ (5001528299530627/5000000000000000 : ℝ)^4241 := by
      have hnat : (25031663237134662471 : ℕ)^1024*5000000000000000^4241 ≤ 5001528299530627^4241*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25031663237134662471 25000000000000000000 5001528299530627 5000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001528299530627/5000000000000000 : ℝ)) (X := (25031663237134662471/25000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50125582342900945477/50000000000000000000 : ℝ) ≤ (1250757687307933/1250000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (50125582342900945477/50000000000000000000 : ℝ)^1024 ≤ (1250757687307933/1250000000000000 : ℝ)^4241 := by
      have hnat : (50125582342900945477 : ℕ)^1024*1250000000000000^4241 ≤ 1250757687307933^4241*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50125582342900945477 50000000000000000000 1250757687307933 1250000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250757687307933/1250000000000000 : ℝ)) (X := (50125582342900945477/50000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1070605637704407/100000000000000000000 : ℝ) ≤ ((597336817954372259/597500000000000000 : ℝ)+2*(100163313407/45410000000000 : ℝ)*(1577/25000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (597336817954372259/597500000000000000 : ℝ)+2*(100163313407/45410000000000 : ℝ)*(1577/25000 : ℝ)=(2500012924914761/2500000000000000 : ℝ) by norm_num, show 1+2*(1070605637704407/100000000000000000000 : ℝ)=(50001070605637704407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(125582342900945477/100000000000000000000 : ℝ)+(1070605637704407/100000000000000000000 : ℝ) ≤ ((597336817954372259/597500000000000000 : ℝ)+(100163313407/45410000000000 : ℝ)*((19931/100000 : ℝ)+(1577/25000 : ℝ)))^(4241/1024 : ℝ) := by
    rw [show (597336817954372259/597500000000000000 : ℝ)+(100163313407/45410000000000 : ℝ)*((19931/100000 : ℝ)+(1577/25000 : ℝ))=(5001528299530627/5000000000000000 : ℝ) by norm_num, show 1+(125582342900945477/100000000000000000000 : ℝ)+(1070605637704407/100000000000000000000 : ℝ)=(25031663237134662471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(125582342900945477/100000000000000000000 : ℝ) ≤ ((597336817954372259/597500000000000000 : ℝ)+2*(100163313407/45410000000000 : ℝ)*(19931/100000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (597336817954372259/597500000000000000 : ℝ)+2*(100163313407/45410000000000 : ℝ)*(19931/100000 : ℝ)=(1250757687307933/1250000000000000 : ℝ) by norm_num, show 1+2*(125582342900945477/100000000000000000000 : ℝ)=(50125582342900945477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (597336817954372259/597500000000000000 : ℝ)*(X 1 0+X 2 0)+(100163313407/45410000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (1577/25000 : ℝ)) (hi := (19931/100000 : ℝ)) (c := (597336817954372259/597500000000000000 : ℝ)) (alpha := (100163313407/45410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (597336817954372259/597500000000000000 : ℝ)*(X 0 1+X 2 1)+(100163313407/45410000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (1577/25000 : ℝ)) (hi := (19931/100000 : ℝ)) (c := (597336817954372259/597500000000000000 : ℝ)) (alpha := (100163313407/45410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (597336817954372259/597500000000000000 : ℝ)*(X 0 2+X 1 2)+(100163313407/45410000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (1577/25000 : ℝ)) (hi := (19931/100000 : ℝ)) (c := (597336817954372259/597500000000000000 : ℝ)) (alpha := (100163313407/45410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1042148323/5000000000 : ℝ)*X 0 0+(5497360851/10000000000 : ℝ)*X 0 1+(5169255401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370336929/10000000000 : ℝ)*X 1 0+(-225443387/1000000000 : ℝ)*X 1 1+(646157013/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370337339/10000000000 : ℝ)*X 2 0+(1033851101/2000000000 : ℝ)*X 2 1+(-225443411/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083644823/2500000000 : ℝ)*X 0 0+(4011152899/10000000000 : ℝ)*X 0 1+(46829179/100000000 : ℝ)*X 0 2+(1083644823/2500000000 : ℝ)*X 1 0+(4011152899/10000000000 : ℝ)*X 1 1+(46829179/100000000 : ℝ)*X 1 2+(1083644823/2500000000 : ℝ)*X 2 0+(4011152899/10000000000 : ℝ)*X 2 1+(46829179/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2084382703/10000000000 : ℝ)*X 0 0+(5171459403/10000000000 : ℝ)*X 0 1+(5495136093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5286343213/10000000000 : ℝ)*X 1 0+(-482138301/2500000000 : ℝ)*X 1 1+(686892031/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321585849/2500000000 : ℝ)*X 2 0+(2747568051/5000000000 : ℝ)*X 2 1+(-385710631/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((433475567/1000000000 : ℝ)*X 0 0+(2339202181/5000000000 : ℝ)*X 0 1+(62745501/156250000 : ℝ)*X 0 2+(433475567/1000000000 : ℝ)*X 1 0+(2339202181/5000000000 : ℝ)*X 1 1+(62745501/156250000 : ℝ)*X 1 2+(433475567/1000000000 : ℝ)*X 2 0+(2339202181/5000000000 : ℝ)*X 2 1+(62745501/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (240408624523969220699806761/35476562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1101998131/50000000000000 : ℝ)*(base19) + (1171412351/50000000000000 : ℝ)*(base23) + (25203069/50000000000000 : ℝ)*(lower2) + (534156161/100000000000000 : ℝ)*(upper3) + (341606927/100000000000000 : ℝ)*(upper5) + (70882838805963/3125000000000 : ℝ)*(major0) + (70882838805963/3125000000000 : ℝ)*(major1) + (70882838805963/3125000000000 : ℝ)*(major2) + (1523912766645501/50000000000000 : ℝ)*(sp0) + (3047846184337953/100000000000000 : ℝ)*(sp1) + (3047846045509513/100000000000000 : ℝ)*(sp2) + (37215829572823/2500000000000 : ℝ)*(sp3) + (22855043213/100000000000000 : ℝ)*(sp4) + (3977289911/20000000000000 : ℝ)*(sp7) + (372163267340619/25000000000000 : ℝ)*(f.failure) + (380981048541777/12500000000000 : ℝ)*(f.sum) + (563113520181/908200000000000000000000000 : ℝ)*base65 + (942515832122896471/70953125000000000000000000000000 : ℝ)*base67 + (555372195972896471/70953125000000000000000000000000 : ℝ)*base69 + (341238666323896471/70953125000000000000000000000000 : ℝ)*base71 + (3367913299893/567625000000000000000000000 : ℝ)*base73 + (330194017978315423/35476562500000000000000000000000 : ℝ)*base75 + (303531368083740221/70953125000000000000000000000000 : ℝ)*base77 + (1000727583474708971/70953125000000000000000000000000 : ℝ)*base79 + (7669015340267/2270500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4880841/2500000000000000000000 : ℝ)*base89 + (4880841/2500000000000000000000 : ℝ)*base91 + (4880841/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1202360557916844449731654059/141906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (318662009/20000000000000 : ℝ)*(base19) + (1939635041/100000000000000 : ℝ)*(base23) + (242321421/100000000000000 : ℝ)*(upper3) + (11269551/12500000000000 : ℝ)*(lower4) + (24689121/20000000000000 : ℝ)*(upper5) + (574812135024207/25000000000000 : ℝ)*(major0) + (574812135024207/25000000000000 : ℝ)*(major1) + (574812135024207/25000000000000 : ℝ)*(major2) + (16058980713/100000000000000 : ℝ)*(sp1) + (1274425261/6250000000000 : ℝ)*(sp2) + (3089499938429679/100000000000000 : ℝ)*(sp4) + (77237057153473/2500000000000 : ℝ)*(sp5) + (1544738803995231/50000000000000 : ℝ)*(sp6) + (1508996859333247/100000000000000 : ℝ)*(sp7) + (1508996859333247/100000000000000 : ℝ)*(f.failure) + (3089499938429679/100000000000000 : ℝ)*(f.sum) + (4047753413219/4541000000000000000000000000 : ℝ)*base65 + (1243581148156511147/283812500000000000000000000000000 : ℝ)*base67 + (922801813465011147/283812500000000000000000000000000 : ℝ)*base69 + (1188971145730511147/283812500000000000000000000000000 : ℝ)*base71 + (197908992913/283812500000000000000000000 : ℝ)*base73 + (2303892992260948647/283812500000000000000000000000000 : ℝ)*base75 + (342145149453176353/283812500000000000000000000000000 : ℝ)*base78 + (190814710127676353/283812500000000000000000000000000 : ℝ)*base80 + (647902200317/2270500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (26113733/10000000000000000000000 : ℝ)*base89 + (26113733/10000000000000000000000 : ℝ)*base91 + (26113733/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1282_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1577/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1282_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1282_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1282_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1282_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1282_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1282_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

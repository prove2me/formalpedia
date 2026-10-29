-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1425_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:50.139276+00:00
-- url     : https://prove2.me/submissions/67b79c83-da50-4023-8f7d-2e0ad2ebc023

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
theorem support_rectangle_w1425_s0_0 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1761080639/10000000000 : ℝ)*x 0 + (5961833427/10000000000 : ℝ)*x 1 + (1207580581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1761080639/10000000000 : ℝ)^4385 ≤ (10375042336871/100000000000000 : ℝ)^3361 := by
    have hnat : (1761080639 : ℕ)^4385*100000000000000^3361 ≤ 10375042336871^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761080639 10000000000 10375042336871 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5961833427/10000000000 : ℝ)^4385 ≤ (25463291464489/50000000000000 : ℝ)^3361 := by
    have hnat : (5961833427 : ℕ)^4385*50000000000000^3361 ≤ 25463291464489^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5961833427 10000000000 25463291464489 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207580581/2500000000 : ℝ)^4385 ≤ (4837296839391/12500000000000 : ℝ)^3361 := by
    have hnat : (1207580581 : ℕ)^4385*12500000000000^3361 ≤ 4837296839391^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207580581 2500000000 4837296839391 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1761080639/10000000000 : ℝ), (5961833427/10000000000 : ℝ), (1207580581/2500000000 : ℝ)] ![(10375042336871/100000000000000 : ℝ), (25463291464489/50000000000000 : ℝ), (4837296839391/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1761080639/10000000000 : ℝ)|^4385 ≤ (10375042336871/100000000000000 : ℝ)^3361
        have hw : |(-1761080639/10000000000 : ℝ)|=(1761080639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5961833427/10000000000 : ℝ)|^4385 ≤ (25463291464489/50000000000000 : ℝ)^3361
        have hw : |(5961833427/10000000000 : ℝ)|=(5961833427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207580581/2500000000 : ℝ)|^4385 ≤ (4837296839391/12500000000000 : ℝ)^3361
        have hw : |(1207580581/2500000000 : ℝ)|=(1207580581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s0_1 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2746272089/5000000000 : ℝ)*x 0 + (-1200222387/5000000000 : ℝ)*x 1 + (2415161371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2746272089/5000000000 : ℝ)^4385 ≤ (11440106245199/25000000000000 : ℝ)^3361 := by
    have hnat : (2746272089 : ℕ)^4385*25000000000000^3361 ≤ 11440106245199^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746272089 5000000000 11440106245199 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1200222387/5000000000 : ℝ)^4385 ≤ (15541195914689/100000000000000 : ℝ)^3361 := by
    have hnat : (1200222387 : ℕ)^4385*100000000000000^3361 ≤ 15541195914689^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200222387 5000000000 15541195914689 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2415161371/5000000000 : ℝ)^4385 ≤ (4837297385531/12500000000000 : ℝ)^3361 := by
    have hnat : (2415161371 : ℕ)^4385*12500000000000^3361 ≤ 4837297385531^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415161371 5000000000 4837297385531 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2746272089/5000000000 : ℝ), (-1200222387/5000000000 : ℝ), (2415161371/5000000000 : ℝ)] ![(11440106245199/25000000000000 : ℝ), (15541195914689/100000000000000 : ℝ), (4837297385531/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2746272089/5000000000 : ℝ)|^4385 ≤ (11440106245199/25000000000000 : ℝ)^3361
        have hw : |(2746272089/5000000000 : ℝ)|=(2746272089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1200222387/5000000000 : ℝ)|^4385 ≤ (15541195914689/100000000000000 : ℝ)^3361
        have hw : |(-1200222387/5000000000 : ℝ)|=(1200222387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2415161371/5000000000 : ℝ)|^4385 ≤ (4837297385531/12500000000000 : ℝ)^3361
        have hw : |(2415161371/5000000000 : ℝ)|=(2415161371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s0_2 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1373136149/2500000000 : ℝ)*x 0 + (4830322569/10000000000 : ℝ)*x 1 + (-2400444451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1373136149/2500000000 : ℝ)^4385 ≤ (45760429524331/100000000000000 : ℝ)^3361 := by
    have hnat : (1373136149 : ℕ)^4385*100000000000000^3361 ≤ 45760429524331^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373136149 2500000000 45760429524331 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4830322569/10000000000 : ℝ)^4385 ≤ (4837297159497/12500000000000 : ℝ)^3361 := by
    have hnat : (4830322569 : ℕ)^4385*12500000000000^3361 ≤ 4837297159497^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4830322569 10000000000 4837297159497 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2400444451/10000000000 : ℝ)^4385 ≤ (7770596593181/50000000000000 : ℝ)^3361 := by
    have hnat : (2400444451 : ℕ)^4385*50000000000000^3361 ≤ 7770596593181^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400444451 10000000000 7770596593181 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1373136149/2500000000 : ℝ), (4830322569/10000000000 : ℝ), (-2400444451/10000000000 : ℝ)] ![(45760429524331/100000000000000 : ℝ), (4837297159497/12500000000000 : ℝ), (7770596593181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1373136149/2500000000 : ℝ)|^4385 ≤ (45760429524331/100000000000000 : ℝ)^3361
        have hw : |(1373136149/2500000000 : ℝ)|=(1373136149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4830322569/10000000000 : ℝ)|^4385 ≤ (4837297159497/12500000000000 : ℝ)^3361
        have hw : |(4830322569/10000000000 : ℝ)|=(4830322569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2400444451/10000000000 : ℝ)|^4385 ≤ (7770596593181/50000000000000 : ℝ)^3361
        have hw : |(-2400444451/10000000000 : ℝ)|=(2400444451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s0_3 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166574909/10000000000 : ℝ)*x 0 + (1551728801/5000000000 : ℝ)*x 1 + (5547708153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166574909/10000000000 : ℝ)^4385 ≤ (797768460771/2500000000000 : ℝ)^3361 := by
    have hnat : (4166574909 : ℕ)^4385*2500000000000^3361 ≤ 797768460771^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166574909 10000000000 797768460771 2500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551728801/5000000000 : ℝ)^4385 ≤ (10864152708489/50000000000000 : ℝ)^3361 := by
    have hnat : (1551728801 : ℕ)^4385*50000000000000^3361 ≤ 10864152708489^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551728801 5000000000 10864152708489 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5547708153/10000000000 : ℝ)^4385 ≤ (1854438245331/4000000000000 : ℝ)^3361 := by
    have hnat : (5547708153 : ℕ)^4385*4000000000000^3361 ≤ 1854438245331^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5547708153 10000000000 1854438245331 4000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166574909/10000000000 : ℝ), (1551728801/5000000000 : ℝ), (5547708153/10000000000 : ℝ)] ![(797768460771/2500000000000 : ℝ), (10864152708489/50000000000000 : ℝ), (1854438245331/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166574909/10000000000 : ℝ)|^4385 ≤ (797768460771/2500000000000 : ℝ)^3361
        have hw : |(4166574909/10000000000 : ℝ)|=(4166574909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551728801/5000000000 : ℝ)|^4385 ≤ (10864152708489/50000000000000 : ℝ)^3361
        have hw : |(1551728801/5000000000 : ℝ)|=(1551728801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5547708153/10000000000 : ℝ)|^4385 ≤ (1854438245331/4000000000000 : ℝ)^3361
        have hw : |(5547708153/10000000000 : ℝ)|=(5547708153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s0_4 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6894989/39062500 : ℝ)*x 0 + (4859281951/10000000000 : ℝ)*x 1 + (5931839811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6894989/39062500 : ℝ)^4385 ≤ (325189964351/3125000000000 : ℝ)^3361 := by
    have hnat : (6894989 : ℕ)^4385*3125000000000^3361 ≤ 325189964351^3361*39062500^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6894989 39062500 325189964351 3125000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4859281951/10000000000 : ℝ)^4385 ≤ (39001349564363/100000000000000 : ℝ)^3361 := by
    have hnat : (4859281951 : ℕ)^4385*100000000000000^3361 ≤ 39001349564363^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859281951 10000000000 39001349564363 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5931839811/10000000000 : ℝ)^4385 ≤ (25296285777811/50000000000000 : ℝ)^3361 := by
    have hnat : (5931839811 : ℕ)^4385*50000000000000^3361 ≤ 25296285777811^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5931839811 10000000000 25296285777811 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6894989/39062500 : ℝ), (4859281951/10000000000 : ℝ), (5931839811/10000000000 : ℝ)] ![(325189964351/3125000000000 : ℝ), (39001349564363/100000000000000 : ℝ), (25296285777811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6894989/39062500 : ℝ)|^4385 ≤ (325189964351/3125000000000 : ℝ)^3361
        have hw : |(-6894989/39062500 : ℝ)|=(6894989/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4859281951/10000000000 : ℝ)|^4385 ≤ (39001349564363/100000000000000 : ℝ)^3361
        have hw : |(4859281951/10000000000 : ℝ)|=(4859281951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5931839811/10000000000 : ℝ)|^4385 ≤ (25296285777811/50000000000000 : ℝ)^3361
        have hw : |(5931839811/10000000000 : ℝ)|=(5931839811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s0_5 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5183728327/10000000000 : ℝ)*x 0 + (-81182943/625000000 : ℝ)*x 1 + (5931839889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183728327/10000000000 : ℝ)^4385 ≤ (10608205876897/25000000000000 : ℝ)^3361 := by
    have hnat : (5183728327 : ℕ)^4385*25000000000000^3361 ≤ 10608205876897^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183728327 10000000000 10608205876897 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81182943/625000000 : ℝ)^4385 ≤ (871825505999/12500000000000 : ℝ)^3361 := by
    have hnat : (81182943 : ℕ)^4385*12500000000000^3361 ≤ 871825505999^3361*625000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81182943 625000000 871825505999 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5931839889/10000000000 : ℝ)^4385 ≤ (50592572423569/100000000000000 : ℝ)^3361 := by
    have hnat : (5931839889 : ℕ)^4385*100000000000000^3361 ≤ 50592572423569^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5931839889 10000000000 50592572423569 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183728327/10000000000 : ℝ), (-81182943/625000000 : ℝ), (5931839889/10000000000 : ℝ)] ![(10608205876897/25000000000000 : ℝ), (871825505999/12500000000000 : ℝ), (50592572423569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183728327/10000000000 : ℝ)|^4385 ≤ (10608205876897/25000000000000 : ℝ)^3361
        have hw : |(5183728327/10000000000 : ℝ)|=(5183728327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81182943/625000000 : ℝ)|^4385 ≤ (871825505999/12500000000000 : ℝ)^3361
        have hw : |(-81182943/625000000 : ℝ)|=(81182943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5931839889/10000000000 : ℝ)|^4385 ≤ (50592572423569/100000000000000 : ℝ)^3361
        have hw : |(5931839889/10000000000 : ℝ)|=(5931839889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s0_6 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2591864173/5000000000 : ℝ)*x 0 + (5931839723/10000000000 : ℝ)*x 1 + (-1298927323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591864173/5000000000 : ℝ)^4385 ≤ (42432823710503/100000000000000 : ℝ)^3361 := by
    have hnat : (2591864173 : ℕ)^4385*100000000000000^3361 ≤ 42432823710503^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591864173 5000000000 42432823710503 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5931839723/10000000000 : ℝ)^4385 ≤ (126481426441/250000000000 : ℝ)^3361 := by
    have hnat : (5931839723 : ℕ)^4385*250000000000^3361 ≤ 126481426441^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5931839723 10000000000 126481426441 250000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298927323/10000000000 : ℝ)^4385 ≤ (6974605694273/100000000000000 : ℝ)^3361 := by
    have hnat : (1298927323 : ℕ)^4385*100000000000000^3361 ≤ 6974605694273^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298927323 10000000000 6974605694273 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591864173/5000000000 : ℝ), (5931839723/10000000000 : ℝ), (-1298927323/10000000000 : ℝ)] ![(42432823710503/100000000000000 : ℝ), (126481426441/250000000000 : ℝ), (6974605694273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591864173/5000000000 : ℝ)|^4385 ≤ (42432823710503/100000000000000 : ℝ)^3361
        have hw : |(2591864173/5000000000 : ℝ)|=(2591864173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5931839723/10000000000 : ℝ)|^4385 ≤ (126481426441/250000000000 : ℝ)^3361
        have hw : |(5931839723/10000000000 : ℝ)|=(5931839723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1298927323/10000000000 : ℝ)|^4385 ≤ (6974605694273/100000000000000 : ℝ)^3361
        have hw : |(-1298927323/10000000000 : ℝ)|=(1298927323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s0_7 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65239009/156250000 : ℝ)*x 0 + (1097030079/2000000000 : ℝ)*x 1 + (633649837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65239009/156250000 : ℝ)^4385 ≤ (15998957185819/50000000000000 : ℝ)^3361 := by
    have hnat : (65239009 : ℕ)^4385*50000000000000^3361 ≤ 15998957185819^3361*156250000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65239009 156250000 15998957185819 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097030079/2000000000 : ℝ)^4385 ≤ (9136014652081/20000000000000 : ℝ)^3361 := by
    have hnat : (1097030079 : ℕ)^4385*20000000000000^3361 ≤ 9136014652081^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097030079 2000000000 9136014652081 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633649837/2000000000 : ℝ)^4385 ≤ (22322012359153/100000000000000 : ℝ)^3361 := by
    have hnat : (633649837 : ℕ)^4385*100000000000000^3361 ≤ 22322012359153^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633649837 2000000000 22322012359153 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65239009/156250000 : ℝ), (1097030079/2000000000 : ℝ), (633649837/2000000000 : ℝ)] ![(15998957185819/50000000000000 : ℝ), (9136014652081/20000000000000 : ℝ), (22322012359153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65239009/156250000 : ℝ)|^4385 ≤ (15998957185819/50000000000000 : ℝ)^3361
        have hw : |(65239009/156250000 : ℝ)|=(65239009/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097030079/2000000000 : ℝ)|^4385 ≤ (9136014652081/20000000000000 : ℝ)^3361
        have hw : |(1097030079/2000000000 : ℝ)|=(1097030079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(633649837/2000000000 : ℝ)|^4385 ≤ (22322012359153/100000000000000 : ℝ)^3361
        have hw : |(633649837/2000000000 : ℝ)|=(633649837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1425_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2019/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13143/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (137/32 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^137 ≤ (0 : ℝ)^32 := by
      have hnat : (0 : ℕ)^137*1^32 ≤ 0^32*1^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (137/32 : ℝ) ≤ (395684769130815417/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^137 ≤ (395684769130815417/20000000000000000000 : ℝ)^32 := by
      have hnat : (2 : ℕ)^137*20000000000000000000^32 ≤ 395684769130815417^32*5^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 395684769130815417 20000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (395684769130815417/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (1 : ℝ)^32 ≤ (1 : ℝ)^137 := by
      have hnat : (1 : ℕ)^32*1^137 ≤ 1^137*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (20395684769130815417/20000000000000000000 : ℝ) ≤ (2009173006478447/2000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (20395684769130815417/20000000000000000000 : ℝ)^32 ≤ (2009173006478447/2000000000000000 : ℝ)^137 := by
      have hnat : (20395684769130815417 : ℕ)^32*2000000000000000^137 ≤ 2009173006478447^137*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20395684769130815417 20000000000000000000 2009173006478447 2000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2009173006478447/2000000000000000 : ℝ)) (X := (20395684769130815417/20000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (10395684769130815417/10000000000000000000 : ℝ) ≤ (1009173006478447/1000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (10395684769130815417/10000000000000000000 : ℝ)^32 ≤ (1009173006478447/1000000000000000 : ℝ)^137 := by
      have hnat : (10395684769130815417 : ℕ)^32*1000000000000000^137 ≤ 1009173006478447^137*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10395684769130815417 10000000000000000000 1009173006478447 1000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1009173006478447/1000000000000000 : ℝ)) (X := (10395684769130815417/10000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9173006478447/800000000000000 : ℝ)*(0 : ℝ))^(137/32 : ℝ) := by
    rw [show (1 : ℝ)+2*(9173006478447/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(395684769130815417/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9173006478447/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(137/32 : ℝ) := by
    rw [show (1 : ℝ)+(9173006478447/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2009173006478447/2000000000000000 : ℝ) by norm_num, show 1+(395684769130815417/20000000000000000000 : ℝ)+(0 : ℝ)=(20395684769130815417/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(395684769130815417/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9173006478447/800000000000000 : ℝ)*(2/5 : ℝ))^(137/32 : ℝ) := by
    rw [show (1 : ℝ)+2*(9173006478447/800000000000000 : ℝ)*(2/5 : ℝ)=(1009173006478447/1000000000000000 : ℝ) by norm_num, show 1+2*(395684769130815417/20000000000000000000 : ℝ)=(10395684769130815417/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9173006478447/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9173006478447/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9173006478447/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9173006478447/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9173006478447/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9173006478447/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1761080639/10000000000 : ℝ)*X 0 0+(5961833427/10000000000 : ℝ)*X 0 1+(1207580581/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2746272089/5000000000 : ℝ)*X 1 0+(-1200222387/5000000000 : ℝ)*X 1 1+(2415161371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1373136149/2500000000 : ℝ)*X 2 0+(4830322569/10000000000 : ℝ)*X 2 1+(-2400444451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4166574909/10000000000 : ℝ)*X 0 0+(1551728801/5000000000 : ℝ)*X 0 1+(5547708153/10000000000 : ℝ)*X 0 2+(4166574909/10000000000 : ℝ)*X 1 0+(1551728801/5000000000 : ℝ)*X 1 1+(5547708153/10000000000 : ℝ)*X 1 2+(4166574909/10000000000 : ℝ)*X 2 0+(1551728801/5000000000 : ℝ)*X 2 1+(5547708153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-6894989/39062500 : ℝ)*X 0 0+(4859281951/10000000000 : ℝ)*X 0 1+(5931839811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5183728327/10000000000 : ℝ)*X 1 0+(-81182943/625000000 : ℝ)*X 1 1+(5931839889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2591864173/5000000000 : ℝ)*X 2 0+(5931839723/10000000000 : ℝ)*X 2 1+(-1298927323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((65239009/156250000 : ℝ)*X 0 0+(1097030079/2000000000 : ℝ)*X 0 1+(633649837/2000000000 : ℝ)*X 0 2+(65239009/156250000 : ℝ)*X 1 0+(1097030079/2000000000 : ℝ)*X 1 1+(633649837/2000000000 : ℝ)*X 1 2+(65239009/156250000 : ℝ)*X 2 0+(1097030079/2000000000 : ℝ)*X 2 1+(633649837/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73283213357189283538557/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (873333859/50000000000000 : ℝ)*(base19) + (893887689/50000000000000 : ℝ)*(base23) + (189518499/100000000000000 : ℝ)*(upper3) + (14363637/100000000000000 : ℝ)*(upper4) + (2184431/800000000000 : ℝ)*(upper5) + (646458068515377/100000000000000 : ℝ)*(major0) + (646458068515377/100000000000000 : ℝ)*(major1) + (646458068515377/100000000000000 : ℝ)*(major2) + (55236230574533/6250000000000 : ℝ)*(sp0) + (55236547181009/6250000000000 : ℝ)*(sp1) + (220946178447121/25000000000000 : ℝ)*(sp2) + (102281597525629/25000000000000 : ℝ)*(sp3) + (3406185667/50000000000000 : ℝ)*(sp4) + (187567937/6250000000000 : ℝ)*(sp7) + (409129391189507/100000000000000 : ℝ)*(f.failure) + (441893250781931/50000000000000 : ℝ)*(f.sum) + (6122575059519/40000000000000000000000000000 : ℝ)*base65 + (537996926380481/80000000000000000000000000000 : ℝ)*base68 + (984650754540481/80000000000000000000000000000 : ℝ)*base70 + (416256566860481/80000000000000000000000000000 : ℝ)*base72 + (138585242060481/40000000000000000000000000000 : ℝ)*base74 + (532053466700481/80000000000000000000000000000 : ℝ)*base76 + (557007193420481/80000000000000000000000000000 : ℝ)*base78 + (447794470860481/80000000000000000000000000000 : ℝ)*base80 + (249444248780481/40000000000000000000000000000 : ℝ)*base82 + (812623/500000000000000000000 : ℝ)*base90 + (812623/500000000000000000000 : ℝ)*base92 + (812623/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (332469356172207596160237/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118500689/6250000000000 : ℝ)*(base19) + (1911028809/100000000000000 : ℝ)*(base23) + (7442507/4000000000000 : ℝ)*(base32) + (287018477/100000000000000 : ℝ)*(upper3) + (41661487/25000000000000 : ℝ)*(upper5) + (681980389195381/100000000000000 : ℝ)*(major0) + (681980389195381/100000000000000 : ℝ)*(major1) + (681980389195381/100000000000000 : ℝ)*(major2) + (4462767509/100000000000000 : ℝ)*(sp1) + (1164371089/25000000000000 : ℝ)*(sp2) + (233087449574443/25000000000000 : ℝ)*(sp4) + (466171719759619/50000000000000 : ℝ)*(sp5) + (932343229784607/100000000000000 : ℝ)*(sp6) + (431610516972509/100000000000000 : ℝ)*(sp7) + (26975668939699/6250000000000 : ℝ)*(f.failure) + (233087449574443/25000000000000 : ℝ)*(f.sum) + (20046043013307/40000000000000000000000000000 : ℝ)*base65 + (800466310293307/80000000000000000000000000000 : ℝ)*base67 + (346753852106693/80000000000000000000000000000 : ℝ)*base70 + (530642919493307/80000000000000000000000000000 : ℝ)*base71 + (258189682653307/40000000000000000000000000000 : ℝ)*base73 + (297208294453307/80000000000000000000000000000 : ℝ)*base75 + (156631497893307/80000000000000000000000000000 : ℝ)*base77 + (473693410053307/80000000000000000000000000000 : ℝ)*base79 + (119246533466693/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (246211/31250000000000000000 : ℝ)*base90 + (246211/31250000000000000000 : ℝ)*base92 + (246211/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1425_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2019/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13143/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1425_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1425_s1_0 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-967001049/5000000000 : ℝ)*x 0 + (140171019/250000000 : ℝ)*x 1 + (5074465351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (967001049/5000000000 : ℝ)^4385 ≤ (2344719503339/20000000000000 : ℝ)^3361 := by
    have hnat : (967001049 : ℕ)^4385*20000000000000^3361 ≤ 2344719503339^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967001049 5000000000 2344719503339 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140171019/250000000 : ℝ)^4385 ≤ (47006714088147/100000000000000 : ℝ)^3361 := by
    have hnat : (140171019 : ℕ)^4385*100000000000000^3361 ≤ 47006714088147^3361*250000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140171019 250000000 47006714088147 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5074465351/10000000000 : ℝ)^4385 ≤ (2579355523223/6250000000000 : ℝ)^3361 := by
    have hnat : (5074465351 : ℕ)^4385*6250000000000^3361 ≤ 2579355523223^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074465351 10000000000 2579355523223 6250000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-967001049/5000000000 : ℝ), (140171019/250000000 : ℝ), (5074465351/10000000000 : ℝ)] ![(2344719503339/20000000000000 : ℝ), (47006714088147/100000000000000 : ℝ), (2579355523223/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-967001049/5000000000 : ℝ)|^4385 ≤ (2344719503339/20000000000000 : ℝ)^3361
        have hw : |(-967001049/5000000000 : ℝ)|=(967001049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140171019/250000000 : ℝ)|^4385 ≤ (47006714088147/100000000000000 : ℝ)^3361
        have hw : |(140171019/250000000 : ℝ)|=(140171019/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5074465351/10000000000 : ℝ)|^4385 ≤ (2579355523223/6250000000000 : ℝ)^3361
        have hw : |(5074465351/10000000000 : ℝ)|=(5074465351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s1_1 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107944267/200000000 : ℝ)*x 0 + (-2216187571/10000000000 : ℝ)*x 1 + (1268616641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107944267/200000000 : ℝ)^4385 ≤ (22363479149329/50000000000000 : ℝ)^3361 := by
    have hnat : (107944267 : ℕ)^4385*50000000000000^3361 ≤ 22363479149329^3361*200000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107944267 200000000 22363479149329 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216187571/10000000000 : ℝ)^4385 ≤ (43760438921/312500000000 : ℝ)^3361 := by
    have hnat : (2216187571 : ℕ)^4385*312500000000^3361 ≤ 43760438921^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216187571 10000000000 43760438921 312500000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1268616641/2500000000 : ℝ)^4385 ≤ (41269701242287/100000000000000 : ℝ)^3361 := by
    have hnat : (1268616641 : ℕ)^4385*100000000000000^3361 ≤ 41269701242287^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268616641 2500000000 41269701242287 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107944267/200000000 : ℝ), (-2216187571/10000000000 : ℝ), (1268616641/2500000000 : ℝ)] ![(22363479149329/50000000000000 : ℝ), (43760438921/312500000000 : ℝ), (41269701242287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107944267/200000000 : ℝ)|^4385 ≤ (22363479149329/50000000000000 : ℝ)^3361
        have hw : |(107944267/200000000 : ℝ)|=(107944267/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216187571/10000000000 : ℝ)|^4385 ≤ (43760438921/312500000000 : ℝ)^3361
        have hw : |(-2216187571/10000000000 : ℝ)|=(2216187571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1268616641/2500000000 : ℝ)|^4385 ≤ (41269701242287/100000000000000 : ℝ)^3361
        have hw : |(1268616641/2500000000 : ℝ)|=(1268616641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s1_2 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079442861/2000000000 : ℝ)*x 0 + (1014893099/2000000000 : ℝ)*x 1 + (-2216187693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079442861/2000000000 : ℝ)^4385 ≤ (11181742155999/25000000000000 : ℝ)^3361 := by
    have hnat : (1079442861 : ℕ)^4385*25000000000000^3361 ≤ 11181742155999^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079442861 2000000000 11181742155999 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014893099/2000000000 : ℝ)^4385 ≤ (20634844949751/50000000000000 : ℝ)^3361 := by
    have hnat : (1014893099 : ℕ)^4385*50000000000000^3361 ≤ 20634844949751^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014893099 2000000000 20634844949751 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216187693/10000000000 : ℝ)^4385 ≤ (700167073023/5000000000000 : ℝ)^3361 := by
    have hnat : (2216187693 : ℕ)^4385*5000000000000^3361 ≤ 700167073023^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216187693 10000000000 700167073023 5000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079442861/2000000000 : ℝ), (1014893099/2000000000 : ℝ), (-2216187693/10000000000 : ℝ)] ![(11181742155999/25000000000000 : ℝ), (20634844949751/50000000000000 : ℝ), (700167073023/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079442861/2000000000 : ℝ)|^4385 ≤ (11181742155999/25000000000000 : ℝ)^3361
        have hw : |(1079442861/2000000000 : ℝ)|=(1079442861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014893099/2000000000 : ℝ)|^4385 ≤ (20634844949751/50000000000000 : ℝ)^3361
        have hw : |(1014893099/2000000000 : ℝ)|=(1014893099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2216187693/10000000000 : ℝ)|^4385 ≤ (700167073023/5000000000000 : ℝ)^3361
        have hw : |(-2216187693/10000000000 : ℝ)|=(2216187693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s1_3 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34218909/80000000 : ℝ)*x 0 + (3736915823/10000000000 : ℝ)*x 1 + (4886931967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34218909/80000000 : ℝ)^4385 ≤ (1031944129027/3125000000000 : ℝ)^3361 := by
    have hnat : (34218909 : ℕ)^4385*3125000000000^3361 ≤ 1031944129027^3361*80000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34218909 80000000 1031944129027 3125000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3736915823/10000000000 : ℝ)^4385 ≤ (13843325348603/50000000000000 : ℝ)^3361 := by
    have hnat : (3736915823 : ℕ)^4385*50000000000000^3361 ≤ 13843325348603^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736915823 10000000000 13843325348603 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4886931967/10000000000 : ℝ)^4385 ≤ (9822784291747/25000000000000 : ℝ)^3361 := by
    have hnat : (4886931967 : ℕ)^4385*25000000000000^3361 ≤ 9822784291747^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886931967 10000000000 9822784291747 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34218909/80000000 : ℝ), (3736915823/10000000000 : ℝ), (4886931967/10000000000 : ℝ)] ![(1031944129027/3125000000000 : ℝ), (13843325348603/50000000000000 : ℝ), (9822784291747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34218909/80000000 : ℝ)|^4385 ≤ (1031944129027/3125000000000 : ℝ)^3361
        have hw : |(34218909/80000000 : ℝ)|=(34218909/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3736915823/10000000000 : ℝ)|^4385 ≤ (13843325348603/50000000000000 : ℝ)^3361
        have hw : |(3736915823/10000000000 : ℝ)|=(3736915823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4886931967/10000000000 : ℝ)|^4385 ≤ (9822784291747/25000000000000 : ℝ)^3361
        have hw : |(4886931967/10000000000 : ℝ)|=(4886931967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s1_4 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1934405629/10000000000 : ℝ)*x 0 + (5080727937/10000000000 : ℝ)*x 1 + (1120094329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1934405629/10000000000 : ℝ)^4385 ≤ (366462156979/3125000000000 : ℝ)^3361 := by
    have hnat : (1934405629 : ℕ)^4385*3125000000000^3361 ≤ 366462156979^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934405629 10000000000 366462156979 3125000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080727937/10000000000 : ℝ)^4385 ≤ (826723019361/2000000000000 : ℝ)^3361 := by
    have hnat : (5080727937 : ℕ)^4385*2000000000000^3361 ≤ 826723019361^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080727937 10000000000 826723019361 2000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120094329/2000000000 : ℝ)^4385 ≤ (46937059990841/100000000000000 : ℝ)^3361 := by
    have hnat : (1120094329 : ℕ)^4385*100000000000000^3361 ≤ 46937059990841^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120094329 2000000000 46937059990841 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1934405629/10000000000 : ℝ), (5080727937/10000000000 : ℝ), (1120094329/2000000000 : ℝ)] ![(366462156979/3125000000000 : ℝ), (826723019361/2000000000000 : ℝ), (46937059990841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1934405629/10000000000 : ℝ)|^4385 ≤ (366462156979/3125000000000 : ℝ)^3361
        have hw : |(-1934405629/10000000000 : ℝ)|=(1934405629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080727937/10000000000 : ℝ)|^4385 ≤ (826723019361/2000000000000 : ℝ)^3361
        have hw : |(5080727937/10000000000 : ℝ)|=(5080727937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120094329/2000000000 : ℝ)|^4385 ≤ (46937059990841/100000000000000 : ℝ)^3361
        have hw : |(1120094329/2000000000 : ℝ)|=(1120094329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s1_5 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314539949/2500000000 : ℝ)*x 0 + (-1690181937/10000000000 : ℝ)*x 1 + (2800235829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314539949/2500000000 : ℝ)^4385 ≤ (2161473270839/5000000000000 : ℝ)^3361 := by
    have hnat : (1314539949 : ℕ)^4385*5000000000000^3361 ≤ 2161473270839^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314539949 2500000000 2161473270839 5000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1690181937/10000000000 : ℝ)^4385 ≤ (4916737221869/50000000000000 : ℝ)^3361 := by
    have hnat : (1690181937 : ℕ)^4385*50000000000000^3361 ≤ 4916737221869^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690181937 10000000000 4916737221869 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2800235829/5000000000 : ℝ)^4385 ≤ (46937060132987/100000000000000 : ℝ)^3361 := by
    have hnat : (2800235829 : ℕ)^4385*100000000000000^3361 ≤ 46937060132987^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800235829 5000000000 46937060132987 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314539949/2500000000 : ℝ), (-1690181937/10000000000 : ℝ), (2800235829/5000000000 : ℝ)] ![(2161473270839/5000000000000 : ℝ), (4916737221869/50000000000000 : ℝ), (46937060132987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314539949/2500000000 : ℝ)|^4385 ≤ (2161473270839/5000000000000 : ℝ)^3361
        have hw : |(1314539949/2500000000 : ℝ)|=(1314539949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1690181937/10000000000 : ℝ)|^4385 ≤ (4916737221869/50000000000000 : ℝ)^3361
        have hw : |(-1690181937/10000000000 : ℝ)|=(1690181937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2800235829/5000000000 : ℝ)|^4385 ≤ (46937060132987/100000000000000 : ℝ)^3361
        have hw : |(2800235829/5000000000 : ℝ)|=(2800235829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s1_6 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314539939/2500000000 : ℝ)*x 0 + (5600471621/10000000000 : ℝ)*x 1 + (-338036409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314539939/2500000000 : ℝ)^4385 ≤ (43229464987731/100000000000000 : ℝ)^3361 := by
    have hnat : (1314539939 : ℕ)^4385*100000000000000^3361 ≤ 43229464987731^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314539939 2500000000 43229464987731 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5600471621/10000000000 : ℝ)^4385 ≤ (46937059728417/100000000000000 : ℝ)^3361 := by
    have hnat : (5600471621 : ℕ)^4385*100000000000000^3361 ≤ 46937059728417^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5600471621 10000000000 46937059728417 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338036409/2000000000 : ℝ)^4385 ≤ (61459220397/625000000000 : ℝ)^3361 := by
    have hnat : (338036409 : ℕ)^4385*625000000000^3361 ≤ 61459220397^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338036409 2000000000 61459220397 625000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314539939/2500000000 : ℝ), (5600471621/10000000000 : ℝ), (-338036409/2000000000 : ℝ)] ![(43229464987731/100000000000000 : ℝ), (46937059728417/100000000000000 : ℝ), (61459220397/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314539939/2500000000 : ℝ)|^4385 ≤ (43229464987731/100000000000000 : ℝ)^3361
        have hw : |(1314539939/2500000000 : ℝ)|=(1314539939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5600471621/10000000000 : ℝ)|^4385 ≤ (46937059728417/100000000000000 : ℝ)^3361
        have hw : |(5600471621/10000000000 : ℝ)|=(5600471621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-338036409/2000000000 : ℝ)|^4385 ≤ (61459220397/625000000000 : ℝ)^3361
        have hw : |(-338036409/2000000000 : ℝ)|=(338036409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s1_7 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278235661/10000000000 : ℝ)*x 0 + (19493619/40000000 : ℝ)*x 1 + (1875336333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278235661/10000000000 : ℝ)^4385 ≤ (1651549792943/5000000000000 : ℝ)^3361 := by
    have hnat : (4278235661 : ℕ)^4385*5000000000000^3361 ≤ 1651549792943^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278235661 10000000000 1651549792943 5000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19493619/40000000 : ℝ)^4385 ≤ (39149301791803/100000000000000 : ℝ)^3361 := by
    have hnat : (19493619 : ℕ)^4385*100000000000000^3361 ≤ 39149301791803^3361*40000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19493619 40000000 39149301791803 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875336333/5000000000 : ℝ)^4385 ≤ (27819702342299/100000000000000 : ℝ)^3361 := by
    have hnat : (1875336333 : ℕ)^4385*100000000000000^3361 ≤ 27819702342299^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875336333 5000000000 27819702342299 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278235661/10000000000 : ℝ), (19493619/40000000 : ℝ), (1875336333/5000000000 : ℝ)] ![(1651549792943/5000000000000 : ℝ), (39149301791803/100000000000000 : ℝ), (27819702342299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278235661/10000000000 : ℝ)|^4385 ≤ (1651549792943/5000000000000 : ℝ)^3361
        have hw : |(4278235661/10000000000 : ℝ)|=(4278235661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19493619/40000000 : ℝ)|^4385 ≤ (39149301791803/100000000000000 : ℝ)^3361
        have hw : |(19493619/40000000 : ℝ)|=(19493619/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1875336333/5000000000 : ℝ)|^4385 ≤ (27819702342299/100000000000000 : ℝ)^3361
        have hw : |(1875336333/5000000000 : ℝ)|=(1875336333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1425_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13143/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2019/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3809/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18873/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13143/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2019/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13143/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2019/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13143/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2019/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13143/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2019/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13143/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2019/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13143/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2019/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2019/100000 : ℝ) ^ (137/32 : ℝ) ≤ (5544531631681/100000000000000000000 : ℝ) := by
    have hpowers : (2019/100000 : ℝ)^137 ≤ (5544531631681/100000000000000000000 : ℝ)^32 := by
      have hnat : (2019 : ℕ)^137*100000000000000000000^32 ≤ 5544531631681^32*100000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2019 100000 5544531631681 100000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2019/100000 : ℝ)) (X := (5544531631681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hpowhi : (13143/50000 : ℝ) ^ (137/32 : ℝ) ≤ (40983169655586351/12500000000000000000 : ℝ) := by
    have hpowers : (13143/50000 : ℝ)^137 ≤ (40983169655586351/12500000000000000000 : ℝ)^32 := by
      have hnat : (13143 : ℕ)^137*12500000000000000000^32 ≤ 40983169655586351^32*50000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13143 50000 40983169655586351 12500000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13143/50000 : ℝ)) (X := (40983169655586351/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000005544531631681/50000000000000000000 : ℝ) ≤ (5000000129507303/5000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (50000005544531631681/50000000000000000000 : ℝ)^32 ≤ (5000000129507303/5000000000000000 : ℝ)^137 := by
      have hnat : (50000005544531631681 : ℕ)^32*5000000000000000^137 ≤ 5000000129507303^137*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000005544531631681 50000000000000000000 5000000129507303 5000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000129507303/5000000000000000 : ℝ)) (X := (50000005544531631681/50000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100327870901776322489/100000000000000000000 : ℝ) ≤ (2501912173695057/2500000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (100327870901776322489/100000000000000000000 : ℝ)^32 ≤ (2501912173695057/2500000000000000 : ℝ)^137 := by
      have hnat : (100327870901776322489 : ℕ)^32*2500000000000000^137 ≤ 2501912173695057^137*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100327870901776322489 100000000000000000000 2501912173695057 2500000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501912173695057/2500000000000000 : ℝ)) (X := (100327870901776322489/100000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (6290983169655586351/6250000000000000000 : ℝ) ≤ (200305942610917/200000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (6290983169655586351/6250000000000000000 : ℝ)^32 ≤ (200305942610917/200000000000000 : ℝ)^137 := by
      have hnat : (6290983169655586351 : ℕ)^32*200000000000000^137 ≤ 200305942610917^137*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6290983169655586351 6250000000000000000 200305942610917 200000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200305942610917/200000000000000 : ℝ)) (X := (6290983169655586351/6250000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5544531631681/100000000000000000000 : ℝ) ≤ ((40439853650314310361/40445000000000000000 : ℝ)+2*(3824217882811/1213350000000000 : ℝ)*(2019/100000 : ℝ))^(137/32 : ℝ) := by
    rw [show (40439853650314310361/40445000000000000000 : ℝ)+2*(3824217882811/1213350000000000 : ℝ)*(2019/100000 : ℝ)=(5000000129507303/5000000000000000 : ℝ) by norm_num, show 1+2*(5544531631681/100000000000000000000 : ℝ)=(50000005544531631681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40983169655586351/12500000000000000000 : ℝ)+(5544531631681/100000000000000000000 : ℝ) ≤ ((40439853650314310361/40445000000000000000 : ℝ)+(3824217882811/1213350000000000 : ℝ)*((13143/50000 : ℝ)+(2019/100000 : ℝ)))^(137/32 : ℝ) := by
    rw [show (40439853650314310361/40445000000000000000 : ℝ)+(3824217882811/1213350000000000 : ℝ)*((13143/50000 : ℝ)+(2019/100000 : ℝ))=(2501912173695057/2500000000000000 : ℝ) by norm_num, show 1+(40983169655586351/12500000000000000000 : ℝ)+(5544531631681/100000000000000000000 : ℝ)=(100327870901776322489/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40983169655586351/12500000000000000000 : ℝ) ≤ ((40439853650314310361/40445000000000000000 : ℝ)+2*(3824217882811/1213350000000000 : ℝ)*(13143/50000 : ℝ))^(137/32 : ℝ) := by
    rw [show (40439853650314310361/40445000000000000000 : ℝ)+2*(3824217882811/1213350000000000 : ℝ)*(13143/50000 : ℝ)=(200305942610917/200000000000000 : ℝ) by norm_num, show 1+2*(40983169655586351/12500000000000000000 : ℝ)=(6290983169655586351/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40439853650314310361/40445000000000000000 : ℝ)*(X 1 0+X 2 0)+(3824217882811/1213350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (2019/100000 : ℝ)) (hi := (13143/50000 : ℝ)) (c := (40439853650314310361/40445000000000000000 : ℝ)) (alpha := (3824217882811/1213350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40439853650314310361/40445000000000000000 : ℝ)*(X 0 1+X 2 1)+(3824217882811/1213350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (2019/100000 : ℝ)) (hi := (13143/50000 : ℝ)) (c := (40439853650314310361/40445000000000000000 : ℝ)) (alpha := (3824217882811/1213350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40439853650314310361/40445000000000000000 : ℝ)*(X 0 2+X 1 2)+(3824217882811/1213350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (2019/100000 : ℝ)) (hi := (13143/50000 : ℝ)) (c := (40439853650314310361/40445000000000000000 : ℝ)) (alpha := (3824217882811/1213350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-967001049/5000000000 : ℝ)*X 0 0+(140171019/250000000 : ℝ)*X 0 1+(5074465351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107944267/200000000 : ℝ)*X 1 0+(-2216187571/10000000000 : ℝ)*X 1 1+(1268616641/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1079442861/2000000000 : ℝ)*X 2 0+(1014893099/2000000000 : ℝ)*X 2 1+(-2216187693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34218909/80000000 : ℝ)*X 0 0+(3736915823/10000000000 : ℝ)*X 0 1+(4886931967/10000000000 : ℝ)*X 0 2+(34218909/80000000 : ℝ)*X 1 0+(3736915823/10000000000 : ℝ)*X 1 1+(4886931967/10000000000 : ℝ)*X 1 2+(34218909/80000000 : ℝ)*X 2 0+(3736915823/10000000000 : ℝ)*X 2 1+(4886931967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1934405629/10000000000 : ℝ)*X 0 0+(5080727937/10000000000 : ℝ)*X 0 1+(1120094329/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314539949/2500000000 : ℝ)*X 1 0+(-1690181937/10000000000 : ℝ)*X 1 1+(2800235829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314539939/2500000000 : ℝ)*X 2 0+(5600471621/10000000000 : ℝ)*X 2 1+(-338036409/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278235661/10000000000 : ℝ)*X 0 0+(19493619/40000000 : ℝ)*X 0 1+(1875336333/5000000000 : ℝ)*X 0 2+(4278235661/10000000000 : ℝ)*X 1 0+(19493619/40000000 : ℝ)*X 1 1+(1875336333/5000000000 : ℝ)*X 1 2+(4278235661/10000000000 : ℝ)*X 2 0+(19493619/40000000 : ℝ)*X 2 1+(1875336333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4873707815185843416635336031/505562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39373783/100000000000000 : ℝ)*(base1) + (1672502339/100000000000000 : ℝ)*(base19) + (501218199/25000000000000 : ℝ)*(base23) + (46943469/25000000000000 : ℝ)*(upper3) + (103147041/50000000000000 : ℝ)*(upper5) + (686992582644657/50000000000000 : ℝ)*(major0) + (686992582644657/50000000000000 : ℝ)*(major1) + (686992582644657/50000000000000 : ℝ)*(major2) + (187838838052991/10000000000000 : ℝ)*(sp0) + (1878402712056969/100000000000000 : ℝ)*(sp1) + (117400148730407/6250000000000 : ℝ)*(sp2) + (17391181611673/2000000000000 : ℝ)*(sp3) + (16043403181/100000000000000 : ℝ)*(sp4) + (260188917/4000000000000 : ℝ)*(sp7) + (434782812340179/50000000000000 : ℝ)*(f.failure) + (469601096139827/25000000000000 : ℝ)*(f.sum) + (66714277268483/20222500000000000000000000000 : ℝ)*base65 + (13458997486620958823/2022250000000000000000000000000000 : ℝ)*base68 + (3917965076461458823/2022250000000000000000000000000000 : ℝ)*base70 + (5747506058731041177/2022250000000000000000000000000000 : ℝ)*base71 + (123112169639009/40445000000000000000000000000 : ℝ)*base74 + (10078210490743708823/2022250000000000000000000000000000 : ℝ)*base76 + (4231525211991458823/2022250000000000000000000000000000 : ℝ)*base78 + (9439581967027708823/2022250000000000000000000000000000 : ℝ)*base80 + (25199299848889/10111250000000000000000000000 : ℝ)*base81 + (913569/250000000000000000000 : ℝ)*base89 + (913569/250000000000000000000 : ℝ)*base91 + (913569/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9630618074504977178420695943/2022250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18275241/50000000000000 : ℝ)*(base1) + (1023745817/100000000000000 : ℝ)*(base19) + (100210509/10000000000000 : ℝ)*(base23) + (29422541/25000000000000 : ℝ)*(upper3) + (99769719/100000000000000 : ℝ)*(upper5) + (1407354795106807/100000000000000 : ℝ)*(major0) + (1407354795106807/100000000000000 : ℝ)*(major1) + (1407354795106807/100000000000000 : ℝ)*(major2) + (23934441/400000000000 : ℝ)*(sp1) + (2859355701/50000000000000 : ℝ)*(sp2) + (1924024923186133/100000000000000 : ℝ)*(sp4) + (60125558727487/3125000000000 : ℝ)*(sp5) + (962009082909579/50000000000000 : ℝ)*(sp6) + (445342254141601/50000000000000 : ℝ)*(sp7) + (178136908966737/20000000000000 : ℝ)*(f.failure) + (38480497732713/2000000000000 : ℝ)*(f.sum) + (54596176370821/121335000000000000000000000000 : ℝ)*base66 + (98719739958580618019/12133500000000000000000000000000000 : ℝ)*base68 + (14063681894746618019/12133500000000000000000000000000000 : ℝ)*base70 + (54398512574208118019/12133500000000000000000000000000000 : ℝ)*base72 + (2724410850673/15166875000000000000000000000 : ℝ)*base73 + (139754759905761118019/12133500000000000000000000000000000 : ℝ)*base76 + (101490672922857118019/12133500000000000000000000000000000 : ℝ)*base78 + (61410337516095118019/12133500000000000000000000000000000 : ℝ)*base80 + (128323818541447/60667500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (628907/100000000000000000000 : ℝ)*base89 + (628907/100000000000000000000 : ℝ)*base91 + (628907/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1425_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13143/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2019/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3809/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18873/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1425_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1425_s2_0 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98371773/500000000 : ℝ)*x 0 + (5459076929/10000000000 : ℝ)*x 1 + (5200713417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98371773/500000000 : ℝ)^4385 ≤ (11988705463449/100000000000000 : ℝ)^3361 := by
    have hnat : (98371773 : ℕ)^4385*100000000000000^3361 ≤ 11988705463449^3361*500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98371773 500000000 11988705463449 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459076929/10000000000 : ℝ)^4385 ≤ (283731150951/625000000000 : ℝ)^3361 := by
    have hnat : (5459076929 : ℕ)^4385*625000000000^3361 ≤ 283731150951^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459076929 10000000000 283731150951 625000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5200713417/10000000000 : ℝ)^4385 ≤ (85228620741/200000000000 : ℝ)^3361 := by
    have hnat : (5200713417 : ℕ)^4385*200000000000^3361 ≤ 85228620741^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200713417 10000000000 85228620741 200000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98371773/500000000 : ℝ), (5459076929/10000000000 : ℝ), (5200713417/10000000000 : ℝ)] ![(11988705463449/100000000000000 : ℝ), (283731150951/625000000000 : ℝ), (85228620741/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98371773/500000000 : ℝ)|^4385 ≤ (11988705463449/100000000000000 : ℝ)^3361
        have hw : |(-98371773/500000000 : ℝ)|=(98371773/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459076929/10000000000 : ℝ)|^4385 ≤ (283731150951/625000000000 : ℝ)^3361
        have hw : |(5459076929/10000000000 : ℝ)|=(5459076929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5200713417/10000000000 : ℝ)|^4385 ≤ (85228620741/200000000000 : ℝ)^3361
        have hw : |(5200713417/10000000000 : ℝ)|=(5200713417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s2_1 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360395493/10000000000 : ℝ)*x 0 + (-2100385517/10000000000 : ℝ)*x 1 + (1040142677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360395493/10000000000 : ℝ)^4385 ≤ (44329302692331/100000000000000 : ℝ)^3361 := by
    have hnat : (5360395493 : ℕ)^4385*100000000000000^3361 ≤ 44329302692331^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360395493 10000000000 44329302692331 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100385517/10000000000 : ℝ)^4385 ≤ (3264096815767/25000000000000 : ℝ)^3361 := by
    have hnat : (2100385517 : ℕ)^4385*25000000000000^3361 ≤ 3264096815767^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100385517 10000000000 3264096815767 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040142677/2000000000 : ℝ)^4385 ≤ (5326788753551/12500000000000 : ℝ)^3361 := by
    have hnat : (1040142677 : ℕ)^4385*12500000000000^3361 ≤ 5326788753551^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040142677 2000000000 5326788753551 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360395493/10000000000 : ℝ), (-2100385517/10000000000 : ℝ), (1040142677/2000000000 : ℝ)] ![(44329302692331/100000000000000 : ℝ), (3264096815767/25000000000000 : ℝ), (5326788753551/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360395493/10000000000 : ℝ)|^4385 ≤ (44329302692331/100000000000000 : ℝ)^3361
        have hw : |(5360395493/10000000000 : ℝ)|=(5360395493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100385517/10000000000 : ℝ)|^4385 ≤ (3264096815767/25000000000000 : ℝ)^3361
        have hw : |(-2100385517/10000000000 : ℝ)|=(2100385517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040142677/2000000000 : ℝ)|^4385 ≤ (5326788753551/12500000000000 : ℝ)^3361
        have hw : |(1040142677/2000000000 : ℝ)|=(1040142677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s2_2 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340098909/2500000000 : ℝ)*x 0 + (2600356613/5000000000 : ℝ)*x 1 + (-420077107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340098909/2500000000 : ℝ)^4385 ≤ (5541163029401/12500000000000 : ℝ)^3361 := by
    have hnat : (1340098909 : ℕ)^4385*12500000000000^3361 ≤ 5541163029401^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340098909 2500000000 5541163029401 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2600356613/5000000000 : ℝ)^4385 ≤ (8522861665727/20000000000000 : ℝ)^3361 := by
    have hnat : (2600356613 : ℕ)^4385*20000000000000^3361 ≤ 8522861665727^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600356613 5000000000 8522861665727 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420077107/2000000000 : ℝ)^4385 ≤ (13056387409049/100000000000000 : ℝ)^3361 := by
    have hnat : (420077107 : ℕ)^4385*100000000000000^3361 ≤ 13056387409049^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420077107 2000000000 13056387409049 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340098909/2500000000 : ℝ), (2600356613/5000000000 : ℝ), (-420077107/2000000000 : ℝ)] ![(5541163029401/12500000000000 : ℝ), (8522861665727/20000000000000 : ℝ), (13056387409049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340098909/2500000000 : ℝ)|^4385 ≤ (5541163029401/12500000000000 : ℝ)^3361
        have hw : |(1340098909/2500000000 : ℝ)|=(1340098909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2600356613/5000000000 : ℝ)|^4385 ≤ (8522861665727/20000000000000 : ℝ)^3361
        have hw : |(2600356613/5000000000 : ℝ)|=(2600356613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420077107/2000000000 : ℝ)|^4385 ≤ (13056387409049/100000000000000 : ℝ)^3361
        have hw : |(-420077107/2000000000 : ℝ)|=(420077107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s2_3 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300954657/10000000000 : ℝ)*x 0 + (4030041099/10000000000 : ℝ)*x 1 + (917629817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300954657/10000000000 : ℝ)^4385 ≤ (1330401151727/4000000000000 : ℝ)^3361 := by
    have hnat : (4300954657 : ℕ)^4385*4000000000000^3361 ≤ 1330401151727^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300954657 10000000000 1330401151727 4000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030041099/10000000000 : ℝ)^4385 ≤ (30553335428553/100000000000000 : ℝ)^3361 := by
    have hnat : (4030041099 : ℕ)^4385*100000000000000^3361 ≤ 30553335428553^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030041099 10000000000 30553335428553 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (917629817/2000000000 : ℝ)^4385 ≤ (36186635760329/100000000000000 : ℝ)^3361 := by
    have hnat : (917629817 : ℕ)^4385*100000000000000^3361 ≤ 36186635760329^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917629817 2000000000 36186635760329 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300954657/10000000000 : ℝ), (4030041099/10000000000 : ℝ), (917629817/2000000000 : ℝ)] ![(1330401151727/4000000000000 : ℝ), (30553335428553/100000000000000 : ℝ), (36186635760329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300954657/10000000000 : ℝ)|^4385 ≤ (1330401151727/4000000000000 : ℝ)^3361
        have hw : |(4300954657/10000000000 : ℝ)|=(4300954657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030041099/10000000000 : ℝ)|^4385 ≤ (30553335428553/100000000000000 : ℝ)^3361
        have hw : |(4030041099/10000000000 : ℝ)|=(4030041099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(917629817/2000000000 : ℝ)|^4385 ≤ (36186635760329/100000000000000 : ℝ)^3361
        have hw : |(917629817/2000000000 : ℝ)|=(917629817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s2_4 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967481577/10000000000 : ℝ)*x 0 + (2601098729/5000000000 : ℝ)*x 1 + (545758073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967481577/10000000000 : ℝ)^4385 ≤ (2997268024941/25000000000000 : ℝ)^3361 := by
    have hnat : (1967481577 : ℕ)^4385*25000000000000^3361 ≤ 2997268024941^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967481577 10000000000 2997268024941 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601098729/5000000000 : ℝ)^4385 ≤ (5328772005001/12500000000000 : ℝ)^3361 := by
    have hnat : (2601098729 : ℕ)^4385*12500000000000^3361 ≤ 5328772005001^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601098729 5000000000 5328772005001 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545758073/1000000000 : ℝ)^4385 ≤ (45380751850707/100000000000000 : ℝ)^3361 := by
    have hnat : (545758073 : ℕ)^4385*100000000000000^3361 ≤ 45380751850707^3361*1000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545758073 1000000000 45380751850707 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967481577/10000000000 : ℝ), (2601098729/5000000000 : ℝ), (545758073/1000000000 : ℝ)] ![(2997268024941/25000000000000 : ℝ), (5328772005001/12500000000000 : ℝ), (45380751850707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967481577/10000000000 : ℝ)|^4385 ≤ (2997268024941/25000000000000 : ℝ)^3361
        have hw : |(-1967481577/10000000000 : ℝ)|=(1967481577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601098729/5000000000 : ℝ)|^4385 ≤ (5328772005001/12500000000000 : ℝ)^3361
        have hw : |(2601098729/5000000000 : ℝ)|=(2601098729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545758073/1000000000 : ℝ)|^4385 ≤ (45380751850707/100000000000000 : ℝ)^3361
        have hw : |(545758073/1000000000 : ℝ)|=(545758073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s2_5 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058647519/2000000000 : ℝ)*x 0 + (-921759117/5000000000 : ℝ)*x 1 + (5457581079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058647519/2000000000 : ℝ)^4385 ≤ (1090152494739/2500000000000 : ℝ)^3361 := by
    have hnat : (1058647519 : ℕ)^4385*2500000000000^3361 ≤ 1090152494739^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058647519 2000000000 1090152494739 2500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921759117/5000000000 : ℝ)^4385 ≤ (5506572280759/50000000000000 : ℝ)^3361 := by
    have hnat : (921759117 : ℕ)^4385*50000000000000^3361 ≤ 5506572280759^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921759117 5000000000 5506572280759 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457581079/10000000000 : ℝ)^4385 ≤ (45380755636859/100000000000000 : ℝ)^3361 := by
    have hnat : (5457581079 : ℕ)^4385*100000000000000^3361 ≤ 45380755636859^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457581079 10000000000 45380755636859 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058647519/2000000000 : ℝ), (-921759117/5000000000 : ℝ), (5457581079/10000000000 : ℝ)] ![(1090152494739/2500000000000 : ℝ), (5506572280759/50000000000000 : ℝ), (45380755636859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058647519/2000000000 : ℝ)|^4385 ≤ (1090152494739/2500000000000 : ℝ)^3361
        have hw : |(1058647519/2000000000 : ℝ)|=(1058647519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-921759117/5000000000 : ℝ)|^4385 ≤ (5506572280759/50000000000000 : ℝ)^3361
        have hw : |(-921759117/5000000000 : ℝ)|=(921759117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457581079/10000000000 : ℝ)|^4385 ≤ (45380755636859/100000000000000 : ℝ)^3361
        have hw : |(5457581079/10000000000 : ℝ)|=(5457581079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s2_6 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293237533/10000000000 : ℝ)*x 0 + (1091516211/2000000000 : ℝ)*x 1 + (-921759177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293237533/10000000000 : ℝ)^4385 ≤ (8721219824637/20000000000000 : ℝ)^3361 := by
    have hnat : (5293237533 : ℕ)^4385*20000000000000^3361 ≤ 8721219824637^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293237533 10000000000 8721219824637 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091516211/2000000000 : ℝ)^4385 ≤ (22690377688247/50000000000000 : ℝ)^3361 := by
    have hnat : (1091516211 : ℕ)^4385*50000000000000^3361 ≤ 22690377688247^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091516211 2000000000 22690377688247 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921759177/5000000000 : ℝ)^4385 ≤ (1376643187101/12500000000000 : ℝ)^3361 := by
    have hnat : (921759177 : ℕ)^4385*12500000000000^3361 ≤ 1376643187101^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921759177 5000000000 1376643187101 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293237533/10000000000 : ℝ), (1091516211/2000000000 : ℝ), (-921759177/5000000000 : ℝ)] ![(8721219824637/20000000000000 : ℝ), (22690377688247/50000000000000 : ℝ), (1376643187101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293237533/10000000000 : ℝ)|^4385 ≤ (8721219824637/20000000000000 : ℝ)^3361
        have hw : |(5293237533/10000000000 : ℝ)|=(5293237533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091516211/2000000000 : ℝ)|^4385 ≤ (22690377688247/50000000000000 : ℝ)^3361
        have hw : |(1091516211/2000000000 : ℝ)|=(1091516211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-921759177/5000000000 : ℝ)|^4385 ≤ (1376643187101/12500000000000 : ℝ)^3361
        have hw : |(-921759177/5000000000 : ℝ)|=(921759177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s2_7 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301054681/10000000000 : ℝ)*x 0 + (4584943513/10000000000 : ℝ)*x 1 + (4033273101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301054681/10000000000 : ℝ)^4385 ≤ (8315259490949/25000000000000 : ℝ)^3361 := by
    have hnat : (4301054681 : ℕ)^4385*25000000000000^3361 ≤ 8315259490949^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301054681 10000000000 8315259490949 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4584943513/10000000000 : ℝ)^4385 ≤ (36153654209217/100000000000000 : ℝ)^3361 := by
    have hnat : (4584943513 : ℕ)^4385*100000000000000^3361 ≤ 36153654209217^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584943513 10000000000 36153654209217 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033273101/10000000000 : ℝ)^4385 ≤ (3823163475493/12500000000000 : ℝ)^3361 := by
    have hnat : (4033273101 : ℕ)^4385*12500000000000^3361 ≤ 3823163475493^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033273101 10000000000 3823163475493 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301054681/10000000000 : ℝ), (4584943513/10000000000 : ℝ), (4033273101/10000000000 : ℝ)] ![(8315259490949/25000000000000 : ℝ), (36153654209217/100000000000000 : ℝ), (3823163475493/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301054681/10000000000 : ℝ)|^4385 ≤ (8315259490949/25000000000000 : ℝ)^3361
        have hw : |(4301054681/10000000000 : ℝ)|=(4301054681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4584943513/10000000000 : ℝ)|^4385 ≤ (36153654209217/100000000000000 : ℝ)^3361
        have hw : |(4584943513/10000000000 : ℝ)|=(4584943513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033273101/10000000000 : ℝ)|^4385 ≤ (3823163475493/12500000000000 : ℝ)^3361
        have hw : |(4033273101/10000000000 : ℝ)|=(4033273101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1425_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3809/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5173/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3953/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3809/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18873/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3809/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3809/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18873/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3809/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3809/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18873/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3809/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3809/50000 : ℝ) ^ (137/32 : ℝ) ≤ (1632606967609/100000000000000000 : ℝ) := by
    have hpowers : (3809/50000 : ℝ)^137 ≤ (1632606967609/100000000000000000 : ℝ)^32 := by
      have hnat : (3809 : ℕ)^137*100000000000000000^32 ≤ 1632606967609^32*50000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3809 50000 1632606967609 100000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3809/50000 : ℝ)) (X := (1632606967609/100000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hpowhi : (18873/100000 : ℝ) ^ (137/32 : ℝ) ≤ (39688439954923153/50000000000000000000 : ℝ) := by
    have hpowers : (18873/100000 : ℝ)^137 ≤ (39688439954923153/50000000000000000000 : ℝ)^32 := by
      have hnat : (18873 : ℕ)^137*50000000000000000000^32 ≤ 39688439954923153^32*100000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18873 100000 39688439954923153 50000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18873/100000 : ℝ)) (X := (39688439954923153/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001632606967609/50000000000000000 : ℝ) ≤ (5000038133408227/5000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (50001632606967609/50000000000000000 : ℝ)^32 ≤ (5000038133408227/5000000000000000 : ℝ)^137 := by
      have hnat : (50001632606967609 : ℕ)^32*5000000000000000^137 ≤ 5000038133408227^137*50000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001632606967609 50000000000000000 5000038133408227 5000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000038133408227/5000000000000000 : ℝ)) (X := (50001632606967609/50000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (50040504743438727653/50000000000000000000 : ℝ) ≤ (5000945802633089/5000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (50040504743438727653/50000000000000000000 : ℝ)^32 ≤ (5000945802633089/5000000000000000 : ℝ)^137 := by
      have hnat : (50040504743438727653 : ℕ)^32*5000000000000000^137 ≤ 5000945802633089^137*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040504743438727653 50000000000000000000 5000945802633089 5000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000945802633089/5000000000000000 : ℝ)) (X := (50040504743438727653/50000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (25039688439954923153/25000000000000000000 : ℝ) ≤ (5001853471857951/5000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (25039688439954923153/25000000000000000000 : ℝ)^32 ≤ (5001853471857951/5000000000000000 : ℝ)^137 := by
      have hnat : (25039688439954923153 : ℕ)^32*5000000000000000^137 ≤ 5001853471857951^137*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25039688439954923153 25000000000000000000 5001853471857951 5000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001853471857951/5000000000000000 : ℝ)) (X := (25039688439954923153/25000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1632606967609/100000000000000000 : ℝ) ≤ ((56261599943199597453/56275000000000000000 : ℝ)+2*(453834612431/281375000000000 : ℝ)*(3809/50000 : ℝ))^(137/32 : ℝ) := by
    rw [show (56261599943199597453/56275000000000000000 : ℝ)+2*(453834612431/281375000000000 : ℝ)*(3809/50000 : ℝ)=(5000038133408227/5000000000000000 : ℝ) by norm_num, show 1+2*(1632606967609/100000000000000000 : ℝ)=(50001632606967609/50000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39688439954923153/50000000000000000000 : ℝ)+(1632606967609/100000000000000000 : ℝ) ≤ ((56261599943199597453/56275000000000000000 : ℝ)+(453834612431/281375000000000 : ℝ)*((18873/100000 : ℝ)+(3809/50000 : ℝ)))^(137/32 : ℝ) := by
    rw [show (56261599943199597453/56275000000000000000 : ℝ)+(453834612431/281375000000000 : ℝ)*((18873/100000 : ℝ)+(3809/50000 : ℝ))=(5000945802633089/5000000000000000 : ℝ) by norm_num, show 1+(39688439954923153/50000000000000000000 : ℝ)+(1632606967609/100000000000000000 : ℝ)=(50040504743438727653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39688439954923153/50000000000000000000 : ℝ) ≤ ((56261599943199597453/56275000000000000000 : ℝ)+2*(453834612431/281375000000000 : ℝ)*(18873/100000 : ℝ))^(137/32 : ℝ) := by
    rw [show (56261599943199597453/56275000000000000000 : ℝ)+2*(453834612431/281375000000000 : ℝ)*(18873/100000 : ℝ)=(5001853471857951/5000000000000000 : ℝ) by norm_num, show 1+2*(39688439954923153/50000000000000000000 : ℝ)=(25039688439954923153/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56261599943199597453/56275000000000000000 : ℝ)*(X 1 0+X 2 0)+(453834612431/281375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (3809/50000 : ℝ)) (hi := (18873/100000 : ℝ)) (c := (56261599943199597453/56275000000000000000 : ℝ)) (alpha := (453834612431/281375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56261599943199597453/56275000000000000000 : ℝ)*(X 0 1+X 2 1)+(453834612431/281375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (3809/50000 : ℝ)) (hi := (18873/100000 : ℝ)) (c := (56261599943199597453/56275000000000000000 : ℝ)) (alpha := (453834612431/281375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56261599943199597453/56275000000000000000 : ℝ)*(X 0 2+X 1 2)+(453834612431/281375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (3809/50000 : ℝ)) (hi := (18873/100000 : ℝ)) (c := (56261599943199597453/56275000000000000000 : ℝ)) (alpha := (453834612431/281375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-98371773/500000000 : ℝ)*X 0 0+(5459076929/10000000000 : ℝ)*X 0 1+(5200713417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360395493/10000000000 : ℝ)*X 1 0+(-2100385517/10000000000 : ℝ)*X 1 1+(1040142677/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1340098909/2500000000 : ℝ)*X 2 0+(2600356613/5000000000 : ℝ)*X 2 1+(-420077107/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4300954657/10000000000 : ℝ)*X 0 0+(4030041099/10000000000 : ℝ)*X 0 1+(917629817/2000000000 : ℝ)*X 0 2+(4300954657/10000000000 : ℝ)*X 1 0+(4030041099/10000000000 : ℝ)*X 1 1+(917629817/2000000000 : ℝ)*X 1 2+(4300954657/10000000000 : ℝ)*X 2 0+(4030041099/10000000000 : ℝ)*X 2 1+(917629817/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1967481577/10000000000 : ℝ)*X 0 0+(2601098729/5000000000 : ℝ)*X 0 1+(545758073/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058647519/2000000000 : ℝ)*X 1 0+(-921759117/5000000000 : ℝ)*X 1 1+(5457581079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293237533/10000000000 : ℝ)*X 2 0+(1091516211/2000000000 : ℝ)*X 2 1+(-921759177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4301054681/10000000000 : ℝ)*X 0 0+(4584943513/10000000000 : ℝ)*X 0 1+(4033273101/10000000000 : ℝ)*X 0 2+(4301054681/10000000000 : ℝ)*X 1 0+(4584943513/10000000000 : ℝ)*X 1 1+(4033273101/10000000000 : ℝ)*X 1 2+(4301054681/10000000000 : ℝ)*X 2 0+(4584943513/10000000000 : ℝ)*X 2 1+(4033273101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13317510767471037391924142379/2813750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1148357267/100000000000000 : ℝ)*(base19) + (61764389/5000000000000 : ℝ)*(base23) + (124018879/100000000000000 : ℝ)*(upper3) + (4375307/50000000000000 : ℝ)*(upper4) + (28885217/25000000000000 : ℝ)*(upper5) + (2831165565759219/100000000000000 : ℝ)*(major0) + (2831165565759219/100000000000000 : ℝ)*(major1) + (2831165565759219/100000000000000 : ℝ)*(major2) + (3870531106019831/100000000000000 : ℝ)*(sp0) + (3870546103155351/100000000000000 : ℝ)*(sp1) + (1935273008112419/50000000000000 : ℝ)*(sp2) + (358355122094291/20000000000000 : ℝ)*(sp3) + (16145492787/100000000000000 : ℝ)*(sp4) + (506985457/6250000000000 : ℝ)*(sp7) + (895891861119383/50000000000000 : ℝ)*(f.failure) + (1935273625756309/50000000000000 : ℝ)*(f.sum) + (51774589194839/14068750000000000000000000000 : ℝ)*base65 + (21842658613786469207/5627500000000000000000000000000000 : ℝ)*base67 + (1149667625841469207/5627500000000000000000000000000000 : ℝ)*base69 + (43955098789026469207/5627500000000000000000000000000000 : ℝ)*base71 + (62242946113603/28137500000000000000000000000 : ℝ)*base73 + (52002666940653530793/5627500000000000000000000000000000 : ℝ)*base76 + (13618581473911030793/5627500000000000000000000000000000 : ℝ)*base78 + (30514675827053969207/5627500000000000000000000000000000 : ℝ)*base79 + (45706507177881/56275000000000000000000000000 : ℝ)*base81 + (1733587/250000000000000000000 : ℝ)*base90 + (1733587/250000000000000000000 : ℝ)*base92 + (1733587/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (446155964755016484456459/56275000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167067957/20000000000000 : ℝ)*(base19) + (973259223/100000000000000 : ℝ)*(base23) + (52268083/25000000000000 : ℝ)*(upper3) + (84911357/100000000000000 : ℝ)*(lower4) + (308809/250000000000 : ℝ)*(upper5) + (358022296716059/12500000000000 : ℝ)*(major0) + (358022296716059/12500000000000 : ℝ)*(major1) + (358022296716059/12500000000000 : ℝ)*(major2) + (119528933/1000000000000 : ℝ)*(sp1) + (215543157/1562500000000 : ℝ)*(sp2) + (195783983282889/5000000000000 : ℝ)*(sp4) + (1957833438712347/50000000000000 : ℝ)*(sp5) + (3915664897636509/100000000000000 : ℝ)*(sp6) + (1812676817527893/100000000000000 : ℝ)*(sp7) + (1812676817527893/100000000000000 : ℝ)*(f.failure) + (195783983282889/5000000000000 : ℝ)*(f.sum) + (22399082783653/56275000000000000000000000000 : ℝ)*base65 + (430593558535789773/703437500000000000000000000000000 : ℝ)*base68 + (1838913590799539773/703437500000000000000000000000000 : ℝ)*base70 + (138801383616085227/703437500000000000000000000000000 : ℝ)*base71 + (117765258929847/56275000000000000000000000000 : ℝ)*base74 + (9341517865629835227/703437500000000000000000000000000 : ℝ)*base75 + (2320027111929227273/703437500000000000000000000000000 : ℝ)*base78 + (2849352186041397727/703437500000000000000000000000000 : ℝ)*base79 + (28639317660197/56275000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1335977/500000000000000000000 : ℝ)*base90 + (1335977/500000000000000000000 : ℝ)*base92 + (1335977/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1425_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18873/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3809/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5173/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1425_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1425_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5173/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1425_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1425_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1425_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5173/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3953/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1425_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

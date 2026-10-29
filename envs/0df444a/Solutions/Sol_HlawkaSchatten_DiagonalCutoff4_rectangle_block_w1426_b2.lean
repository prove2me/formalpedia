-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1426_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:55.951046+00:00
-- url     : https://prove2.me/submissions/2f72a4b5-aac6-4e33-b54d-a73d5d0ea307

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
theorem support_rectangle_w1426_s6_0 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-49339181/250000000 : ℝ)*x 0 + (676047029/1250000000 : ℝ)*x 1 + (5246836327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49339181/250000000 : ℝ)^2193 ≤ (6019623601807/50000000000000 : ℝ)^1681 := by
    have hnat : (49339181 : ℕ)^2193*50000000000000^1681 ≤ 6019623601807^1681*250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49339181 250000000 6019623601807 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676047029/1250000000 : ℝ)^2193 ≤ (11212546504003/25000000000000 : ℝ)^1681 := by
    have hnat : (676047029 : ℕ)^2193*25000000000000^1681 ≤ 11212546504003^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676047029 1250000000 11212546504003 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246836327/10000000000 : ℝ)^2193 ≤ (5388820845557/12500000000000 : ℝ)^1681 := by
    have hnat : (5246836327 : ℕ)^2193*12500000000000^1681 ≤ 5388820845557^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246836327 10000000000 5388820845557 12500000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49339181/250000000 : ℝ), (676047029/1250000000 : ℝ), (5246836327/10000000000 : ℝ)] ![(6019623601807/50000000000000 : ℝ), (11212546504003/25000000000000 : ℝ), (5388820845557/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49339181/250000000 : ℝ)|^2193 ≤ (6019623601807/50000000000000 : ℝ)^1681
        have hw : |(-49339181/250000000 : ℝ)|=(49339181/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676047029/1250000000 : ℝ)|^2193 ≤ (11212546504003/25000000000000 : ℝ)^1681
        have hw : |(676047029/1250000000 : ℝ)|=(676047029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246836327/10000000000 : ℝ)|^2193 ≤ (5388820845557/12500000000000 : ℝ)^1681
        have hw : |(5246836327/10000000000 : ℝ)|=(5246836327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s6_1 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26736953/50000000 : ℝ)*x 0 + (-513952959/2500000000 : ℝ)*x 1 + (5246836357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26736953/50000000 : ℝ)^2193 ≤ (2761971692031/6250000000000 : ℝ)^1681 := by
    have hnat : (26736953 : ℕ)^2193*6250000000000^1681 ≤ 2761971692031^1681*50000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26736953 50000000 2761971692031 6250000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513952959/2500000000 : ℝ)^2193 ≤ (793617863957/6250000000000 : ℝ)^1681 := by
    have hnat : (513952959 : ℕ)^2193*6250000000000^1681 ≤ 793617863957^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513952959 2500000000 793617863957 6250000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246836357/10000000000 : ℝ)^2193 ≤ (10777641771507/25000000000000 : ℝ)^1681 := by
    have hnat : (5246836357 : ℕ)^2193*25000000000000^1681 ≤ 10777641771507^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246836357 10000000000 10777641771507 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26736953/50000000 : ℝ), (-513952959/2500000000 : ℝ), (5246836357/10000000000 : ℝ)] ![(2761971692031/6250000000000 : ℝ), (793617863957/6250000000000 : ℝ), (10777641771507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26736953/50000000 : ℝ)|^2193 ≤ (2761971692031/6250000000000 : ℝ)^1681
        have hw : |(26736953/50000000 : ℝ)|=(26736953/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513952959/2500000000 : ℝ)|^2193 ≤ (793617863957/6250000000000 : ℝ)^1681
        have hw : |(-513952959/2500000000 : ℝ)|=(513952959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246836357/10000000000 : ℝ)|^2193 ≤ (10777641771507/25000000000000 : ℝ)^1681
        have hw : |(5246836357/10000000000 : ℝ)|=(5246836357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s6_2 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347390593/10000000000 : ℝ)*x 0 + (5246836353/10000000000 : ℝ)*x 1 + (-2055811851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347390593/10000000000 : ℝ)^2193 ≤ (44191546997027/100000000000000 : ℝ)^1681 := by
    have hnat : (5347390593 : ℕ)^2193*100000000000000^1681 ≤ 44191546997027^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347390593 10000000000 44191546997027 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246836353/10000000000 : ℝ)^2193 ≤ (2694410440197/6250000000000 : ℝ)^1681 := by
    have hnat : (5246836353 : ℕ)^2193*6250000000000^1681 ≤ 2694410440197^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246836353 10000000000 2694410440197 6250000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055811851/10000000000 : ℝ)^2193 ≤ (634894297209/5000000000000 : ℝ)^1681 := by
    have hnat : (2055811851 : ℕ)^2193*5000000000000^1681 ≤ 634894297209^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055811851 10000000000 634894297209 5000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347390593/10000000000 : ℝ), (5246836353/10000000000 : ℝ), (-2055811851/10000000000 : ℝ)] ![(44191546997027/100000000000000 : ℝ), (2694410440197/6250000000000 : ℝ), (634894297209/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347390593/10000000000 : ℝ)|^2193 ≤ (44191546997027/100000000000000 : ℝ)^1681
        have hw : |(5347390593/10000000000 : ℝ)|=(5347390593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246836353/10000000000 : ℝ)|^2193 ≤ (2694410440197/6250000000000 : ℝ)^1681
        have hw : |(5246836353/10000000000 : ℝ)|=(5246836353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055811851/10000000000 : ℝ)|^2193 ≤ (634894297209/5000000000000 : ℝ)^1681
        have hw : |(-2055811851/10000000000 : ℝ)|=(2055811851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s6_3 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1076280949/2500000000 : ℝ)*x 0 + (51672127/125000000 : ℝ)*x 1 + (4482850851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076280949/2500000000 : ℝ)^2193 ≤ (6660928401631/20000000000000 : ℝ)^1681 := by
    have hnat : (1076280949 : ℕ)^2193*20000000000000^1681 ≤ 6660928401631^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076280949 2500000000 6660928401631 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51672127/125000000 : ℝ)^2193 ≤ (31585870982877/100000000000000 : ℝ)^1681 := by
    have hnat : (51672127 : ℕ)^2193*100000000000000^1681 ≤ 31585870982877^1681*125000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51672127 125000000 31585870982877 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482850851/10000000000 : ℝ)^2193 ≤ (17554743498561/50000000000000 : ℝ)^1681 := by
    have hnat : (4482850851 : ℕ)^2193*50000000000000^1681 ≤ 17554743498561^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482850851 10000000000 17554743498561 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076280949/2500000000 : ℝ), (51672127/125000000 : ℝ), (4482850851/10000000000 : ℝ)] ![(6660928401631/20000000000000 : ℝ), (31585870982877/100000000000000 : ℝ), (17554743498561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076280949/2500000000 : ℝ)|^2193 ≤ (6660928401631/20000000000000 : ℝ)^1681
        have hw : |(1076280949/2500000000 : ℝ)|=(1076280949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51672127/125000000 : ℝ)|^2193 ≤ (31585870982877/100000000000000 : ℝ)^1681
        have hw : |(51672127/125000000 : ℝ)|=(51672127/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482850851/10000000000 : ℝ)|^2193 ≤ (17554743498561/50000000000000 : ℝ)^1681
        have hw : |(4482850851/10000000000 : ℝ)|=(4482850851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s6_4 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1973578593/10000000000 : ℝ)*x 0 + (5247418817/10000000000 : ℝ)*x 1 + (2703895363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973578593/10000000000 : ℝ)^2193 ≤ (601966877693/5000000000000 : ℝ)^1681 := by
    have hnat : (1973578593 : ℕ)^2193*5000000000000^1681 ≤ 601966877693^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973578593 10000000000 601966877693 5000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247418817/10000000000 : ℝ)^2193 ≤ (43116810621487/100000000000000 : ℝ)^1681 := by
    have hnat : (5247418817 : ℕ)^2193*100000000000000^1681 ≤ 43116810621487^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247418817 10000000000 43116810621487 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703895363/5000000000 : ℝ)^2193 ≤ (8968770361193/20000000000000 : ℝ)^1681 := by
    have hnat : (2703895363 : ℕ)^2193*20000000000000^1681 ≤ 8968770361193^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703895363 5000000000 8968770361193 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1973578593/10000000000 : ℝ), (5247418817/10000000000 : ℝ), (2703895363/5000000000 : ℝ)] ![(601966877693/5000000000000 : ℝ), (43116810621487/100000000000000 : ℝ), (8968770361193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1973578593/10000000000 : ℝ)|^2193 ≤ (601966877693/5000000000000 : ℝ)^1681
        have hw : |(-1973578593/10000000000 : ℝ)|=(1973578593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247418817/10000000000 : ℝ)|^2193 ≤ (43116810621487/100000000000000 : ℝ)^1681
        have hw : |(5247418817/10000000000 : ℝ)|=(5247418817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703895363/5000000000 : ℝ)|^2193 ≤ (8968770361193/20000000000000 : ℝ)^1681
        have hw : |(2703895363/5000000000 : ℝ)|=(2703895363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s6_5 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305406951/10000000000 : ℝ)*x 0 + (-236857181/1250000000 : ℝ)*x 1 + (216311629/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305406951/10000000000 : ℝ)^2193 ≤ (43739453985493/100000000000000 : ℝ)^1681 := by
    have hnat : (5305406951 : ℕ)^2193*100000000000000^1681 ≤ 43739453985493^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305406951 10000000000 43739453985493 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236857181/1250000000 : ℝ)^2193 ≤ (11416694194647/100000000000000 : ℝ)^1681 := by
    have hnat : (236857181 : ℕ)^2193*100000000000000^1681 ≤ 11416694194647^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236857181 1250000000 11416694194647 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216311629/400000000 : ℝ)^2193 ≤ (44843851795147/100000000000000 : ℝ)^1681 := by
    have hnat : (216311629 : ℕ)^2193*100000000000000^1681 ≤ 44843851795147^1681*400000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216311629 400000000 44843851795147 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305406951/10000000000 : ℝ), (-236857181/1250000000 : ℝ), (216311629/400000000 : ℝ)] ![(43739453985493/100000000000000 : ℝ), (11416694194647/100000000000000 : ℝ), (44843851795147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305406951/10000000000 : ℝ)|^2193 ≤ (43739453985493/100000000000000 : ℝ)^1681
        have hw : |(5305406951/10000000000 : ℝ)|=(5305406951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236857181/1250000000 : ℝ)|^2193 ≤ (11416694194647/100000000000000 : ℝ)^1681
        have hw : |(-236857181/1250000000 : ℝ)|=(236857181/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216311629/400000000 : ℝ)|^2193 ≤ (44843851795147/100000000000000 : ℝ)^1681
        have hw : |(216311629/400000000 : ℝ)|=(216311629/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s6_6 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061081391/2000000000 : ℝ)*x 0 + (5407790721/10000000000 : ℝ)*x 1 + (-1894857449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061081391/2000000000 : ℝ)^2193 ≤ (21869727014257/50000000000000 : ℝ)^1681 := by
    have hnat : (1061081391 : ℕ)^2193*50000000000000^1681 ≤ 21869727014257^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061081391 2000000000 21869727014257 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407790721/10000000000 : ℝ)^2193 ≤ (22421925875937/50000000000000 : ℝ)^1681 := by
    have hnat : (5407790721 : ℕ)^2193*50000000000000^1681 ≤ 22421925875937^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407790721 10000000000 22421925875937 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1894857449/10000000000 : ℝ)^2193 ≤ (11416694202507/100000000000000 : ℝ)^1681 := by
    have hnat : (1894857449 : ℕ)^2193*100000000000000^1681 ≤ 11416694202507^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894857449 10000000000 11416694202507 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061081391/2000000000 : ℝ), (5407790721/10000000000 : ℝ), (-1894857449/10000000000 : ℝ)] ![(21869727014257/50000000000000 : ℝ), (22421925875937/50000000000000 : ℝ), (11416694202507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061081391/2000000000 : ℝ)|^2193 ≤ (21869727014257/50000000000000 : ℝ)^1681
        have hw : |(1061081391/2000000000 : ℝ)|=(1061081391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407790721/10000000000 : ℝ)|^2193 ≤ (22421925875937/50000000000000 : ℝ)^1681
        have hw : |(5407790721/10000000000 : ℝ)|=(5407790721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1894857449/10000000000 : ℝ)|^2193 ≤ (11416694202507/100000000000000 : ℝ)^1681
        have hw : |(-1894857449/10000000000 : ℝ)|=(1894857449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s6_7 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2152574179/5000000000 : ℝ)*x 0 + (4481592131/10000000000 : ℝ)*x 1 + (827007073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152574179/5000000000 : ℝ)^2193 ≤ (33304889895381/100000000000000 : ℝ)^1681 := by
    have hnat : (2152574179 : ℕ)^2193*100000000000000^1681 ≤ 33304889895381^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152574179 5000000000 33304889895381 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481592131/10000000000 : ℝ)^2193 ≤ (7019325336031/20000000000000 : ℝ)^1681 := by
    have hnat : (4481592131 : ℕ)^2193*20000000000000^1681 ≤ 7019325336031^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481592131 10000000000 7019325336031 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827007073/2000000000 : ℝ)^2193 ≤ (15799241703839/50000000000000 : ℝ)^1681 := by
    have hnat : (827007073 : ℕ)^2193*50000000000000^1681 ≤ 15799241703839^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827007073 2000000000 15799241703839 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152574179/5000000000 : ℝ), (4481592131/10000000000 : ℝ), (827007073/2000000000 : ℝ)] ![(33304889895381/100000000000000 : ℝ), (7019325336031/20000000000000 : ℝ), (15799241703839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152574179/5000000000 : ℝ)|^2193 ≤ (33304889895381/100000000000000 : ℝ)^1681
        have hw : |(2152574179/5000000000 : ℝ)|=(2152574179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481592131/10000000000 : ℝ)|^2193 ≤ (7019325336031/20000000000000 : ℝ)^1681
        have hw : |(4481592131/10000000000 : ℝ)|=(4481592131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827007073/2000000000 : ℝ)|^2193 ≤ (15799241703839/50000000000000 : ℝ)^1681
        have hw : |(827007073/2000000000 : ℝ)|=(827007073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1426_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5667/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3689/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1133/10000 : ℝ) ^ (4385/1024 : ℝ) ≤ (4456236200545107/50000000000000000000 : ℝ) := by
    have hpowers : (1133/10000 : ℝ)^4385 ≤ (4456236200545107/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1133 : ℕ)^4385*50000000000000000000^1024 ≤ 4456236200545107^1024*10000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1133 10000 4456236200545107 50000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1133/10000 : ℝ)) (X := (4456236200545107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (4385/1024 : ℝ) ≤ (27651170840751543/100000000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^4385 ≤ (27651170840751543/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14759 : ℕ)^4385*100000000000000000000^1024 ≤ 27651170840751543^1024*100000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 27651170840751543 100000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (27651170840751543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004456236200545107/25000000000000000000 : ℝ) ≤ (10000416225695019/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (25004456236200545107/25000000000000000000 : ℝ)^1024 ≤ (10000416225695019/10000000000000000 : ℝ)^4385 := by
      have hnat : (25004456236200545107 : ℕ)^1024*10000000000000000^4385 ≤ 10000416225695019^4385*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004456236200545107 25000000000000000000 10000416225695019 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000416225695019/10000000000000000 : ℝ)) (X := (25004456236200545107/25000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036563643241841757/100000000000000000000 : ℝ) ≤ (5000426863458741/5000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (100036563643241841757/100000000000000000000 : ℝ)^1024 ≤ (5000426863458741/5000000000000000 : ℝ)^4385 := by
      have hnat : (100036563643241841757 : ℕ)^1024*5000000000000000^4385 ≤ 5000426863458741^4385*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036563643241841757 100000000000000000000 5000426863458741 5000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000426863458741/5000000000000000 : ℝ)) (X := (100036563643241841757/100000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027651170840751543/50000000000000000000 : ℝ) ≤ (2000258245627989/2000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (50027651170840751543/50000000000000000000 : ℝ)^1024 ≤ (2000258245627989/2000000000000000 : ℝ)^4385 := by
      have hnat : (50027651170840751543 : ℕ)^1024*2000000000000000^4385 ≤ 2000258245627989^4385*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027651170840751543 50000000000000000000 2000258245627989 2000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000258245627989/2000000000000000 : ℝ)) (X := (50027651170840751543/50000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4456236200545107/50000000000000000000 : ℝ) ≤ ((11427171153402402857/11430000000000000000 : ℝ)+2*(145833740821/114300000000000 : ℝ)*(1133/10000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (11427171153402402857/11430000000000000000 : ℝ)+2*(145833740821/114300000000000 : ℝ)*(1133/10000 : ℝ)=(10000416225695019/10000000000000000 : ℝ) by norm_num, show 1+2*(4456236200545107/50000000000000000000 : ℝ)=(25004456236200545107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27651170840751543/100000000000000000000 : ℝ)+(4456236200545107/50000000000000000000 : ℝ) ≤ ((11427171153402402857/11430000000000000000 : ℝ)+(145833740821/114300000000000 : ℝ)*((14759/100000 : ℝ)+(1133/10000 : ℝ)))^(4385/1024 : ℝ) := by
    rw [show (11427171153402402857/11430000000000000000 : ℝ)+(145833740821/114300000000000 : ℝ)*((14759/100000 : ℝ)+(1133/10000 : ℝ))=(5000426863458741/5000000000000000 : ℝ) by norm_num, show 1+(27651170840751543/100000000000000000000 : ℝ)+(4456236200545107/50000000000000000000 : ℝ)=(100036563643241841757/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27651170840751543/100000000000000000000 : ℝ) ≤ ((11427171153402402857/11430000000000000000 : ℝ)+2*(145833740821/114300000000000 : ℝ)*(14759/100000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (11427171153402402857/11430000000000000000 : ℝ)+2*(145833740821/114300000000000 : ℝ)*(14759/100000 : ℝ)=(2000258245627989/2000000000000000 : ℝ) by norm_num, show 1+2*(27651170840751543/100000000000000000000 : ℝ)=(50027651170840751543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11427171153402402857/11430000000000000000 : ℝ)*(X 1 0+X 2 0)+(145833740821/114300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (11427171153402402857/11430000000000000000 : ℝ)) (alpha := (145833740821/114300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11427171153402402857/11430000000000000000 : ℝ)*(X 0 1+X 2 1)+(145833740821/114300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (11427171153402402857/11430000000000000000 : ℝ)) (alpha := (145833740821/114300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11427171153402402857/11430000000000000000 : ℝ)*(X 0 2+X 1 2)+(145833740821/114300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (11427171153402402857/11430000000000000000 : ℝ)) (alpha := (145833740821/114300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-49339181/250000000 : ℝ)*X 0 0+(676047029/1250000000 : ℝ)*X 0 1+(5246836327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((26736953/50000000 : ℝ)*X 1 0+(-513952959/2500000000 : ℝ)*X 1 1+(5246836357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347390593/10000000000 : ℝ)*X 2 0+(5246836353/10000000000 : ℝ)*X 2 1+(-2055811851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1076280949/2500000000 : ℝ)*X 0 0+(51672127/125000000 : ℝ)*X 0 1+(4482850851/10000000000 : ℝ)*X 0 2+(1076280949/2500000000 : ℝ)*X 1 0+(51672127/125000000 : ℝ)*X 1 1+(4482850851/10000000000 : ℝ)*X 1 2+(1076280949/2500000000 : ℝ)*X 2 0+(51672127/125000000 : ℝ)*X 2 1+(4482850851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1973578593/10000000000 : ℝ)*X 0 0+(5247418817/10000000000 : ℝ)*X 0 1+(2703895363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305406951/10000000000 : ℝ)*X 1 0+(-236857181/1250000000 : ℝ)*X 1 1+(216311629/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061081391/2000000000 : ℝ)*X 2 0+(5407790721/10000000000 : ℝ)*X 2 1+(-1894857449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2152574179/5000000000 : ℝ)*X 0 0+(4481592131/10000000000 : ℝ)*X 0 1+(827007073/2000000000 : ℝ)*X 0 2+(2152574179/5000000000 : ℝ)*X 1 0+(4481592131/10000000000 : ℝ)*X 1 1+(827007073/2000000000 : ℝ)*X 1 2+(2152574179/5000000000 : ℝ)*X 2 0+(4481592131/10000000000 : ℝ)*X 2 1+(827007073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181592343606812611152434317/38100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (398166217/50000000000000 : ℝ)*(base19) + (93090667/12500000000000 : ℝ)*(base23) + (23263011/100000000000000 : ℝ)*(lower2) + (5970603/5000000000000 : ℝ)*(upper3) + (8435307/12500000000000 : ℝ)*(upper5) + (905514024660219/20000000000000 : ℝ)*(major0) + (905514024660219/20000000000000 : ℝ)*(major1) + (565946265412637/12500000000000 : ℝ)*(major2) + (3095219772104993/50000000000000 : ℝ)*(sp0) + (773806999911841/12500000000000 : ℝ)*(sp1) + (6190456050901827/100000000000000 : ℝ)*(sp2) + (716168687053693/25000000000000 : ℝ)*(sp3) + (17251417177/100000000000000 : ℝ)*(sp4) + (8543886803/100000000000000 : ℝ)*(sp7) + (1432341646050787/50000000000000 : ℝ)*(f.failure) + (6190456795627163/100000000000000 : ℝ)*(f.sum) + (20862538351739/11430000000000000000000000000 : ℝ)*base66 + (1226769697659765683/228600000000000000000000000000000 : ℝ)*base67 + (147187693938983591/142875000000000000000000000000000 : ℝ)*base70 + (3717054038696565683/228600000000000000000000000000000 : ℝ)*base71 + (2792227038661/11430000000000000000000000000 : ℝ)*base73 + (1563002628561516409/142875000000000000000000000000000 : ℝ)*base75 + (63951191400616187/25400000000000000000000000000000 : ℝ)*base77 + (75635022873183813/25400000000000000000000000000000 : ℝ)*base80 + (232724107481/127000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (21124173/2500000000000000000000 : ℝ)*base90 + (21124173/2500000000000000000000 : ℝ)*base92 + (46124173/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (739134231797487550348304763/63500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1972493573/100000000000000 : ℝ)*(base19) + (2145593553/100000000000000 : ℝ)*(base23) + (668668861/100000000000000 : ℝ)*(lower1) + (236517909/100000000000000 : ℝ)*(upper3) + (76691291/100000000000000 : ℝ)*(lower4) + (240602847/100000000000000 : ℝ)*(upper5) + (4560486720560023/100000000000000 : ℝ)*(major0) + (4560486720560023/100000000000000 : ℝ)*(major1) + (4560486720560023/100000000000000 : ℝ)*(major2) + (3013345291/100000000000000 : ℝ)*(sp2) + (6235462777974823/100000000000000 : ℝ)*(sp4) + (997673728877/16000000000 : ℝ)*(sp5) + (3117728809517989/50000000000000 : ℝ)*(sp6) + (144275513757411/5000000000000 : ℝ)*(sp7) + (144275513757411/5000000000000 : ℝ)*(f.failure) + (6235462777974823/100000000000000 : ℝ)*(f.sum) + (2064340424477/357187500000000000000000000 : ℝ)*base66 + (7021484876203495237/381000000000000000000000000000000 : ℝ)*base67 + (954136937443504763/381000000000000000000000000000000 : ℝ)*base70 + (43360201772284495237/381000000000000000000000000000000 : ℝ)*base71 + (15026900177417/5715000000000000000000000000 : ℝ)*base74 + (45923763057955504763/381000000000000000000000000000000 : ℝ)*base76 + (2219629061341495237/381000000000000000000000000000000 : ℝ)*base77 + (2300407398133495237/381000000000000000000000000000000 : ℝ)*base79 + (9727807663759/714375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2528531/250000000000000000000 : ℝ)*base89 + (2528531/250000000000000000000 : ℝ)*base91 + (2528531/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1426_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1426_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1426_s7_0 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336846301/2500000000 : ℝ)*x 0 + (5246860571/10000000000 : ℝ)*x 1 + (-411157369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336846301/2500000000 : ℝ)^2193 ≤ (44191488897001/100000000000000 : ℝ)^1681 := by
    have hnat : (1336846301 : ℕ)^2193*100000000000000^1681 ≤ 44191488897001^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336846301 2500000000 44191488897001 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246860571/10000000000 : ℝ)^2193 ≤ (10777706659447/25000000000000 : ℝ)^1681 := by
    have hnat : (5246860571 : ℕ)^2193*25000000000000^1681 ≤ 10777706659447^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246860571 10000000000 10777706659447 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411157369/2000000000 : ℝ)^2193 ≤ (253953689001/2000000000000 : ℝ)^1681 := by
    have hnat : (411157369 : ℕ)^2193*2000000000000^1681 ≤ 253953689001^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411157369 2000000000 253953689001 2000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336846301/2500000000 : ℝ), (5246860571/10000000000 : ℝ), (-411157369/2000000000 : ℝ)] ![(44191488897001/100000000000000 : ℝ), (10777706659447/25000000000000 : ℝ), (253953689001/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336846301/2500000000 : ℝ)|^2193 ≤ (44191488897001/100000000000000 : ℝ)^1681
        have hw : |(1336846301/2500000000 : ℝ)|=(1336846301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246860571/10000000000 : ℝ)|^2193 ≤ (10777706659447/25000000000000 : ℝ)^1681
        have hw : |(5246860571/10000000000 : ℝ)|=(5246860571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411157369/2000000000 : ℝ)|^2193 ≤ (253953689001/2000000000000 : ℝ)^1681
        have hw : |(-411157369/2000000000 : ℝ)|=(411157369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s7_1 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1973578661/10000000000 : ℝ)*x 0 + (2623721373/5000000000 : ℝ)*x 1 + (2703883483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973578661/10000000000 : ℝ)^2193 ≤ (12039338095023/100000000000000 : ℝ)^1681 := by
    have hnat : (1973578661 : ℕ)^2193*100000000000000^1681 ≤ 12039338095023^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973578661 10000000000 12039338095023 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623721373/5000000000 : ℝ)^2193 ≤ (43117067126979/100000000000000 : ℝ)^1681 := by
    have hnat : (2623721373 : ℕ)^2193*100000000000000^1681 ≤ 43117067126979^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623721373 5000000000 43117067126979 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703883483/5000000000 : ℝ)^2193 ≤ (4484359476633/10000000000000 : ℝ)^1681 := by
    have hnat : (2703883483 : ℕ)^2193*10000000000000^1681 ≤ 4484359476633^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703883483 5000000000 4484359476633 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1973578661/10000000000 : ℝ), (2623721373/5000000000 : ℝ), (2703883483/5000000000 : ℝ)] ![(12039338095023/100000000000000 : ℝ), (43117067126979/100000000000000 : ℝ), (4484359476633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1973578661/10000000000 : ℝ)|^2193 ≤ (12039338095023/100000000000000 : ℝ)^1681
        have hw : |(-1973578661/10000000000 : ℝ)|=(1973578661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623721373/5000000000 : ℝ)|^2193 ≤ (43117067126979/100000000000000 : ℝ)^1681
        have hw : |(2623721373/5000000000 : ℝ)|=(2623721373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703883483/5000000000 : ℝ)|^2193 ≤ (4484359476633/10000000000000 : ℝ)^1681
        have hw : |(2703883483/5000000000 : ℝ)|=(2703883483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s7_2 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305414011/10000000000 : ℝ)*x 0 + (-1894880489/10000000000 : ℝ)*x 1 + (2703883483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305414011/10000000000 : ℝ)^2193 ≤ (43739529918459/100000000000000 : ℝ)^1681 := by
    have hnat : (5305414011 : ℕ)^2193*100000000000000^1681 ≤ 43739529918459^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305414011 10000000000 43739529918459 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1894880489/10000000000 : ℝ)^2193 ≤ (11416875302329/100000000000000 : ℝ)^1681 := by
    have hnat : (1894880489 : ℕ)^2193*100000000000000^1681 ≤ 11416875302329^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894880489 10000000000 11416875302329 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703883483/5000000000 : ℝ)^2193 ≤ (4484359476633/10000000000000 : ℝ)^1681 := by
    have hnat : (2703883483 : ℕ)^2193*10000000000000^1681 ≤ 4484359476633^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703883483 5000000000 4484359476633 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305414011/10000000000 : ℝ), (-1894880489/10000000000 : ℝ), (2703883483/5000000000 : ℝ)] ![(43739529918459/100000000000000 : ℝ), (11416875302329/100000000000000 : ℝ), (4484359476633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305414011/10000000000 : ℝ)|^2193 ≤ (43739529918459/100000000000000 : ℝ)^1681
        have hw : |(5305414011/10000000000 : ℝ)|=(5305414011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1894880489/10000000000 : ℝ)|^2193 ≤ (11416875302329/100000000000000 : ℝ)^1681
        have hw : |(-1894880489/10000000000 : ℝ)|=(1894880489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703883483/5000000000 : ℝ)|^2193 ≤ (4484359476633/10000000000000 : ℝ)^1681
        have hw : |(2703883483/5000000000 : ℝ)|=(2703883483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s7_3 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326353503/2500000000 : ℝ)*x 0 + (2703883483/5000000000 : ℝ)*x 1 + (-236860061/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326353503/2500000000 : ℝ)^2193 ≤ (21869764964607/50000000000000 : ℝ)^1681 := by
    have hnat : (1326353503 : ℕ)^2193*50000000000000^1681 ≤ 21869764964607^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326353503 2500000000 21869764964607 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703883483/5000000000 : ℝ)^2193 ≤ (4484359476633/10000000000000 : ℝ)^1681 := by
    have hnat : (2703883483 : ℕ)^2193*10000000000000^1681 ≤ 4484359476633^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703883483 5000000000 4484359476633 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236860061/1250000000 : ℝ)^2193 ≤ (11416875294469/100000000000000 : ℝ)^1681 := by
    have hnat : (236860061 : ℕ)^2193*100000000000000^1681 ≤ 11416875294469^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236860061 1250000000 11416875294469 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326353503/2500000000 : ℝ), (2703883483/5000000000 : ℝ), (-236860061/1250000000 : ℝ)] ![(21869764964607/50000000000000 : ℝ), (4484359476633/10000000000000 : ℝ), (11416875294469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326353503/2500000000 : ℝ)|^2193 ≤ (21869764964607/50000000000000 : ℝ)^1681
        have hw : |(1326353503/2500000000 : ℝ)|=(1326353503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703883483/5000000000 : ℝ)|^2193 ≤ (4484359476633/10000000000000 : ℝ)^1681
        have hw : |(2703883483/5000000000 : ℝ)|=(2703883483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-236860061/1250000000 : ℝ)|^2193 ≤ (11416875294469/100000000000000 : ℝ)^1681
        have hw : |(-236860061/1250000000 : ℝ)|=(236860061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_s7_4 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1076287509/2500000000 : ℝ)*x 0 + (4481540401/10000000000 : ℝ)*x 1 + (103377167/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076287509/2500000000 : ℝ)^2193 ≤ (33304906830287/100000000000000 : ℝ)^1681 := by
    have hnat : (1076287509 : ℕ)^2193*100000000000000^1681 ≤ 33304906830287^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076287509 2500000000 33304906830287 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481540401/10000000000 : ℝ)^2193 ≤ (8774024544829/25000000000000 : ℝ)^1681 := by
    have hnat : (4481540401 : ℕ)^2193*25000000000000^1681 ≤ 8774024544829^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481540401 10000000000 8774024544829 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103377167/250000000 : ℝ)^2193 ≤ (31598994975339/100000000000000 : ℝ)^1681 := by
    have hnat : (103377167 : ℕ)^2193*100000000000000^1681 ≤ 31598994975339^1681*250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103377167 250000000 31598994975339 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076287509/2500000000 : ℝ), (4481540401/10000000000 : ℝ), (103377167/250000000 : ℝ)] ![(33304906830287/100000000000000 : ℝ), (8774024544829/25000000000000 : ℝ), (31598994975339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076287509/2500000000 : ℝ)|^2193 ≤ (33304906830287/100000000000000 : ℝ)^1681
        have hw : |(1076287509/2500000000 : ℝ)|=(1076287509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481540401/10000000000 : ℝ)|^2193 ≤ (8774024544829/25000000000000 : ℝ)^1681
        have hw : |(4481540401/10000000000 : ℝ)|=(4481540401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103377167/250000000 : ℝ)|^2193 ≤ (31598994975339/100000000000000 : ℝ)^1681
        have hw : |(103377167/250000000 : ℝ)|=(103377167/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1426_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5667/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2951/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5667/50000 : ℝ) ^ (4385/1024 : ℝ) ≤ (8925954252607789/100000000000000000000 : ℝ) := by
    have hpowers : (5667/50000 : ℝ)^4385 ≤ (8925954252607789/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5667 : ℕ)^4385*100000000000000000000^1024 ≤ 8925954252607789^1024*50000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5667 50000 8925954252607789 100000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5667/50000 : ℝ)) (X := (8925954252607789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3689/25000 : ℝ) ^ (4385/1024 : ℝ) ≤ (27627110453454843/100000000000000000000 : ℝ) := by
    have hpowers : (3689/25000 : ℝ)^4385 ≤ (27627110453454843/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3689 : ℕ)^4385*100000000000000000000^1024 ≤ 27627110453454843^1024*25000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689 25000 27627110453454843 100000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3689/25000 : ℝ)) (X := (27627110453454843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008925954252607789/50000000000000000000 : ℝ) ≤ (5000208427637217/5000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (50008925954252607789/50000000000000000000 : ℝ)^1024 ≤ (5000208427637217/5000000000000000 : ℝ)^4385 := by
      have hnat : (50008925954252607789 : ℕ)^1024*5000000000000000^4385 ≤ 5000208427637217^4385*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008925954252607789 50000000000000000000 5000208427637217 5000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000208427637217/5000000000000000 : ℝ)) (X := (50008925954252607789/50000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504569133088257829/12500000000000000000 : ℝ) ≤ (10000853479953143/10000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (12504569133088257829/12500000000000000000 : ℝ)^1024 ≤ (10000853479953143/10000000000000000 : ℝ)^4385 := by
      have hnat : (12504569133088257829 : ℕ)^1024*10000000000000000^4385 ≤ 10000853479953143^4385*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504569133088257829 12500000000000000000 10000853479953143 10000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000853479953143/10000000000000000 : ℝ)) (X := (12504569133088257829/12500000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027627110453454843/50000000000000000000 : ℝ) ≤ (2500322526157963/2500000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (50027627110453454843/50000000000000000000 : ℝ)^1024 ≤ (2500322526157963/2500000000000000 : ℝ)^4385 := by
      have hnat : (50027627110453454843 : ℕ)^1024*2500000000000000^4385 ≤ 2500322526157963^4385*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027627110453454843 50000000000000000000 2500322526157963 2500000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500322526157963/2500000000000000 : ℝ)) (X := (50027627110453454843/50000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8925954252607789/100000000000000000000 : ℝ) ≤ ((534555141727064649/534687500000000000 : ℝ)+2*(436624678709/342200000000000 : ℝ)*(5667/50000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (534555141727064649/534687500000000000 : ℝ)+2*(436624678709/342200000000000 : ℝ)*(5667/50000 : ℝ)=(5000208427637217/5000000000000000 : ℝ) by norm_num, show 1+2*(8925954252607789/100000000000000000000 : ℝ)=(50008925954252607789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27627110453454843/100000000000000000000 : ℝ)+(8925954252607789/100000000000000000000 : ℝ) ≤ ((534555141727064649/534687500000000000 : ℝ)+(436624678709/342200000000000 : ℝ)*((3689/25000 : ℝ)+(5667/50000 : ℝ)))^(4385/1024 : ℝ) := by
    rw [show (534555141727064649/534687500000000000 : ℝ)+(436624678709/342200000000000 : ℝ)*((3689/25000 : ℝ)+(5667/50000 : ℝ))=(10000853479953143/10000000000000000 : ℝ) by norm_num, show 1+(27627110453454843/100000000000000000000 : ℝ)+(8925954252607789/100000000000000000000 : ℝ)=(12504569133088257829/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27627110453454843/100000000000000000000 : ℝ) ≤ ((534555141727064649/534687500000000000 : ℝ)+2*(436624678709/342200000000000 : ℝ)*(3689/25000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (534555141727064649/534687500000000000 : ℝ)+2*(436624678709/342200000000000 : ℝ)*(3689/25000 : ℝ)=(2500322526157963/2500000000000000 : ℝ) by norm_num, show 1+2*(27627110453454843/100000000000000000000 : ℝ)=(50027627110453454843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (534555141727064649/534687500000000000 : ℝ)*(X 1 0+X 2 0)+(436624678709/342200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (534555141727064649/534687500000000000 : ℝ)) (alpha := (436624678709/342200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (534555141727064649/534687500000000000 : ℝ)*(X 0 1+X 2 1)+(436624678709/342200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (534555141727064649/534687500000000000 : ℝ)) (alpha := (436624678709/342200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (534555141727064649/534687500000000000 : ℝ)*(X 0 2+X 1 2)+(436624678709/342200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (534555141727064649/534687500000000000 : ℝ)) (alpha := (436624678709/342200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336846301/2500000000 : ℝ)*X 2 0+(5246860571/10000000000 : ℝ)*X 2 1+(-411157369/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1973578661/10000000000 : ℝ)*X 0 0+(2623721373/5000000000 : ℝ)*X 0 1+(2703883483/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5305414011/10000000000 : ℝ)*X 1 0+(-1894880489/10000000000 : ℝ)*X 1 1+(2703883483/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1326353503/2500000000 : ℝ)*X 2 0+(2703883483/5000000000 : ℝ)*X 2 1+(-236860061/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1076287509/2500000000 : ℝ)*X 0 0+(4481540401/10000000000 : ℝ)*X 0 1+(103377167/250000000 : ℝ)*X 0 2+(1076287509/2500000000 : ℝ)*X 1 0+(4481540401/10000000000 : ℝ)*X 1 1+(103377167/250000000 : ℝ)*X 1 2+(1076287509/2500000000 : ℝ)*X 2 0+(4481540401/10000000000 : ℝ)*X 2 1+(103377167/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2228750913121071056564523/334179687500000000000000000000 : ℝ) := by norm_num
    linear_combination (1126541833/100000000000000 : ℝ)*(base19) + (1225003143/100000000000000 : ℝ)*(base23) + (23815279/6250000000000 : ℝ)*(lower1) + (136289799/100000000000000 : ℝ)*(upper3) + (43956653/100000000000000 : ℝ)*(lower4) + (137230231/100000000000000 : ℝ)*(upper5) + (912371337220981/20000000000000 : ℝ)*(major0) + (912371337220981/20000000000000 : ℝ)*(major1) + (912371337220981/20000000000000 : ℝ)*(major2) + (912222897/50000000000000 : ℝ)*(sp0) + (6237336070416549/100000000000000 : ℝ)*(sp1) + (1559333735968679/25000000000000 : ℝ)*(sp2) + (6237333020967613/100000000000000 : ℝ)*(sp3) + (144318853974131/5000000000000 : ℝ)*(sp4) + (144318853974131/5000000000000 : ℝ)*(f.failure) + (6237336070416549/100000000000000 : ℝ)*(f.sum) + (19765834567353/3422000000000000000000000000 : ℝ)*base66 + (292537617544245537/21387500000000000000000000000000 : ℝ)*base68 + (116162797988754463/21387500000000000000000000000000 : ℝ)*base69 + (537389647660229463/21387500000000000000000000000000 : ℝ)*base71 + (14399457811783/3422000000000000000000000000 : ℝ)*base74 + (336763924589479463/21387500000000000000000000000000 : ℝ)*base75 + (82927099545029463/21387500000000000000000000000000 : ℝ)*base77 + (253061788661220537/21387500000000000000000000000000 : ℝ)*base80 + (1066024701557/3422000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1687651/250000000000000000000 : ℝ)*base89 + (1687651/250000000000000000000 : ℝ)*base91 + (1687651/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1426_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1426_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1426_box_0 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1812688919/10000000000 : ℝ)*x 0 + (1346596413/2500000000 : ℝ)*x 1 + (1346596511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1812688919/10000000000 : ℝ)^2193 ≤ (10775140319163/100000000000000 : ℝ)^1681 := by
    have hnat : (1812688919 : ℕ)^2193*100000000000000^1681 ≤ 10775140319163^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812688919 10000000000 10775140319163 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346596413/2500000000 : ℝ)^2193 ≤ (22306213855513/50000000000000 : ℝ)^1681 := by
    have hnat : (1346596413 : ℕ)^2193*50000000000000^1681 ≤ 22306213855513^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346596413 2500000000 22306213855513 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346596511/2500000000 : ℝ)^2193 ≤ (44612431946631/100000000000000 : ℝ)^1681 := by
    have hnat : (1346596511 : ℕ)^2193*100000000000000^1681 ≤ 44612431946631^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346596511 2500000000 44612431946631 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1812688919/10000000000 : ℝ), (1346596413/2500000000 : ℝ), (1346596511/2500000000 : ℝ)] ![(10775140319163/100000000000000 : ℝ), (22306213855513/50000000000000 : ℝ), (44612431946631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1812688919/10000000000 : ℝ)|^2193 ≤ (10775140319163/100000000000000 : ℝ)^1681
        have hw : |(-1812688919/10000000000 : ℝ)|=(1812688919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346596413/2500000000 : ℝ)|^2193 ≤ (22306213855513/50000000000000 : ℝ)^1681
        have hw : |(1346596413/2500000000 : ℝ)|=(1346596413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346596511/2500000000 : ℝ)|^2193 ≤ (44612431946631/100000000000000 : ℝ)^1681
        have hw : |(1346596511/2500000000 : ℝ)|=(1346596511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_1 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643020857/5000000000 : ℝ)*x 0 + (-1950535459/10000000000 : ℝ)*x 1 + (673298229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643020857/5000000000 : ℝ)^2193 ≤ (43531289467571/100000000000000 : ℝ)^1681 := by
    have hnat : (2643020857 : ℕ)^2193*100000000000000^1681 ≤ 43531289467571^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643020857 5000000000 43531289467571 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1950535459/10000000000 : ℝ)^2193 ≤ (5928140430361/50000000000000 : ℝ)^1681 := by
    have hnat : (1950535459 : ℕ)^2193*50000000000000^1681 ≤ 5928140430361^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950535459 10000000000 5928140430361 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673298229/1250000000 : ℝ)^2193 ≤ (44612429655947/100000000000000 : ℝ)^1681 := by
    have hnat : (673298229 : ℕ)^2193*100000000000000^1681 ≤ 44612429655947^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673298229 1250000000 44612429655947 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643020857/5000000000 : ℝ), (-1950535459/10000000000 : ℝ), (673298229/1250000000 : ℝ)] ![(43531289467571/100000000000000 : ℝ), (5928140430361/50000000000000 : ℝ), (44612429655947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643020857/5000000000 : ℝ)|^2193 ≤ (43531289467571/100000000000000 : ℝ)^1681
        have hw : |(2643020857/5000000000 : ℝ)|=(2643020857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1950535459/10000000000 : ℝ)|^2193 ≤ (5928140430361/50000000000000 : ℝ)^1681
        have hw : |(-1950535459/10000000000 : ℝ)|=(1950535459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673298229/1250000000 : ℝ)|^2193 ≤ (44612429655947/100000000000000 : ℝ)^1681
        have hw : |(673298229/1250000000 : ℝ)|=(673298229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_2 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660755237/1250000000 : ℝ)*x 0 + (5386385763/10000000000 : ℝ)*x 1 + (-975267653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660755237/1250000000 : ℝ)^2193 ≤ (4353129142287/10000000000000 : ℝ)^1681 := by
    have hnat : (660755237 : ℕ)^2193*10000000000000^1681 ≤ 4353129142287^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660755237 1250000000 4353129142287 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386385763/10000000000 : ℝ)^2193 ≤ (22306214455197/50000000000000 : ℝ)^1681 := by
    have hnat : (5386385763 : ℕ)^2193*50000000000000^1681 ≤ 22306214455197^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386385763 10000000000 22306214455197 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975267653/5000000000 : ℝ)^2193 ≤ (5928139823727/50000000000000 : ℝ)^1681 := by
    have hnat : (975267653 : ℕ)^2193*50000000000000^1681 ≤ 5928139823727^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975267653 5000000000 5928139823727 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660755237/1250000000 : ℝ), (5386385763/10000000000 : ℝ), (-975267653/5000000000 : ℝ)] ![(4353129142287/10000000000000 : ℝ), (22306214455197/50000000000000 : ℝ), (5928139823727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660755237/1250000000 : ℝ)|^2193 ≤ (4353129142287/10000000000000 : ℝ)^1681
        have hw : |(660755237/1250000000 : ℝ)|=(660755237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386385763/10000000000 : ℝ)|^2193 ≤ (22306214455197/50000000000000 : ℝ)^1681
        have hw : |(5386385763/10000000000 : ℝ)|=(5386385763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-975267653/5000000000 : ℝ)|^2193 ≤ (5928139823727/50000000000000 : ℝ)^1681
        have hw : |(-975267653/5000000000 : ℝ)|=(975267653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_3 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4451485877/10000000000 : ℝ)*x 0 + (529457483/1250000000 : ℝ)*x 1 + (529457471/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4451485877/10000000000 : ℝ)^2193 ≤ (34789360005689/100000000000000 : ℝ)^1681 := by
    have hnat : (4451485877 : ℕ)^2193*100000000000000^1681 ≤ 34789360005689^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4451485877 10000000000 34789360005689 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529457483/1250000000 : ℝ)^2193 ≤ (32605320472517/100000000000000 : ℝ)^1681 := by
    have hnat : (529457483 : ℕ)^2193*100000000000000^1681 ≤ 32605320472517^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529457483 1250000000 32605320472517 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529457471/1250000000 : ℝ)^2193 ≤ (6521063901689/20000000000000 : ℝ)^1681 := by
    have hnat : (529457471 : ℕ)^2193*20000000000000^1681 ≤ 6521063901689^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529457471 1250000000 6521063901689 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4451485877/10000000000 : ℝ), (529457483/1250000000 : ℝ), (529457471/1250000000 : ℝ)] ![(34789360005689/100000000000000 : ℝ), (32605320472517/100000000000000 : ℝ), (6521063901689/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4451485877/10000000000 : ℝ)|^2193 ≤ (34789360005689/100000000000000 : ℝ)^1681
        have hw : |(4451485877/10000000000 : ℝ)|=(4451485877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529457483/1250000000 : ℝ)|^2193 ≤ (32605320472517/100000000000000 : ℝ)^1681
        have hw : |(529457483/1250000000 : ℝ)|=(529457483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529457471/1250000000 : ℝ)|^2193 ≤ (6521063901689/20000000000000 : ℝ)^1681
        have hw : |(529457471/1250000000 : ℝ)|=(529457471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_4 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137185809/10000000000 : ℝ)*x 0 + (5266479969/10000000000 : ℝ)*x 1 + (5266480127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137185809/10000000000 : ℝ)^2193 ≤ (13357501675631/100000000000000 : ℝ)^1681 := by
    have hnat : (2137185809 : ℕ)^2193*100000000000000^1681 ≤ 13357501675631^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137185809 10000000000 13357501675631 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266479969/10000000000 : ℝ)^2193 ≤ (4332124830091/10000000000000 : ℝ)^1681 := by
    have hnat : (5266479969 : ℕ)^2193*10000000000000^1681 ≤ 4332124830091^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266479969 10000000000 4332124830091 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266480127/10000000000 : ℝ)^2193 ≤ (10830312499113/25000000000000 : ℝ)^1681 := by
    have hnat : (5266480127 : ℕ)^2193*25000000000000^1681 ≤ 10830312499113^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266480127 10000000000 10830312499113 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137185809/10000000000 : ℝ), (5266479969/10000000000 : ℝ), (5266480127/10000000000 : ℝ)] ![(13357501675631/100000000000000 : ℝ), (4332124830091/10000000000000 : ℝ), (10830312499113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137185809/10000000000 : ℝ)|^2193 ≤ (13357501675631/100000000000000 : ℝ)^1681
        have hw : |(-2137185809/10000000000 : ℝ)|=(2137185809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266479969/10000000000 : ℝ)|^2193 ≤ (4332124830091/10000000000000 : ℝ)^1681
        have hw : |(5266479969/10000000000 : ℝ)|=(5266479969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266480127/10000000000 : ℝ)|^2193 ≤ (10830312499113/25000000000000 : ℝ)^1681
        have hw : |(5266480127/10000000000 : ℝ)|=(5266480127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_5 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (671246061/1250000000 : ℝ)*x 0 + (-249899897/1250000000 : ℝ)*x 1 + (1316619893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671246061/1250000000 : ℝ)^2193 ≤ (355480966303/800000000000 : ℝ)^1681 := by
    have hnat : (671246061 : ℕ)^2193*800000000000^1681 ≤ 355480966303^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671246061 1250000000 355480966303 800000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249899897/1250000000 : ℝ)^2193 ≤ (12243635160987/100000000000000 : ℝ)^1681 := by
    have hnat : (249899897 : ℕ)^2193*100000000000000^1681 ≤ 12243635160987^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249899897 1250000000 12243635160987 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316619893/2500000000 : ℝ)^2193 ≤ (2707577752537/6250000000000 : ℝ)^1681 := by
    have hnat : (1316619893 : ℕ)^2193*6250000000000^1681 ≤ 2707577752537^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316619893 2500000000 2707577752537 6250000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671246061/1250000000 : ℝ), (-249899897/1250000000 : ℝ), (1316619893/2500000000 : ℝ)] ![(355480966303/800000000000 : ℝ), (12243635160987/100000000000000 : ℝ), (2707577752537/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671246061/1250000000 : ℝ)|^2193 ≤ (355480966303/800000000000 : ℝ)^1681
        have hw : |(671246061/1250000000 : ℝ)|=(671246061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-249899897/1250000000 : ℝ)|^2193 ≤ (12243635160987/100000000000000 : ℝ)^1681
        have hw : |(-249899897/1250000000 : ℝ)|=(249899897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316619893/2500000000 : ℝ)|^2193 ≤ (2707577752537/6250000000000 : ℝ)^1681
        have hw : |(1316619893/2500000000 : ℝ)|=(1316619893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_6 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369967851/10000000000 : ℝ)*x 0 + (658310093/1250000000 : ℝ)*x 1 + (-999599231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369967851/10000000000 : ℝ)^2193 ≤ (22217556955707/50000000000000 : ℝ)^1681 := by
    have hnat : (5369967851 : ℕ)^2193*50000000000000^1681 ≤ 22217556955707^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369967851 10000000000 22217556955707 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658310093/1250000000 : ℝ)^2193 ≤ (866425132353/2000000000000 : ℝ)^1681 := by
    have hnat : (658310093 : ℕ)^2193*2000000000000^1681 ≤ 866425132353^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658310093 1250000000 866425132353 2000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999599231/5000000000 : ℝ)^2193 ≤ (1224362945641/10000000000000 : ℝ)^1681 := by
    have hnat : (999599231 : ℕ)^2193*10000000000000^1681 ≤ 1224362945641^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999599231 5000000000 1224362945641 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369967851/10000000000 : ℝ), (658310093/1250000000 : ℝ), (-999599231/5000000000 : ℝ)] ![(22217556955707/50000000000000 : ℝ), (866425132353/2000000000000 : ℝ), (1224362945641/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369967851/10000000000 : ℝ)|^2193 ≤ (22217556955707/50000000000000 : ℝ)^1681
        have hw : |(5369967851/10000000000 : ℝ)|=(5369967851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658310093/1250000000 : ℝ)|^2193 ≤ (866425132353/2000000000000 : ℝ)^1681
        have hw : |(658310093/1250000000 : ℝ)|=(658310093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-999599231/5000000000 : ℝ)|^2193 ≤ (1224362945641/10000000000000 : ℝ)^1681
        have hw : |(-999599231/5000000000 : ℝ)|=(999599231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_7 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (51971507/125000000 : ℝ)*x 0 + (547811399/1250000000 : ℝ)*x 1 + (4382491791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51971507/125000000 : ℝ)^2193 ≤ (31824824119871/100000000000000 : ℝ)^1681 := by
    have hnat : (51971507 : ℕ)^2193*100000000000000^1681 ≤ 31824824119871^1681*125000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51971507 125000000 31824824119871 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547811399/1250000000 : ℝ)^2193 ≤ (17043792445543/50000000000000 : ℝ)^1681 := by
    have hnat : (547811399 : ℕ)^2193*50000000000000^1681 ≤ 17043792445543^1681*1250000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547811399 1250000000 17043792445543 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4382491791/10000000000 : ℝ)^2193 ≤ (34087590969257/100000000000000 : ℝ)^1681 := by
    have hnat : (4382491791 : ℕ)^2193*100000000000000^1681 ≤ 34087590969257^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382491791 10000000000 34087590969257 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51971507/125000000 : ℝ), (547811399/1250000000 : ℝ), (4382491791/10000000000 : ℝ)] ![(31824824119871/100000000000000 : ℝ), (17043792445543/50000000000000 : ℝ), (34087590969257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51971507/125000000 : ℝ)|^2193 ≤ (31824824119871/100000000000000 : ℝ)^1681
        have hw : |(51971507/125000000 : ℝ)|=(51971507/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547811399/1250000000 : ℝ)|^2193 ≤ (17043792445543/50000000000000 : ℝ)^1681
        have hw : |(547811399/1250000000 : ℝ)|=(547811399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4382491791/10000000000 : ℝ)|^2193 ≤ (34087590969257/100000000000000 : ℝ)^1681
        have hw : |(4382491791/10000000000 : ℝ)|=(4382491791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_8 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-413768663/2000000000 : ℝ)*x 0 + (1036711077/2000000000 : ℝ)*x 1 + (270018103/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413768663/2000000000 : ℝ)^2193 ≤ (400093521719/3125000000000 : ℝ)^1681 := by
    have hnat : (413768663 : ℕ)^2193*3125000000000^1681 ≤ 400093521719^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413768663 2000000000 400093521719 3125000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036711077/2000000000 : ℝ)^2193 ≤ (8486700652203/20000000000000 : ℝ)^1681 := by
    have hnat : (1036711077 : ℕ)^2193*20000000000000^1681 ≤ 8486700652203^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036711077 2000000000 8486700652203 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270018103/500000000 : ℝ)^2193 ≤ (22381752012259/50000000000000 : ℝ)^1681 := by
    have hnat : (270018103 : ℕ)^2193*50000000000000^1681 ≤ 22381752012259^1681*500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270018103 500000000 22381752012259 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413768663/2000000000 : ℝ), (1036711077/2000000000 : ℝ), (270018103/500000000 : ℝ)] ![(400093521719/3125000000000 : ℝ), (8486700652203/20000000000000 : ℝ), (22381752012259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413768663/2000000000 : ℝ)|^2193 ≤ (400093521719/3125000000000 : ℝ)^1681
        have hw : |(-413768663/2000000000 : ℝ)|=(413768663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036711077/2000000000 : ℝ)|^2193 ≤ (8486700652203/20000000000000 : ℝ)^1681
        have hw : |(1036711077/2000000000 : ℝ)|=(1036711077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270018103/500000000 : ℝ)|^2193 ≤ (22381752012259/50000000000000 : ℝ)^1681
        have hw : |(270018103/500000000 : ℝ)|=(270018103/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_9 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (329765943/625000000 : ℝ)*x 0 + (-1944736623/10000000000 : ℝ)*x 1 + (5400362131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329765943/625000000 : ℝ)^2193 ≤ (10856544364687/25000000000000 : ℝ)^1681 := by
    have hnat : (329765943 : ℕ)^2193*25000000000000^1681 ≤ 10856544364687^1681*625000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329765943 625000000 10856544364687 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944736623/10000000000 : ℝ)^2193 ≤ (2952579433463/25000000000000 : ℝ)^1681 := by
    have hnat : (1944736623 : ℕ)^2193*25000000000000^1681 ≤ 2952579433463^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944736623 10000000000 2952579433463 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400362131/10000000000 : ℝ)^2193 ≤ (44763504792287/100000000000000 : ℝ)^1681 := by
    have hnat : (5400362131 : ℕ)^2193*100000000000000^1681 ≤ 44763504792287^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400362131 10000000000 44763504792287 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329765943/625000000 : ℝ), (-1944736623/10000000000 : ℝ), (5400362131/10000000000 : ℝ)] ![(10856544364687/25000000000000 : ℝ), (2952579433463/25000000000000 : ℝ), (44763504792287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329765943/625000000 : ℝ)|^2193 ≤ (10856544364687/25000000000000 : ℝ)^1681
        have hw : |(329765943/625000000 : ℝ)|=(329765943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1944736623/10000000000 : ℝ)|^2193 ≤ (2952579433463/25000000000000 : ℝ)^1681
        have hw : |(-1944736623/10000000000 : ℝ)|=(1944736623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400362131/10000000000 : ℝ)|^2193 ≤ (44763504792287/100000000000000 : ℝ)^1681
        have hw : |(5400362131/10000000000 : ℝ)|=(5400362131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_10 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1319063779/2500000000 : ℝ)*x 0 + (5400362129/10000000000 : ℝ)*x 1 + (-1944736587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319063779/2500000000 : ℝ)^2193 ≤ (43426177759393/100000000000000 : ℝ)^1681 := by
    have hnat : (1319063779 : ℕ)^2193*100000000000000^1681 ≤ 43426177759393^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319063779 2500000000 43426177759393 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400362129/10000000000 : ℝ)^2193 ≤ (44763504770659/100000000000000 : ℝ)^1681 := by
    have hnat : (5400362129 : ℕ)^2193*100000000000000^1681 ≤ 44763504770659^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400362129 10000000000 44763504770659 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1944736587/10000000000 : ℝ)^2193 ≤ (2952579362159/25000000000000 : ℝ)^1681 := by
    have hnat : (1944736587 : ℕ)^2193*25000000000000^1681 ≤ 2952579362159^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944736587 10000000000 2952579362159 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319063779/2500000000 : ℝ), (5400362129/10000000000 : ℝ), (-1944736587/10000000000 : ℝ)] ![(43426177759393/100000000000000 : ℝ), (44763504770659/100000000000000 : ℝ), (2952579362159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319063779/2500000000 : ℝ)|^2193 ≤ (43426177759393/100000000000000 : ℝ)^1681
        have hw : |(1319063779/2500000000 : ℝ)|=(1319063779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400362129/10000000000 : ℝ)|^2193 ≤ (44763504770659/100000000000000 : ℝ)^1681
        have hw : |(5400362129/10000000000 : ℝ)|=(5400362129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1944736587/10000000000 : ℝ)|^2193 ≤ (2952579362159/25000000000000 : ℝ)^1681
        have hw : |(-1944736587/10000000000 : ℝ)|=(1944736587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_11 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1121292547/2500000000 : ℝ)*x 0 + (210926531/500000000 : ℝ)*x 1 + (2109265237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1121292547/2500000000 : ℝ)^2193 ≤ (35133186497041/100000000000000 : ℝ)^1681 := by
    have hnat : (1121292547 : ℕ)^2193*100000000000000^1681 ≤ 35133186497041^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121292547 2500000000 35133186497041 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210926531/500000000 : ℝ)^2193 ≤ (32433407477463/100000000000000 : ℝ)^1681 := by
    have hnat : (210926531 : ℕ)^2193*100000000000000^1681 ≤ 32433407477463^1681*500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210926531 500000000 32433407477463 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109265237/5000000000 : ℝ)^2193 ≤ (16216703006539/50000000000000 : ℝ)^1681 := by
    have hnat : (2109265237 : ℕ)^2193*50000000000000^1681 ≤ 16216703006539^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109265237 5000000000 16216703006539 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1121292547/2500000000 : ℝ), (210926531/500000000 : ℝ), (2109265237/5000000000 : ℝ)] ![(35133186497041/100000000000000 : ℝ), (32433407477463/100000000000000 : ℝ), (16216703006539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1121292547/2500000000 : ℝ)|^2193 ≤ (35133186497041/100000000000000 : ℝ)^1681
        have hw : |(1121292547/2500000000 : ℝ)|=(1121292547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210926531/500000000 : ℝ)|^2193 ≤ (32433407477463/100000000000000 : ℝ)^1681
        have hw : |(210926531/500000000 : ℝ)|=(210926531/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2109265237/5000000000 : ℝ)|^2193 ≤ (16216703006539/50000000000000 : ℝ)^1681
        have hw : |(2109265237/5000000000 : ℝ)|=(2109265237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_12 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-188121649/1000000000 : ℝ)*x 0 + (2733640699/5000000000 : ℝ)*x 1 + (5255354971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188121649/1000000000 : ℝ)^2193 ≤ (2261918199913/20000000000000 : ℝ)^1681 := by
    have hnat : (188121649 : ℕ)^2193*20000000000000^1681 ≤ 2261918199913^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188121649 1000000000 2261918199913 20000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733640699/5000000000 : ℝ)^2193 ≤ (22744253852053/50000000000000 : ℝ)^1681 := by
    have hnat : (2733640699 : ℕ)^2193*50000000000000^1681 ≤ 22744253852053^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733640699 5000000000 22744253852053 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255354971/10000000000 : ℝ)^2193 ≤ (43201901280299/100000000000000 : ℝ)^1681 := by
    have hnat : (5255354971 : ℕ)^2193*100000000000000^1681 ≤ 43201901280299^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255354971 10000000000 43201901280299 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-188121649/1000000000 : ℝ), (2733640699/5000000000 : ℝ), (5255354971/10000000000 : ℝ)] ![(2261918199913/20000000000000 : ℝ), (22744253852053/50000000000000 : ℝ), (43201901280299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-188121649/1000000000 : ℝ)|^2193 ≤ (2261918199913/20000000000000 : ℝ)^1681
        have hw : |(-188121649/1000000000 : ℝ)|=(188121649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733640699/5000000000 : ℝ)|^2193 ≤ (22744253852053/50000000000000 : ℝ)^1681
        have hw : |(2733640699/5000000000 : ℝ)|=(2733640699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255354971/10000000000 : ℝ)|^2193 ≤ (43201901280299/100000000000000 : ℝ)^1681
        have hw : |(5255354971/10000000000 : ℝ)|=(5255354971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_13 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1344438141/2500000000 : ℝ)*x 0 + (-2003614333/10000000000 : ℝ)*x 1 + (1051071131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344438141/2500000000 : ℝ)^2193 ≤ (22259584496451/50000000000000 : ℝ)^1681 := by
    have hnat : (1344438141 : ℕ)^2193*50000000000000^1681 ≤ 22259584496451^1681*2500000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344438141 2500000000 22259584496451 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003614333/10000000000 : ℝ)^2193 ≤ (1227892237337/10000000000000 : ℝ)^1681 := by
    have hnat : (2003614333 : ℕ)^2193*10000000000000^1681 ≤ 1227892237337^1681*10000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003614333 10000000000 1227892237337 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051071131/2000000000 : ℝ)^2193 ≤ (43201908615767/100000000000000 : ℝ)^1681 := by
    have hnat : (1051071131 : ℕ)^2193*100000000000000^1681 ≤ 43201908615767^1681*2000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051071131 2000000000 43201908615767 100000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344438141/2500000000 : ℝ), (-2003614333/10000000000 : ℝ), (1051071131/2000000000 : ℝ)] ![(22259584496451/50000000000000 : ℝ), (1227892237337/10000000000000 : ℝ), (43201908615767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344438141/2500000000 : ℝ)|^2193 ≤ (22259584496451/50000000000000 : ℝ)^1681
        have hw : |(1344438141/2500000000 : ℝ)|=(1344438141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2003614333/10000000000 : ℝ)|^2193 ≤ (1227892237337/10000000000000 : ℝ)^1681
        have hw : |(-2003614333/10000000000 : ℝ)|=(2003614333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051071131/2000000000 : ℝ)|^2193 ≤ (43201908615767/100000000000000 : ℝ)^1681
        have hw : |(1051071131/2000000000 : ℝ)|=(1051071131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_14 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (537775263/1000000000 : ℝ)*x 0 + (2627677883/5000000000 : ℝ)*x 1 + (-1001807047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537775263/1000000000 : ℝ)^2193 ≤ (11129792426423/25000000000000 : ℝ)^1681 := by
    have hnat : (537775263 : ℕ)^2193*25000000000000^1681 ≤ 11129792426423^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537775263 1000000000 11129792426423 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627677883/5000000000 : ℝ)^2193 ≤ (10800477451543/25000000000000 : ℝ)^1681 := by
    have hnat : (2627677883 : ℕ)^2193*25000000000000^1681 ≤ 10800477451543^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627677883 5000000000 10800477451543 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001807047/5000000000 : ℝ)^2193 ≤ (3069730115643/25000000000000 : ℝ)^1681 := by
    have hnat : (1001807047 : ℕ)^2193*25000000000000^1681 ≤ 3069730115643^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001807047 5000000000 3069730115643 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537775263/1000000000 : ℝ), (2627677883/5000000000 : ℝ), (-1001807047/5000000000 : ℝ)] ![(11129792426423/25000000000000 : ℝ), (10800477451543/25000000000000 : ℝ), (3069730115643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537775263/1000000000 : ℝ)|^2193 ≤ (11129792426423/25000000000000 : ℝ)^1681
        have hw : |(537775263/1000000000 : ℝ)|=(537775263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627677883/5000000000 : ℝ)|^2193 ≤ (10800477451543/25000000000000 : ℝ)^1681
        have hw : |(2627677883/5000000000 : ℝ)|=(2627677883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1001807047/5000000000 : ℝ)|^2193 ≤ (3069730115643/25000000000000 : ℝ)^1681
        have hw : |(-1001807047/5000000000 : ℝ)|=(1001807047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1426_box_15 (p : ℝ) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165200623/400000000 : ℝ)*x 0 + (2198051569/5000000000 : ℝ)*x 1 + (439610351/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165200623/400000000 : ℝ)^2193 ≤ (7887112411441/25000000000000 : ℝ)^1681 := by
    have hnat : (165200623 : ℕ)^2193*25000000000000^1681 ≤ 7887112411441^1681*400000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165200623 400000000 7887112411441 25000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198051569/5000000000 : ℝ)^2193 ≤ (17112886638843/50000000000000 : ℝ)^1681 := by
    have hnat : (2198051569 : ℕ)^2193*50000000000000^1681 ≤ 17112886638843^1681*5000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198051569 5000000000 17112886638843 50000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439610351/1000000000 : ℝ)^2193 ≤ (3422577705601/10000000000000 : ℝ)^1681 := by
    have hnat : (439610351 : ℕ)^2193*10000000000000^1681 ≤ 3422577705601^1681*1000000000^2193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439610351 1000000000 3422577705601 10000000000000 2193 1681 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2193/512 : ℝ)) 2193 1681 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165200623/400000000 : ℝ), (2198051569/5000000000 : ℝ), (439610351/1000000000 : ℝ)] ![(7887112411441/25000000000000 : ℝ), (17112886638843/50000000000000 : ℝ), (3422577705601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165200623/400000000 : ℝ)|^2193 ≤ (7887112411441/25000000000000 : ℝ)^1681
        have hw : |(165200623/400000000 : ℝ)|=(165200623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2198051569/5000000000 : ℝ)|^2193 ≤ (17112886638843/50000000000000 : ℝ)^1681
        have hw : |(2198051569/5000000000 : ℝ)|=(2198051569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(439610351/1000000000 : ℝ)|^2193 ≤ (3422577705601/10000000000000 : ℝ)^1681
        have hw : |(439610351/1000000000 : ℝ)|=(439610351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1426_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31449/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59107/100000 : ℝ) ∧ (5027/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42337/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5667/50000 : ℝ) ^ (4385/1024 : ℝ) ≤ (8925954252607789/100000000000000000000 : ℝ) := by
    have hpowers : (5667/50000 : ℝ)^4385 ≤ (8925954252607789/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5667 : ℕ)^4385*100000000000000000000^1024 ≤ 8925954252607789^1024*50000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5667 50000 8925954252607789 100000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5667/50000 : ℝ)) (X := (8925954252607789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (4385/1024 : ℝ) ≤ (13809546945710969/50000000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^4385 ≤ (13809546945710969/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2951 : ℕ)^4385*50000000000000000000^1024 ≤ 13809546945710969^1024*20000^4385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 13809546945710969 50000000000000000000 4385 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (13809546945710969/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008925954252607789/50000000000000000000 : ℝ) ≤ (5000208427637217/5000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (50008925954252607789/50000000000000000000 : ℝ)^1024 ≤ (5000208427637217/5000000000000000 : ℝ)^4385 := by
      have hnat : (50008925954252607789 : ℕ)^1024*5000000000000000^4385 ≤ 5000208427637217^4385*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008925954252607789 50000000000000000000 5000208427637217 5000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000208427637217/5000000000000000 : ℝ)) (X := (50008925954252607789/50000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036545048144029727/100000000000000000000 : ℝ) ≤ (2500213323200027/2500000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (100036545048144029727/100000000000000000000 : ℝ)^1024 ≤ (2500213323200027/2500000000000000 : ℝ)^4385 := by
      have hnat : (100036545048144029727 : ℕ)^1024*2500000000000000^4385 ≤ 2500213323200027^4385*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036545048144029727 100000000000000000000 2500213323200027 2500000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500213323200027/2500000000000000 : ℝ)) (X := (100036545048144029727/100000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013809546945710969/25000000000000000000 : ℝ) ≤ (5000644865162891/5000000000000000 : ℝ) ^ (4385/1024 : ℝ) := by
    have hpowers : (25013809546945710969/25000000000000000000 : ℝ)^1024 ≤ (5000644865162891/5000000000000000 : ℝ)^4385 := by
      have hnat : (25013809546945710969 : ℕ)^1024*5000000000000000^4385 ≤ 5000644865162891^4385*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013809546945710969 25000000000000000000 5000644865162891 5000000000000000 1024 4385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000644865162891/5000000000000000 : ℝ)) (X := (25013809546945710969/25000000000000000000 : ℝ)) (by norm_num) 4385 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8925954252607789/100000000000000000000 : ℝ) ≤ ((17100766448030930241/17105000000000000000 : ℝ)+2*(218218762837/171050000000000 : ℝ)*(5667/50000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (17100766448030930241/17105000000000000000 : ℝ)+2*(218218762837/171050000000000 : ℝ)*(5667/50000 : ℝ)=(5000208427637217/5000000000000000 : ℝ) by norm_num, show 1+2*(8925954252607789/100000000000000000000 : ℝ)=(50008925954252607789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13809546945710969/50000000000000000000 : ℝ)+(8925954252607789/100000000000000000000 : ℝ) ≤ ((17100766448030930241/17105000000000000000 : ℝ)+(218218762837/171050000000000 : ℝ)*((2951/20000 : ℝ)+(5667/50000 : ℝ)))^(4385/1024 : ℝ) := by
    rw [show (17100766448030930241/17105000000000000000 : ℝ)+(218218762837/171050000000000 : ℝ)*((2951/20000 : ℝ)+(5667/50000 : ℝ))=(2500213323200027/2500000000000000 : ℝ) by norm_num, show 1+(13809546945710969/50000000000000000000 : ℝ)+(8925954252607789/100000000000000000000 : ℝ)=(100036545048144029727/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13809546945710969/50000000000000000000 : ℝ) ≤ ((17100766448030930241/17105000000000000000 : ℝ)+2*(218218762837/171050000000000 : ℝ)*(2951/20000 : ℝ))^(4385/1024 : ℝ) := by
    rw [show (17100766448030930241/17105000000000000000 : ℝ)+2*(218218762837/171050000000000 : ℝ)*(2951/20000 : ℝ)=(5000644865162891/5000000000000000 : ℝ) by norm_num, show 1+2*(13809546945710969/50000000000000000000 : ℝ)=(25013809546945710969/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17100766448030930241/17105000000000000000 : ℝ)*(X 1 0+X 2 0)+(218218762837/171050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (17100766448030930241/17105000000000000000 : ℝ)) (alpha := (218218762837/171050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17100766448030930241/17105000000000000000 : ℝ)*(X 0 1+X 2 1)+(218218762837/171050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (17100766448030930241/17105000000000000000 : ℝ)) (alpha := (218218762837/171050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17100766448030930241/17105000000000000000 : ℝ)*(X 0 2+X 1 2)+(218218762837/171050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4385/1024 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (17100766448030930241/17105000000000000000 : ℝ)) (alpha := (218218762837/171050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1812688919/10000000000 : ℝ)*X 0 0+(1346596413/2500000000 : ℝ)*X 0 1+(1346596511/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2643020857/5000000000 : ℝ)*X 1 0+(-1950535459/10000000000 : ℝ)*X 1 1+(673298229/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660755237/1250000000 : ℝ)*X 2 0+(5386385763/10000000000 : ℝ)*X 2 1+(-975267653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4451485877/10000000000 : ℝ)*X 0 0+(529457483/1250000000 : ℝ)*X 0 1+(529457471/1250000000 : ℝ)*X 0 2+(4451485877/10000000000 : ℝ)*X 1 0+(529457483/1250000000 : ℝ)*X 1 1+(529457471/1250000000 : ℝ)*X 1 2+(4451485877/10000000000 : ℝ)*X 2 0+(529457483/1250000000 : ℝ)*X 2 1+(529457471/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2137185809/10000000000 : ℝ)*X 0 0+(5266479969/10000000000 : ℝ)*X 0 1+(5266480127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((671246061/1250000000 : ℝ)*X 1 0+(-249899897/1250000000 : ℝ)*X 1 1+(1316619893/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5369967851/10000000000 : ℝ)*X 2 0+(658310093/1250000000 : ℝ)*X 2 1+(-999599231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((51971507/125000000 : ℝ)*X 0 0+(547811399/1250000000 : ℝ)*X 0 1+(4382491791/10000000000 : ℝ)*X 0 2+(51971507/125000000 : ℝ)*X 1 0+(547811399/1250000000 : ℝ)*X 1 1+(4382491791/10000000000 : ℝ)*X 1 2+(51971507/125000000 : ℝ)*X 2 0+(547811399/1250000000 : ℝ)*X 2 1+(4382491791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-413768663/2000000000 : ℝ)*X 0 0+(1036711077/2000000000 : ℝ)*X 0 1+(270018103/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((329765943/625000000 : ℝ)*X 1 0+(-1944736623/10000000000 : ℝ)*X 1 1+(5400362131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1319063779/2500000000 : ℝ)*X 2 0+(5400362129/10000000000 : ℝ)*X 2 1+(-1944736587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1121292547/2500000000 : ℝ)*X 0 0+(210926531/500000000 : ℝ)*X 0 1+(2109265237/5000000000 : ℝ)*X 0 2+(1121292547/2500000000 : ℝ)*X 1 0+(210926531/500000000 : ℝ)*X 1 1+(2109265237/5000000000 : ℝ)*X 1 2+(1121292547/2500000000 : ℝ)*X 2 0+(210926531/500000000 : ℝ)*X 2 1+(2109265237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-188121649/1000000000 : ℝ)*X 0 0+(2733640699/5000000000 : ℝ)*X 0 1+(5255354971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1344438141/2500000000 : ℝ)*X 1 0+(-2003614333/10000000000 : ℝ)*X 1 1+(1051071131/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((537775263/1000000000 : ℝ)*X 2 0+(2627677883/5000000000 : ℝ)*X 2 1+(-1001807047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((165200623/400000000 : ℝ)*X 0 0+(2198051569/5000000000 : ℝ)*X 0 1+(439610351/1000000000 : ℝ)*X 0 2+(165200623/400000000 : ℝ)*X 1 0+(2198051569/5000000000 : ℝ)*X 1 1+(439610351/1000000000 : ℝ)*X 1 2+(165200623/400000000 : ℝ)*X 2 0+(2198051569/5000000000 : ℝ)*X 2 1+(439610351/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1426_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31449/50000 : ℝ) ≤ (-16809709047641536010270328965019/26726562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (69050173/100000000000000 : ℝ)*(lower1) + (87296663/100000000000000 : ℝ)*(lower2) + (77549449/50000000000000 : ℝ)*(lower3) + (323329/1250000000000 : ℝ)*(lower4) + (602692376036899/20000000000000 : ℝ)*(major0) + (602692376036899/20000000000000 : ℝ)*(major1) + (188341367511531/6250000000000 : ℝ)*(major2) + (11991744973/100000000000000 : ℝ)*(sp1) + (2070605894822291/50000000000000 : ℝ)*(sp4) + (4141199797899609/100000000000000 : ℝ)*(sp5) + (2070461650081159/50000000000000 : ℝ)*(sp6) + (1906642766372357/100000000000000 : ℝ)*(sp7) + (288489482263/100000000000000 : ℝ)*(sp14) + (34251200901/100000000000000 : ℝ)*(sp15) + (953338508786629/50000000000000 : ℝ)*(f.failure) + (2070605894822291/50000000000000 : ℝ)*(f.sum) + (39737017289009/8552500000000000000000000000 : ℝ)*base66 + (2692280920349997341/342100000000000000000000000000000 : ℝ)*base68 + (277601437443858971/106906250000000000000000000000000 : ℝ)*base69 + (3976193533254897341/342100000000000000000000000000000 : ℝ)*base72 + (1954082161989/2138125000000000000000000000 : ℝ)*base73 + (562668239151046471/106906250000000000000000000000000 : ℝ)*base75 + (96276735200962659/342100000000000000000000000000000 : ℝ)*base77 + (1305649282420062659/342100000000000000000000000000000 : ℝ)*base79 + (19972271764887/3421000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (952309/2500000000000000000000 : ℝ)*base89 + (952309/2500000000000000000000 : ℝ)*base91 + (24047691/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59107/100000 : ℝ) ≤ (252767453225835351320320391022771/427625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7771649/25000000000000 : ℝ)*(lower3) + (81304001/100000000000000 : ℝ)*(upper4) + (5764529/50000000000000 : ℝ)*(upper5) + (3084973691781851/100000000000000 : ℝ)*(major0) + (3084973691781851/100000000000000 : ℝ)*(major1) + (771243422945463/25000000000000 : ℝ)*(major2) + (262394760399159/6250000000000 : ℝ)*(sp0) + (4198316828735149/100000000000000 : ℝ)*(sp1) + (2099160018557973/50000000000000 : ℝ)*(sp2) + (7807693267867/400000000000 : ℝ)*(sp3) + (93618729/50000000000000 : ℝ)*(sp6) + (16004981/2500000000000 : ℝ)*(sp7) + (679123651/20000000000000 : ℝ)*(sp9) + (202898343/5000000000000 : ℝ)*(sp12) + (195192395716599/10000000000000 : ℝ)*(f.failure) + (1049580056088351/25000000000000 : ℝ)*(f.sum) + (72485695698059/17105000000000000000000000000 : ℝ)*base66 + (23809813604820743909/1710500000000000000000000000000000 : ℝ)*base68 + (951030694236878417/427625000000000000000000000000000 : ℝ)*base70 + (18463556785664743909/1710500000000000000000000000000000 : ℝ)*base72 + (32031361940891/17105000000000000000000000000 : ℝ)*base73 + (1089178105076503417/427625000000000000000000000000000 : ℝ)*base76 + (17129293488802443909/1710500000000000000000000000000000 : ℝ)*base78 + (19660151180615443909/1710500000000000000000000000000000 : ℝ)*base80 + (12745918720467/8552500000000000000000000000 : ℝ)*base81 + (2764679/500000000000000000000 : ℝ)*base89 + (2764679/500000000000000000000 : ℝ)*base91 + (2235321/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5027/6250 : ℝ) ≤ (171978824270846918865373352244747/213812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4344803/25000000000000 : ℝ)*(upper0) + (4710141/12500000000000 : ℝ)*(upper1) + (22306163/100000000000000 : ℝ)*(upper4) + (848256984052537/25000000000000 : ℝ)*(major0) + (848256984052537/25000000000000 : ℝ)*(major1) + (848256984052537/25000000000000 : ℝ)*(major2) + (19088605839/25000000000000 : ℝ)*(sp1) + (8594924733/10000000000000 : ℝ)*(sp2) + (19154108331/100000000000000 : ℝ)*(sp3) + (338787281/12500000000000 : ℝ)*(sp4) + (4612405712828791/100000000000000 : ℝ)*(sp8) + (4612332068703683/100000000000000 : ℝ)*(sp9) + (4612322473879709/100000000000000 : ℝ)*(sp10) + (85872672998731/4000000000000 : ℝ)*(sp11) + (1073417989538303/50000000000000 : ℝ)*(f.failure) + (4612408423127039/100000000000000 : ℝ)*(f.sum) + (20847426260099/8552500000000000000000000000 : ℝ)*base66 + (4685029865454096417/427625000000000000000000000000000 : ℝ)*base67 + (2759932595323721417/427625000000000000000000000000000 : ℝ)*base69 + (671513972276096417/427625000000000000000000000000000 : ℝ)*base71 + (303267457452797/17105000000000000000000000000 : ℝ)*base73 + (4600972093012596417/427625000000000000000000000000000 : ℝ)*base75 + (2467103805681596417/427625000000000000000000000000000 : ℝ)*base77 + (15468013567818596417/427625000000000000000000000000000 : ℝ)*base79 + (74391459318277/17105000000000000000000000000 : ℝ)*base81 + (17253937/2500000000000000000000 : ℝ)*base90 + (17253937/2500000000000000000000 : ℝ)*base92 + (17253937/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42337/50000 : ℝ) ≤ (-263327024186923157817830487/311000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2178987/50000000000000 : ℝ)*(lower0) + (31143073/100000000000000 : ℝ)*(lower2) + (29868437/100000000000000 : ℝ)*(upper3) + (227747979/100000000000000 : ℝ)*(upper5) + (68609546643451/2000000000000 : ℝ)*(major0) + (68609546643451/2000000000000 : ℝ)*(major1) + (68609546643451/2000000000000 : ℝ)*(major2) + (6138286047/100000000000000 : ℝ)*(sp0) + (3777518841/4000000000000 : ℝ)*(sp7) + (14651450899/100000000000000 : ℝ)*(sp8) + (1179656652647507/25000000000000 : ℝ)*(sp12) + (2359323700163487/50000000000000 : ℝ)*(sp13) + (2359323700163487/50000000000000 : ℝ)*(sp14) + (2170436515670563/100000000000000 : ℝ)*(sp15) + (542632738410397/25000000000000 : ℝ)*(f.failure) + (2359323700163487/50000000000000 : ℝ)*(f.sum) + (1297923054343/311000000000000000000000000 : ℝ)*base65 + (11099470289802881/3110000000000000000000000000000 : ℝ)*base67 + (11994660362881/3110000000000000000000000000000 : ℝ)*base69 + (7720625245237119/3110000000000000000000000000000 : ℝ)*base72 + (88588855233/77750000000000000000000000 : ℝ)*base74 + (653199426777119/3110000000000000000000000000000 : ℝ)*base76 + (2811739928477119/3110000000000000000000000000000 : ℝ)*base78 + (22916244386892881/3110000000000000000000000000000 : ℝ)*base79 + (619402122199/311000000000000000000000000 : ℝ)*base82 + (3106637/1250000000000000000000 : ℝ)*base89 + (3106637/1250000000000000000000 : ℝ)*base91 + (3106637/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1426_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31449/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59107/100000 : ℝ) else (5027/6250 : ℝ) ≤ X j i ∧ X j i ≤ (42337/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1426_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1426_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31449/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59107/100000 : ℝ) else (5027/6250 : ℝ) ≤ X j i ∧ X j i ≤ (42337/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1426_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1426_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1426_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4385/1024 : ℝ) ≤ p) (hpb : p ≤ (2193/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79023921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31449/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59107/100000 : ℝ) else (5027/6250 : ℝ) ≤ X j i ∧ X j i ≤ (42337/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1426_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1460_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:50.536887+00:00
-- url     : https://prove2.me/submissions/69b27f6c-1bca-47c6-9a6a-d416f6b652f0

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
theorem support_rectangle_w1460_s0_0 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-435349161/2500000000 : ℝ)*x 0 + (5947491957/10000000000 : ℝ)*x 1 + (4838273447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435349161/2500000000 : ℝ)^1105 ≤ (10280273445967/100000000000000 : ℝ)^849 := by
    have hnat : (435349161 : ℕ)^1105*100000000000000^849 ≤ 10280273445967^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435349161 2500000000 10280273445967 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5947491957/10000000000 : ℝ)^1105 ≤ (50849709883259/100000000000000 : ℝ)^849 := by
    have hnat : (5947491957 : ℕ)^1105*100000000000000^849 ≤ 50849709883259^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5947491957 10000000000 50849709883259 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4838273447/10000000000 : ℝ)^1105 ≤ (38870016655889/100000000000000 : ℝ)^849 := by
    have hnat : (4838273447 : ℕ)^1105*100000000000000^849 ≤ 38870016655889^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838273447 10000000000 38870016655889 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435349161/2500000000 : ℝ), (5947491957/10000000000 : ℝ), (4838273447/10000000000 : ℝ)] ![(10280273445967/100000000000000 : ℝ), (50849709883259/100000000000000 : ℝ), (38870016655889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435349161/2500000000 : ℝ)|^1105 ≤ (10280273445967/100000000000000 : ℝ)^849
        have hw : |(-435349161/2500000000 : ℝ)|=(435349161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5947491957/10000000000 : ℝ)|^1105 ≤ (50849709883259/100000000000000 : ℝ)^849
        have hw : |(5947491957/10000000000 : ℝ)|=(5947491957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4838273447/10000000000 : ℝ)|^1105 ≤ (38870016655889/100000000000000 : ℝ)^849
        have hw : |(4838273447/10000000000 : ℝ)|=(4838273447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s0_1 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5488656641/10000000000 : ℝ)*x 0 + (-1183328757/5000000000 : ℝ)*x 1 + (4838273627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5488656641/10000000000 : ℝ)^1105 ≤ (2862773354511/6250000000000 : ℝ)^849 := by
    have hnat : (5488656641 : ℕ)^1105*6250000000000^849 ≤ 2862773354511^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488656641 10000000000 2862773354511 6250000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1183328757/5000000000 : ℝ)^1105 ≤ (1915700972331/12500000000000 : ℝ)^849 := by
    have hnat : (1183328757 : ℕ)^1105*12500000000000^849 ≤ 1915700972331^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183328757 5000000000 1915700972331 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4838273627/10000000000 : ℝ)^1105 ≤ (19435009269013/50000000000000 : ℝ)^849 := by
    have hnat : (4838273627 : ℕ)^1105*50000000000000^849 ≤ 19435009269013^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838273627 10000000000 19435009269013 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5488656641/10000000000 : ℝ), (-1183328757/5000000000 : ℝ), (4838273627/10000000000 : ℝ)] ![(2862773354511/6250000000000 : ℝ), (1915700972331/12500000000000 : ℝ), (19435009269013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5488656641/10000000000 : ℝ)|^1105 ≤ (2862773354511/6250000000000 : ℝ)^849
        have hw : |(5488656641/10000000000 : ℝ)|=(5488656641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1183328757/5000000000 : ℝ)|^1105 ≤ (1915700972331/12500000000000 : ℝ)^849
        have hw : |(-1183328757/5000000000 : ℝ)|=(1183328757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4838273627/10000000000 : ℝ)|^1105 ≤ (19435009269013/50000000000000 : ℝ)^849
        have hw : |(4838273627/10000000000 : ℝ)|=(4838273627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s0_2 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5488657279/10000000000 : ℝ)*x 0 + (4838273653/10000000000 : ℝ)*x 1 + (-118332833/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5488657279/10000000000 : ℝ)^1105 ≤ (45804380601903/100000000000000 : ℝ)^849 := by
    have hnat : (5488657279 : ℕ)^1105*100000000000000^849 ≤ 45804380601903^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488657279 10000000000 45804380601903 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4838273653/10000000000 : ℝ)^1105 ≤ (38870018809891/100000000000000 : ℝ)^849 := by
    have hnat : (4838273653 : ℕ)^1105*100000000000000^849 ≤ 38870018809891^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838273653 10000000000 38870018809891 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118332833/500000000 : ℝ)^1105 ≤ (3831400145233/25000000000000 : ℝ)^849 := by
    have hnat : (118332833 : ℕ)^1105*25000000000000^849 ≤ 3831400145233^849*500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118332833 500000000 3831400145233 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5488657279/10000000000 : ℝ), (4838273653/10000000000 : ℝ), (-118332833/500000000 : ℝ)] ![(45804380601903/100000000000000 : ℝ), (38870018809891/100000000000000 : ℝ), (3831400145233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5488657279/10000000000 : ℝ)|^1105 ≤ (45804380601903/100000000000000 : ℝ)^849
        have hw : |(5488657279/10000000000 : ℝ)|=(5488657279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4838273653/10000000000 : ℝ)|^1105 ≤ (38870018809891/100000000000000 : ℝ)^849
        have hw : |(4838273653/10000000000 : ℝ)|=(4838273653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118332833/500000000 : ℝ)|^1105 ≤ (3831400145233/25000000000000 : ℝ)^849
        have hw : |(-118332833/500000000 : ℝ)|=(118332833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s0_3 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (832317147/2000000000 : ℝ)*x 0 + (3102720021/10000000000 : ℝ)*x 1 + (5529614223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832317147/2000000000 : ℝ)^1105 ≤ (1597436150759/5000000000000 : ℝ)^849 := by
    have hnat : (832317147 : ℕ)^1105*5000000000000^849 ≤ 1597436150759^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832317147 2000000000 1597436150759 5000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102720021/10000000000 : ℝ)^1105 ≤ (2725192136129/12500000000000 : ℝ)^849 := by
    have hnat : (3102720021 : ℕ)^1105*12500000000000^849 ≤ 2725192136129^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102720021 10000000000 2725192136129 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5529614223/10000000000 : ℝ)^1105 ≤ (23124869941497/50000000000000 : ℝ)^849 := by
    have hnat : (5529614223 : ℕ)^1105*50000000000000^849 ≤ 23124869941497^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529614223 10000000000 23124869941497 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(832317147/2000000000 : ℝ), (3102720021/10000000000 : ℝ), (5529614223/10000000000 : ℝ)] ![(1597436150759/5000000000000 : ℝ), (2725192136129/12500000000000 : ℝ), (23124869941497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(832317147/2000000000 : ℝ)|^1105 ≤ (1597436150759/5000000000000 : ℝ)^849
        have hw : |(832317147/2000000000 : ℝ)|=(832317147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102720021/10000000000 : ℝ)|^1105 ≤ (2725192136129/12500000000000 : ℝ)^849
        have hw : |(3102720021/10000000000 : ℝ)|=(3102720021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5529614223/10000000000 : ℝ)|^1105 ≤ (23124869941497/50000000000000 : ℝ)^849
        have hw : |(5529614223/10000000000 : ℝ)|=(5529614223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s0_4 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-174526631/1000000000 : ℝ)*x 0 + (4866583823/10000000000 : ℝ)*x 1 + (5918171811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174526631/1000000000 : ℝ)^1105 ≤ (5155008074441/50000000000000 : ℝ)^849 := by
    have hnat : (174526631 : ℕ)^1105*50000000000000^849 ≤ 5155008074441^849*1000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174526631 1000000000 5155008074441 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4866583823/10000000000 : ℝ)^1105 ≤ (39166299823463/100000000000000 : ℝ)^849 := by
    have hnat : (4866583823 : ℕ)^1105*100000000000000^849 ≤ 39166299823463^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4866583823 10000000000 39166299823463 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5918171811/10000000000 : ℝ)^1105 ≤ (12630921005337/25000000000000 : ℝ)^849 := by
    have hnat : (5918171811 : ℕ)^1105*25000000000000^849 ≤ 12630921005337^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5918171811 10000000000 12630921005337 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174526631/1000000000 : ℝ), (4866583823/10000000000 : ℝ), (5918171811/10000000000 : ℝ)] ![(5155008074441/50000000000000 : ℝ), (39166299823463/100000000000000 : ℝ), (12630921005337/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174526631/1000000000 : ℝ)|^1105 ≤ (5155008074441/50000000000000 : ℝ)^849
        have hw : |(-174526631/1000000000 : ℝ)|=(174526631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4866583823/10000000000 : ℝ)|^1105 ≤ (39166299823463/100000000000000 : ℝ)^849
        have hw : |(4866583823/10000000000 : ℝ)|=(4866583823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5918171811/10000000000 : ℝ)|^1105 ≤ (12630921005337/25000000000000 : ℝ)^849
        have hw : |(5918171811/10000000000 : ℝ)|=(5918171811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s0_5 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5185777133/10000000000 : ℝ)*x 0 + (-643379241/5000000000 : ℝ)*x 1 + (5918171883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185777133/10000000000 : ℝ)^1105 ≤ (21271167447009/50000000000000 : ℝ)^849 := by
    have hnat : (5185777133 : ℕ)^1105*50000000000000^849 ≤ 21271167447009^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185777133 10000000000 21271167447009 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643379241/5000000000 : ℝ)^1105 ≤ (6933980272341/100000000000000 : ℝ)^849 := by
    have hnat : (643379241 : ℕ)^1105*100000000000000^849 ≤ 6933980272341^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643379241 5000000000 6933980272341 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5918171883/10000000000 : ℝ)^1105 ≤ (50523684821357/100000000000000 : ℝ)^849 := by
    have hnat : (5918171883 : ℕ)^1105*100000000000000^849 ≤ 50523684821357^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5918171883 10000000000 50523684821357 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185777133/10000000000 : ℝ), (-643379241/5000000000 : ℝ), (5918171883/10000000000 : ℝ)] ![(21271167447009/50000000000000 : ℝ), (6933980272341/100000000000000 : ℝ), (50523684821357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185777133/10000000000 : ℝ)|^1105 ≤ (21271167447009/50000000000000 : ℝ)^849
        have hw : |(5185777133/10000000000 : ℝ)|=(5185777133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-643379241/5000000000 : ℝ)|^1105 ≤ (6933980272341/100000000000000 : ℝ)^849
        have hw : |(-643379241/5000000000 : ℝ)|=(643379241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5918171883/10000000000 : ℝ)|^1105 ≤ (50523684821357/100000000000000 : ℝ)^849
        have hw : |(5918171883/10000000000 : ℝ)|=(5918171883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s0_6 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5185777169/10000000000 : ℝ)*x 0 + (5918171721/10000000000 : ℝ)*x 1 + (-1286758683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185777169/10000000000 : ℝ)^1105 ≤ (21271167639201/50000000000000 : ℝ)^849 := by
    have hnat : (5185777169 : ℕ)^1105*50000000000000^849 ≤ 21271167639201^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185777169 10000000000 21271167639201 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5918171721/10000000000 : ℝ)^1105 ≤ (25261841510669/50000000000000 : ℝ)^849 := by
    have hnat : (5918171721 : ℕ)^1105*50000000000000^849 ≤ 25261841510669^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5918171721 10000000000 25261841510669 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286758683/10000000000 : ℝ)^1105 ≤ (866747710259/12500000000000 : ℝ)^849 := by
    have hnat : (1286758683 : ℕ)^1105*12500000000000^849 ≤ 866747710259^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286758683 10000000000 866747710259 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185777169/10000000000 : ℝ), (5918171721/10000000000 : ℝ), (-1286758683/10000000000 : ℝ)] ![(21271167639201/50000000000000 : ℝ), (25261841510669/50000000000000 : ℝ), (866747710259/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185777169/10000000000 : ℝ)|^1105 ≤ (21271167639201/50000000000000 : ℝ)^849
        have hw : |(5185777169/10000000000 : ℝ)|=(5185777169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5918171721/10000000000 : ℝ)|^1105 ≤ (25261841510669/50000000000000 : ℝ)^849
        have hw : |(5918171721/10000000000 : ℝ)|=(5918171721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1286758683/10000000000 : ℝ)|^1105 ≤ (866747710259/12500000000000 : ℝ)^849
        have hw : |(-1286758683/10000000000 : ℝ)|=(1286758683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s0_7 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (521256857/1250000000 : ℝ)*x 0 + (54676723/100000000 : ℝ)*x 1 + (63337439/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521256857/1250000000 : ℝ)^1105 ≤ (32033371804233/100000000000000 : ℝ)^849 := by
    have hnat : (521256857 : ℕ)^1105*100000000000000^849 ≤ 32033371804233^849*1250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521256857 1250000000 32033371804233 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54676723/100000000 : ℝ)^1105 ≤ (45576580773259/100000000000000 : ℝ)^849 := by
    have hnat : (54676723 : ℕ)^1105*100000000000000^849 ≤ 45576580773259^849*100000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54676723 100000000 45576580773259 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63337439/200000000 : ℝ)^1105 ≤ (11195023705947/50000000000000 : ℝ)^849 := by
    have hnat : (63337439 : ℕ)^1105*50000000000000^849 ≤ 11195023705947^849*200000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63337439 200000000 11195023705947 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521256857/1250000000 : ℝ), (54676723/100000000 : ℝ), (63337439/200000000 : ℝ)] ![(32033371804233/100000000000000 : ℝ), (45576580773259/100000000000000 : ℝ), (11195023705947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521256857/1250000000 : ℝ)|^1105 ≤ (32033371804233/100000000000000 : ℝ)^849
        have hw : |(521256857/1250000000 : ℝ)|=(521256857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54676723/100000000 : ℝ)|^1105 ≤ (45576580773259/100000000000000 : ℝ)^849
        have hw : |(54676723/100000000 : ℝ)|=(54676723/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63337439/200000000 : ℝ)|^1105 ≤ (11195023705947/50000000000000 : ℝ)^849
        have hw : |(63337439/200000000 : ℝ)|=(63337439/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1460_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (283/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13023/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4419/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4419 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4419*1^1024 ≤ 0^1024*1^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4419/1024 : ℝ) ≤ (1917422735928675573/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4419 ≤ (1917422735928675573/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4419*100000000000000000000^1024 ≤ 1917422735928675573^1024*5^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1917422735928675573 100000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1917422735928675573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4419 := by
      have hnat : (1 : ℕ)^1024*1^4419 ≤ 1^4419*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101917422735928675573/100000000000000000000 : ℝ) ≤ (401764327147251/400000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (101917422735928675573/100000000000000000000 : ℝ)^1024 ≤ (401764327147251/400000000000000 : ℝ)^4419 := by
      have hnat : (101917422735928675573 : ℕ)^1024*400000000000000^4419 ≤ 401764327147251^4419*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101917422735928675573 100000000000000000000 401764327147251 400000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401764327147251/400000000000000 : ℝ)) (X := (101917422735928675573/100000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51917422735928675573/50000000000000000000 : ℝ) ≤ (201764327147251/200000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (51917422735928675573/50000000000000000000 : ℝ)^1024 ≤ (201764327147251/200000000000000 : ℝ)^4419 := by
      have hnat : (51917422735928675573 : ℕ)^1024*200000000000000^4419 ≤ 201764327147251^4419*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51917422735928675573 50000000000000000000 201764327147251 200000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201764327147251/200000000000000 : ℝ)) (X := (51917422735928675573/50000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1764327147251/160000000000000 : ℝ)*(0 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1764327147251/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1917422735928675573/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1764327147251/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4419/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1764327147251/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(401764327147251/400000000000000 : ℝ) by norm_num, show 1+(1917422735928675573/100000000000000000000 : ℝ)+(0 : ℝ)=(101917422735928675573/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1917422735928675573/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1764327147251/160000000000000 : ℝ)*(2/5 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1764327147251/160000000000000 : ℝ)*(2/5 : ℝ)=(201764327147251/200000000000000 : ℝ) by norm_num, show 1+2*(1917422735928675573/100000000000000000000 : ℝ)=(51917422735928675573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1764327147251/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1764327147251/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1764327147251/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1764327147251/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1764327147251/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1764327147251/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-435349161/2500000000 : ℝ)*X 0 0+(5947491957/10000000000 : ℝ)*X 0 1+(4838273447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5488656641/10000000000 : ℝ)*X 1 0+(-1183328757/5000000000 : ℝ)*X 1 1+(4838273627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5488657279/10000000000 : ℝ)*X 2 0+(4838273653/10000000000 : ℝ)*X 2 1+(-118332833/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((832317147/2000000000 : ℝ)*X 0 0+(3102720021/10000000000 : ℝ)*X 0 1+(5529614223/10000000000 : ℝ)*X 0 2+(832317147/2000000000 : ℝ)*X 1 0+(3102720021/10000000000 : ℝ)*X 1 1+(5529614223/10000000000 : ℝ)*X 1 2+(832317147/2000000000 : ℝ)*X 2 0+(3102720021/10000000000 : ℝ)*X 2 1+(5529614223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-174526631/1000000000 : ℝ)*X 0 0+(4866583823/10000000000 : ℝ)*X 0 1+(5918171811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5185777133/10000000000 : ℝ)*X 1 0+(-643379241/5000000000 : ℝ)*X 1 1+(5918171883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5185777169/10000000000 : ℝ)*X 2 0+(5918171721/10000000000 : ℝ)*X 2 1+(-1286758683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((521256857/1250000000 : ℝ)*X 0 0+(54676723/100000000 : ℝ)*X 0 1+(63337439/200000000 : ℝ)*X 0 2+(521256857/1250000000 : ℝ)*X 1 0+(54676723/100000000 : ℝ)*X 1 1+(63337439/200000000 : ℝ)*X 1 2+(521256857/1250000000 : ℝ)*X 2 0+(54676723/100000000 : ℝ)*X 2 1+(63337439/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11004502892158740104073/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (734943581/50000000000000 : ℝ)*(base19) + (184712639/12500000000000 : ℝ)*(base23) + (119666401/100000000000000 : ℝ)*(upper3) + (2129189/4000000000000 : ℝ)*(upper4) + (297183803/100000000000000 : ℝ)*(upper5) + (656800251115441/100000000000000 : ℝ)*(major0) + (656800251115441/100000000000000 : ℝ)*(major1) + (656800251115441/100000000000000 : ℝ)*(major2) + (18030796647691/2000000000000 : ℝ)*(sp0) + (90154443044767/10000000000000 : ℝ)*(sp1) + (22538610565843/2500000000000 : ℝ)*(sp2) + (51506498453181/12500000000000 : ℝ)*(sp3) + (3033975141/50000000000000 : ℝ)*(sp4) + (1215431109/50000000000000 : ℝ)*(sp7) + (206027209243833/50000000000000 : ℝ)*(f.failure) + (56346618770927/6250000000000 : ℝ)*(f.sum) + (5874315341309/8000000000000000000000000000 : ℝ)*base66 + (115780325101309/16000000000000000000000000000 : ℝ)*base68 + (12693418093309/16000000000000000000000000000 : ℝ)*base70 + (23952745074691/16000000000000000000000000000 : ℝ)*base71 + (54706300621309/8000000000000000000000000000 : ℝ)*base74 + (1312109298691/16000000000000000000000000000 : ℝ)*base75 + (25333197485309/16000000000000000000000000000 : ℝ)*base78 + (18817552685309/16000000000000000000000000000 : ℝ)*base80 + (6173447629309/8000000000000000000000000000 : ℝ)*base82 + (19639339/5000000000000000000000 : ℝ)*base89 + (19639339/5000000000000000000000 : ℝ)*base91 + (19639339/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5915214722413091753289/800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (337707577/20000000000000 : ℝ)*(base19) + (1703934009/100000000000000 : ℝ)*(base23) + (15569157/10000000000000 : ℝ)*(base32) + (63646717/25000000000000 : ℝ)*(upper3) + (19578971/12500000000000 : ℝ)*(upper5) + (346393364470141/50000000000000 : ℝ)*(major0) + (346393364470141/50000000000000 : ℝ)*(major1) + (692786728940283/100000000000000 : ℝ)*(major2) + (4088274561/100000000000000 : ℝ)*(sp1) + (4238844217/100000000000000 : ℝ)*(sp2) + (237735521341873/25000000000000 : ℝ)*(sp4) + (475468154277523/50000000000000 : ℝ)*(sp5) + (475468071294633/50000000000000 : ℝ)*(sp6) + (217315485177109/50000000000000 : ℝ)*(sp7) + (108657781511447/25000000000000 : ℝ)*(f.failure) + (237735521341873/25000000000000 : ℝ)*(f.sum) + (3203176666237/3200000000000000000000000000 : ℝ)*base66 + (55076966443967/16000000000000000000000000000 : ℝ)*base68 + (45543274836391/8000000000000000000000000000 : ℝ)*base69 + (48189158619967/16000000000000000000000000000 : ℝ)*base72 + (16651086381437/3200000000000000000000000000 : ℝ)*base74 + (67254424012391/8000000000000000000000000000 : ℝ)*base75 + (33527149107609/8000000000000000000000000000 : ℝ)*base78 + (32137283363609/8000000000000000000000000000 : ℝ)*base80 + (14447313075609/4000000000000000000000000000 : ℝ)*base82 + (26040901/2500000000000000000000 : ℝ)*base89 + (26040901/2500000000000000000000 : ℝ)*base91 + (1040901/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1460_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13023/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1460_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1460_s1_0 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-954687739/5000000000 : ℝ)*x 0 + (1118612021/2000000000 : ℝ)*x 1 + (5084963383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954687739/5000000000 : ℝ)^1105 ≤ (5794655724541/50000000000000 : ℝ)^849 := by
    have hnat : (954687739 : ℕ)^1105*50000000000000^849 ≤ 5794655724541^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954687739 5000000000 5794655724541 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118612021/2000000000 : ℝ)^1105 ≤ (46941604488773/100000000000000 : ℝ)^849 := by
    have hnat : (1118612021 : ℕ)^1105*100000000000000^849 ≤ 46941604488773^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118612021 2000000000 46941604488773 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084963383/10000000000 : ℝ)^1105 ≤ (41469084044939/100000000000000 : ℝ)^849 := by
    have hnat : (5084963383 : ℕ)^1105*100000000000000^849 ≤ 41469084044939^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084963383 10000000000 41469084044939 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-954687739/5000000000 : ℝ), (1118612021/2000000000 : ℝ), (5084963383/10000000000 : ℝ)] ![(5794655724541/50000000000000 : ℝ), (46941604488773/100000000000000 : ℝ), (41469084044939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-954687739/5000000000 : ℝ)|^1105 ≤ (5794655724541/50000000000000 : ℝ)^849
        have hw : |(-954687739/5000000000 : ℝ)|=(954687739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118612021/2000000000 : ℝ)|^1105 ≤ (46941604488773/100000000000000 : ℝ)^849
        have hw : |(1118612021/2000000000 : ℝ)|=(1118612021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084963383/10000000000 : ℝ)|^1105 ≤ (41469084044939/100000000000000 : ℝ)^849
        have hw : |(5084963383/10000000000 : ℝ)|=(5084963383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s1_1 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2696862707/5000000000 : ℝ)*x 0 + (-1088993663/5000000000 : ℝ)*x 1 + (635620681/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696862707/5000000000 : ℝ)^1105 ≤ (2798497771831/6250000000000 : ℝ)^849 := by
    have hnat : (2696862707 : ℕ)^1105*6250000000000^849 ≤ 2798497771831^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696862707 5000000000 2798497771831 6250000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088993663/5000000000 : ℝ)^1105 ≤ (13754929674379/100000000000000 : ℝ)^849 := by
    have hnat : (1088993663 : ℕ)^1105*100000000000000^849 ≤ 13754929674379^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088993663 5000000000 13754929674379 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635620681/1250000000 : ℝ)^1105 ≤ (20734552981731/50000000000000 : ℝ)^849 := by
    have hnat : (635620681 : ℕ)^1105*50000000000000^849 ≤ 20734552981731^849*1250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635620681 1250000000 20734552981731 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696862707/5000000000 : ℝ), (-1088993663/5000000000 : ℝ), (635620681/1250000000 : ℝ)] ![(2798497771831/6250000000000 : ℝ), (13754929674379/100000000000000 : ℝ), (20734552981731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696862707/5000000000 : ℝ)|^1105 ≤ (2798497771831/6250000000000 : ℝ)^849
        have hw : |(2696862707/5000000000 : ℝ)|=(2696862707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1088993663/5000000000 : ℝ)|^1105 ≤ (13754929674379/100000000000000 : ℝ)^849
        have hw : |(-1088993663/5000000000 : ℝ)|=(1088993663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635620681/1250000000 : ℝ)|^1105 ≤ (20734552981731/50000000000000 : ℝ)^849
        have hw : |(635620681/1250000000 : ℝ)|=(635620681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s1_2 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5393727149/10000000000 : ℝ)*x 0 + (1016992707/2000000000 : ℝ)*x 1 + (-435597503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393727149/10000000000 : ℝ)^1105 ≤ (8955196619073/20000000000000 : ℝ)^849 := by
    have hnat : (5393727149 : ℕ)^1105*20000000000000^849 ≤ 8955196619073^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393727149 10000000000 8955196619073 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016992707/2000000000 : ℝ)^1105 ≤ (5183635707289/12500000000000 : ℝ)^849 := by
    have hnat : (1016992707 : ℕ)^1105*12500000000000^849 ≤ 5183635707289^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016992707 2000000000 5183635707289 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435597503/2000000000 : ℝ)^1105 ≤ (3438732806977/25000000000000 : ℝ)^849 := by
    have hnat : (435597503 : ℕ)^1105*25000000000000^849 ≤ 3438732806977^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435597503 2000000000 3438732806977 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393727149/10000000000 : ℝ), (1016992707/2000000000 : ℝ), (-435597503/2000000000 : ℝ)] ![(8955196619073/20000000000000 : ℝ), (5183635707289/12500000000000 : ℝ), (3438732806977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393727149/10000000000 : ℝ)|^1105 ≤ (8955196619073/20000000000000 : ℝ)^849
        have hw : |(5393727149/10000000000 : ℝ)|=(5393727149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016992707/2000000000 : ℝ)|^1105 ≤ (5183635707289/12500000000000 : ℝ)^849
        have hw : |(1016992707/2000000000 : ℝ)|=(1016992707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435597503/2000000000 : ℝ)|^1105 ≤ (3438732806977/25000000000000 : ℝ)^849
        have hw : |(-435597503/2000000000 : ℝ)|=(435597503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s1_3 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4270988569/10000000000 : ℝ)*x 0 + (1873510021/5000000000 : ℝ)*x 1 + (4858695537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270988569/10000000000 : ℝ)^1105 ≤ (33046174515067/100000000000000 : ℝ)^849 := by
    have hnat : (4270988569 : ℕ)^1105*100000000000000^849 ≤ 33046174515067^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270988569 10000000000 33046174515067 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1873510021/5000000000 : ℝ)^1105 ≤ (27870133130641/100000000000000 : ℝ)^849 := by
    have hnat : (1873510021 : ℕ)^1105*100000000000000^849 ≤ 27870133130641^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873510021 5000000000 27870133130641 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4858695537/10000000000 : ℝ)^1105 ≤ (7816738468187/20000000000000 : ℝ)^849 := by
    have hnat : (4858695537 : ℕ)^1105*20000000000000^849 ≤ 7816738468187^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4858695537 10000000000 7816738468187 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270988569/10000000000 : ℝ), (1873510021/5000000000 : ℝ), (4858695537/10000000000 : ℝ)] ![(33046174515067/100000000000000 : ℝ), (27870133130641/100000000000000 : ℝ), (7816738468187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270988569/10000000000 : ℝ)|^1105 ≤ (33046174515067/100000000000000 : ℝ)^849
        have hw : |(4270988569/10000000000 : ℝ)|=(4270988569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1873510021/5000000000 : ℝ)|^1105 ≤ (27870133130641/100000000000000 : ℝ)^849
        have hw : |(1873510021/5000000000 : ℝ)|=(1873510021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4858695537/10000000000 : ℝ)|^1105 ≤ (7816738468187/20000000000000 : ℝ)^849
        have hw : |(4858695537/10000000000 : ℝ)|=(4858695537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s1_4 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909733399/10000000000 : ℝ)*x 0 + (2545389127/5000000000 : ℝ)*x 1 + (1396787269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909733399/10000000000 : ℝ)^1105 ≤ (11592139064459/100000000000000 : ℝ)^849 := by
    have hnat : (1909733399 : ℕ)^1105*100000000000000^849 ≤ 11592139064459^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909733399 10000000000 11592139064459 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2545389127/5000000000 : ℝ)^1105 ≤ (41530815446067/100000000000000 : ℝ)^849 := by
    have hnat : (2545389127 : ℕ)^1105*100000000000000^849 ≤ 41530815446067^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545389127 5000000000 41530815446067 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1396787269/2500000000 : ℝ)^1105 ≤ (46877045473161/100000000000000 : ℝ)^849 := by
    have hnat : (1396787269 : ℕ)^1105*100000000000000^849 ≤ 46877045473161^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396787269 2500000000 46877045473161 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909733399/10000000000 : ℝ), (2545389127/5000000000 : ℝ), (1396787269/2500000000 : ℝ)] ![(11592139064459/100000000000000 : ℝ), (41530815446067/100000000000000 : ℝ), (46877045473161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909733399/10000000000 : ℝ)|^1105 ≤ (11592139064459/100000000000000 : ℝ)^849
        have hw : |(-1909733399/10000000000 : ℝ)|=(1909733399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2545389127/5000000000 : ℝ)|^1105 ≤ (41530815446067/100000000000000 : ℝ)^849
        have hw : |(2545389127/5000000000 : ℝ)|=(2545389127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1396787269/2500000000 : ℝ)|^1105 ≤ (46877045473161/100000000000000 : ℝ)^849
        have hw : |(1396787269/2500000000 : ℝ)|=(1396787269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s1_5 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5260675623/10000000000 : ℝ)*x 0 + (-41895073/250000000 : ℝ)*x 1 + (5587149113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260675623/10000000000 : ℝ)^1105 ≤ (677246644503/1562500000000 : ℝ)^849 := by
    have hnat : (5260675623 : ℕ)^1105*1562500000000^849 ≤ 677246644503^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260675623 10000000000 677246644503 1562500000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41895073/250000000 : ℝ)^1105 ≤ (9779168866981/100000000000000 : ℝ)^849 := by
    have hnat : (41895073 : ℕ)^1105*100000000000000^849 ≤ 9779168866981^849*250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41895073 250000000 9779168866981 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5587149113/10000000000 : ℝ)^1105 ≤ (23438522938601/50000000000000 : ℝ)^849 := by
    have hnat : (5587149113 : ℕ)^1105*50000000000000^849 ≤ 23438522938601^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5587149113 10000000000 23438522938601 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260675623/10000000000 : ℝ), (-41895073/250000000 : ℝ), (5587149113/10000000000 : ℝ)] ![(677246644503/1562500000000 : ℝ), (9779168866981/100000000000000 : ℝ), (23438522938601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260675623/10000000000 : ℝ)|^1105 ≤ (677246644503/1562500000000 : ℝ)^849
        have hw : |(5260675623/10000000000 : ℝ)|=(5260675623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41895073/250000000 : ℝ)|^1105 ≤ (9779168866981/100000000000000 : ℝ)^849
        have hw : |(-41895073/250000000 : ℝ)|=(41895073/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5587149113/10000000000 : ℝ)|^1105 ≤ (23438522938601/50000000000000 : ℝ)^849
        have hw : |(5587149113/10000000000 : ℝ)|=(5587149113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s1_6 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5260675503/10000000000 : ℝ)*x 0 + (5587149079/10000000000 : ℝ)*x 1 + (-837901569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260675503/10000000000 : ℝ)^1105 ≤ (21671891980681/50000000000000 : ℝ)^849 := by
    have hnat : (5260675503 : ℕ)^1105*50000000000000^849 ≤ 21671891980681^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260675503 10000000000 21671891980681 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5587149079/10000000000 : ℝ)^1105 ≤ (46877045505921/100000000000000 : ℝ)^849 := by
    have hnat : (5587149079 : ℕ)^1105*100000000000000^849 ≤ 46877045505921^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5587149079 10000000000 46877045505921 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (837901569/5000000000 : ℝ)^1105 ≤ (4889585261357/50000000000000 : ℝ)^849 := by
    have hnat : (837901569 : ℕ)^1105*50000000000000^849 ≤ 4889585261357^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837901569 5000000000 4889585261357 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260675503/10000000000 : ℝ), (5587149079/10000000000 : ℝ), (-837901569/5000000000 : ℝ)] ![(21671891980681/50000000000000 : ℝ), (46877045505921/100000000000000 : ℝ), (4889585261357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260675503/10000000000 : ℝ)|^1105 ≤ (21671891980681/50000000000000 : ℝ)^849
        have hw : |(5260675503/10000000000 : ℝ)|=(5260675503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5587149079/10000000000 : ℝ)|^1105 ≤ (46877045505921/100000000000000 : ℝ)^849
        have hw : |(5587149079/10000000000 : ℝ)|=(5587149079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-837901569/5000000000 : ℝ)|^1105 ≤ (4889585261357/50000000000000 : ℝ)^849
        have hw : |(-837901569/5000000000 : ℝ)|=(837901569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s1_7 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4271772443/10000000000 : ℝ)*x 0 + (605746851/1250000000 : ℝ)*x 1 + (939987447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271772443/10000000000 : ℝ)^1105 ≤ (4131758583753/12500000000000 : ℝ)^849 := by
    have hnat : (4271772443 : ℕ)^1105*12500000000000^849 ≤ 4131758583753^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271772443 10000000000 4131758583753 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605746851/1250000000 : ℝ)^1105 ≤ (4868820484533/12500000000000 : ℝ)^849 := by
    have hnat : (605746851 : ℕ)^1105*12500000000000^849 ≤ 4868820484533^849*1250000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605746851 1250000000 4868820484533 12500000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939987447/2500000000 : ℝ)^1105 ≤ (27995367434837/100000000000000 : ℝ)^849 := by
    have hnat : (939987447 : ℕ)^1105*100000000000000^849 ≤ 27995367434837^849*2500000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939987447 2500000000 27995367434837 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271772443/10000000000 : ℝ), (605746851/1250000000 : ℝ), (939987447/2500000000 : ℝ)] ![(4131758583753/12500000000000 : ℝ), (4868820484533/12500000000000 : ℝ), (27995367434837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271772443/10000000000 : ℝ)|^1105 ≤ (4131758583753/12500000000000 : ℝ)^849
        have hw : |(4271772443/10000000000 : ℝ)|=(4271772443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605746851/1250000000 : ℝ)|^1105 ≤ (4868820484533/12500000000000 : ℝ)^849
        have hw : |(605746851/1250000000 : ℝ)|=(605746851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(939987447/2500000000 : ℝ)|^1105 ≤ (27995367434837/100000000000000 : ℝ)^849
        have hw : |(939987447/2500000000 : ℝ)|=(939987447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1460_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (7901/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3729/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (283/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13023/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (283/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (283/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13023/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (283/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (283/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13023/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (283/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (283/12500 : ℝ) ^ (4419/1024 : ℝ) ≤ (7953986950201/100000000000000000000 : ℝ) := by
    have hpowers : (283/12500 : ℝ)^4419 ≤ (7953986950201/100000000000000000000 : ℝ)^1024 := by
      have hnat : (283 : ℕ)^4419*100000000000000000000^1024 ≤ 7953986950201^1024*12500^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        283 12500 7953986950201 100000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (283/12500 : ℝ)) (X := (7953986950201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13023/50000 : ℝ) ^ (4419/1024 : ℝ) ≤ (301072800670356661/100000000000000000000 : ℝ) := by
    have hpowers : (13023/50000 : ℝ)^4419 ≤ (301072800670356661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13023 : ℕ)^4419*100000000000000000000^1024 ≤ 301072800670356661^1024*50000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13023 50000 301072800670356661 100000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13023/50000 : ℝ)) (X := (301072800670356661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000007953986950201/50000000000000000000 : ℝ) ≤ (1250000046078763/1250000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (50000007953986950201/50000000000000000000 : ℝ)^1024 ≤ (1250000046078763/1250000000000000 : ℝ)^4419 := by
      have hnat : (50000007953986950201 : ℕ)^1024*1250000000000000^4419 ≤ 1250000046078763^4419*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000007953986950201 50000000000000000000 1250000046078763 1250000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000046078763/1250000000000000 : ℝ)) (X := (50000007953986950201/50000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50150540377328653431/50000000000000000000 : ℝ) ≤ (5003484394077387/5000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (50150540377328653431/50000000000000000000 : ℝ)^1024 ≤ (5003484394077387/5000000000000000 : ℝ)^4419 := by
      have hnat : (50150540377328653431 : ℕ)^1024*5000000000000000^4419 ≤ 5003484394077387^4419*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50150540377328653431 50000000000000000000 5003484394077387 5000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003484394077387/5000000000000000 : ℝ)) (X := (50150540377328653431/50000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50301072800670356661/50000000000000000000 : ℝ) ≤ (2503484301919861/2500000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (50301072800670356661/50000000000000000000 : ℝ)^1024 ≤ (2503484301919861/2500000000000000 : ℝ)^4419 := by
      have hnat : (50301072800670356661 : ℕ)^1024*2500000000000000^4419 ≤ 2503484301919861^4419*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50301072800670356661 50000000000000000000 2503484301919861 2500000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503484301919861/2500000000000000 : ℝ)) (X := (50301072800670356661/50000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7953986950201/100000000000000000000 : ℝ) ≤ ((14861778485197089223/14863750000000000000 : ℝ)+2*(696841952467/237820000000000 : ℝ)*(283/12500 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (14861778485197089223/14863750000000000000 : ℝ)+2*(696841952467/237820000000000 : ℝ)*(283/12500 : ℝ)=(1250000046078763/1250000000000000 : ℝ) by norm_num, show 1+2*(7953986950201/100000000000000000000 : ℝ)=(50000007953986950201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(301072800670356661/100000000000000000000 : ℝ)+(7953986950201/100000000000000000000 : ℝ) ≤ ((14861778485197089223/14863750000000000000 : ℝ)+(696841952467/237820000000000 : ℝ)*((13023/50000 : ℝ)+(283/12500 : ℝ)))^(4419/1024 : ℝ) := by
    rw [show (14861778485197089223/14863750000000000000 : ℝ)+(696841952467/237820000000000 : ℝ)*((13023/50000 : ℝ)+(283/12500 : ℝ))=(5003484394077387/5000000000000000 : ℝ) by norm_num, show 1+(301072800670356661/100000000000000000000 : ℝ)+(7953986950201/100000000000000000000 : ℝ)=(50150540377328653431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(301072800670356661/100000000000000000000 : ℝ) ≤ ((14861778485197089223/14863750000000000000 : ℝ)+2*(696841952467/237820000000000 : ℝ)*(13023/50000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (14861778485197089223/14863750000000000000 : ℝ)+2*(696841952467/237820000000000 : ℝ)*(13023/50000 : ℝ)=(2503484301919861/2500000000000000 : ℝ) by norm_num, show 1+2*(301072800670356661/100000000000000000000 : ℝ)=(50301072800670356661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14861778485197089223/14863750000000000000 : ℝ)*(X 1 0+X 2 0)+(696841952467/237820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (283/12500 : ℝ)) (hi := (13023/50000 : ℝ)) (c := (14861778485197089223/14863750000000000000 : ℝ)) (alpha := (696841952467/237820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14861778485197089223/14863750000000000000 : ℝ)*(X 0 1+X 2 1)+(696841952467/237820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (283/12500 : ℝ)) (hi := (13023/50000 : ℝ)) (c := (14861778485197089223/14863750000000000000 : ℝ)) (alpha := (696841952467/237820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14861778485197089223/14863750000000000000 : ℝ)*(X 0 2+X 1 2)+(696841952467/237820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (283/12500 : ℝ)) (hi := (13023/50000 : ℝ)) (c := (14861778485197089223/14863750000000000000 : ℝ)) (alpha := (696841952467/237820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-954687739/5000000000 : ℝ)*X 0 0+(1118612021/2000000000 : ℝ)*X 0 1+(5084963383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2696862707/5000000000 : ℝ)*X 1 0+(-1088993663/5000000000 : ℝ)*X 1 1+(635620681/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5393727149/10000000000 : ℝ)*X 2 0+(1016992707/2000000000 : ℝ)*X 2 1+(-435597503/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4270988569/10000000000 : ℝ)*X 0 0+(1873510021/5000000000 : ℝ)*X 0 1+(4858695537/10000000000 : ℝ)*X 0 2+(4270988569/10000000000 : ℝ)*X 1 0+(1873510021/5000000000 : ℝ)*X 1 1+(4858695537/10000000000 : ℝ)*X 1 2+(4270988569/10000000000 : ℝ)*X 2 0+(1873510021/5000000000 : ℝ)*X 2 1+(4858695537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1909733399/10000000000 : ℝ)*X 0 0+(2545389127/5000000000 : ℝ)*X 0 1+(1396787269/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260675623/10000000000 : ℝ)*X 1 0+(-41895073/250000000 : ℝ)*X 1 1+(5587149113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5260675503/10000000000 : ℝ)*X 2 0+(5587149079/10000000000 : ℝ)*X 2 1+(-837901569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4271772443/10000000000 : ℝ)*X 0 0+(605746851/1250000000 : ℝ)*X 0 1+(939987447/2500000000 : ℝ)*X 0 2+(4271772443/10000000000 : ℝ)*X 1 0+(605746851/1250000000 : ℝ)*X 1 1+(939987447/2500000000 : ℝ)*X 1 2+(4271772443/10000000000 : ℝ)*X 2 0+(605746851/1250000000 : ℝ)*X 2 1+(939987447/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64355554828966916269051203/8078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (320548459/25000000000000 : ℝ)*(base19) + (74057029/4000000000000 : ℝ)*(base23) + (110467333/100000000000000 : ℝ)*(upper3) + (17224023/50000000000000 : ℝ)*(upper4) + (3410783/3125000000000 : ℝ)*(upper5) + (358464938828333/25000000000000 : ℝ)*(major0) + (358464938828333/25000000000000 : ℝ)*(major1) + (358464938828333/25000000000000 : ℝ)*(major2) + (1968145349093451/100000000000000 : ℝ)*(sp0) + (984081254751843/50000000000000 : ℝ)*(sp1) + (1968161940271797/100000000000000 : ℝ)*(sp2) + (179909758834627/20000000000000 : ℝ)*(sp3) + (18442604071/100000000000000 : ℝ)*(sp4) + (166480029/2500000000000 : ℝ)*(sp7) + (179911090674859/20000000000000 : ℝ)*(f.failure) + (984081895848761/50000000000000 : ℝ)*(f.sum) + (148087241821/64625000000000000000000000 : ℝ)*base66 + (168722745052685283/16156250000000000000000000000000 : ℝ)*base67 + (64119874030654033/16156250000000000000000000000000 : ℝ)*base69 + (146115137048935283/16156250000000000000000000000000 : ℝ)*base71 + (269931651049/51700000000000000000000000 : ℝ)*base73 + (63521314065560283/16156250000000000000000000000000 : ℝ)*base75 + (142673197447904033/16156250000000000000000000000000 : ℝ)*base77 + (245458825393247783/16156250000000000000000000000000 : ℝ)*base79 + (276807267447/129250000000000000000000000 : ℝ)*base81 + (18879103/2000000000000000000000 : ℝ)*base90 + (18879103/2000000000000000000000 : ℝ)*base92 + (18879103/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (156973894068962620048352667/18579687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (917809051/50000000000000 : ℝ)*(base19) + (116355729/6250000000000 : ℝ)*(base23) + (56050097/25000000000000 : ℝ)*(upper3) + (37480573/100000000000000 : ℝ)*(lower4) + (34338339/20000000000000 : ℝ)*(upper5) + (146770560769839/10000000000000 : ℝ)*(major0) + (146770560769839/10000000000000 : ℝ)*(major1) + (146770560769839/10000000000000 : ℝ)*(major2) + (5907048067/50000000000000 : ℝ)*(sp1) + (11844845773/100000000000000 : ℝ)*(sp2) + (201462172934821/10000000000000 : ℝ)*(sp4) + (1007304039816987/50000000000000 : ℝ)*(sp5) + (1007304011405387/50000000000000 : ℝ)*(sp6) + (92078920442579/10000000000000 : ℝ)*(sp7) + (92078920442579/10000000000000 : ℝ)*(f.failure) + (201462172934821/10000000000000 : ℝ)*(f.sum) + (377400049/9512800000000000000000000 : ℝ)*base66 + (1224734034012907597/148637500000000000000000000000000 : ℝ)*base67 + (724767601605157597/148637500000000000000000000000000 : ℝ)*base69 + (687060680539057597/148637500000000000000000000000000 : ℝ)*base71 + (11269515440367/5945500000000000000000000000 : ℝ)*base73 + (969218449200232597/148637500000000000000000000000000 : ℝ)*base75 + (39759942127670097/148637500000000000000000000000000 : ℝ)*base77 + (155727734007729903/148637500000000000000000000000000 : ℝ)*base80 + (20864741729947/11891000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3950343/1000000000000000000000 : ℝ)*base90 + (3950343/1000000000000000000000 : ℝ)*base92 + (3950343/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1460_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13023/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7901/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3729/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1460_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1460_s2_0 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1940262567/10000000000 : ℝ)*x 0 + (109029517/200000000 : ℝ)*x 1 + (5206632471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1940262567/10000000000 : ℝ)^1105 ≤ (11833908831393/100000000000000 : ℝ)^849 := by
    have hnat : (1940262567 : ℕ)^1105*100000000000000^849 ≤ 11833908831393^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940262567 10000000000 11833908831393 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109029517/200000000 : ℝ)^1105 ≤ (45400942341079/100000000000000 : ℝ)^849 := by
    have hnat : (109029517 : ℕ)^1105*100000000000000^849 ≤ 45400942341079^849*200000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109029517 200000000 45400942341079 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206632471/10000000000 : ℝ)^1105 ≤ (42765148800113/100000000000000 : ℝ)^849 := by
    have hnat : (5206632471 : ℕ)^1105*100000000000000^849 ≤ 42765148800113^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206632471 10000000000 42765148800113 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1940262567/10000000000 : ℝ), (109029517/200000000 : ℝ), (5206632471/10000000000 : ℝ)] ![(11833908831393/100000000000000 : ℝ), (45400942341079/100000000000000 : ℝ), (42765148800113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1940262567/10000000000 : ℝ)|^1105 ≤ (11833908831393/100000000000000 : ℝ)^849
        have hw : |(-1940262567/10000000000 : ℝ)|=(1940262567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109029517/200000000 : ℝ)|^1105 ≤ (45400942341079/100000000000000 : ℝ)^849
        have hw : |(109029517/200000000 : ℝ)|=(109029517/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206632471/10000000000 : ℝ)|^1105 ≤ (42765148800113/100000000000000 : ℝ)^849
        have hw : |(5206632471/10000000000 : ℝ)|=(5206632471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s2_1 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1071642911/2000000000 : ℝ)*x 0 + (-413214341/2000000000 : ℝ)*x 1 + (5206628787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071642911/2000000000 : ℝ)^1105 ≤ (44392663376087/100000000000000 : ℝ)^849 := by
    have hnat : (1071642911 : ℕ)^1105*100000000000000^849 ≤ 44392663376087^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071642911 2000000000 44392663376087 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413214341/2000000000 : ℝ)^1105 ≤ (2568445437787/20000000000000 : ℝ)^849 := by
    have hnat : (413214341 : ℕ)^1105*20000000000000^849 ≤ 2568445437787^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413214341 2000000000 2568445437787 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206628787/10000000000 : ℝ)^1105 ≤ (8553021883451/20000000000000 : ℝ)^849 := by
    have hnat : (5206628787 : ℕ)^1105*20000000000000^849 ≤ 8553021883451^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206628787 10000000000 8553021883451 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071642911/2000000000 : ℝ), (-413214341/2000000000 : ℝ), (5206628787/10000000000 : ℝ)] ![(44392663376087/100000000000000 : ℝ), (2568445437787/20000000000000 : ℝ), (8553021883451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071642911/2000000000 : ℝ)|^1105 ≤ (44392663376087/100000000000000 : ℝ)^849
        have hw : |(1071642911/2000000000 : ℝ)|=(1071642911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413214341/2000000000 : ℝ)|^1105 ≤ (2568445437787/20000000000000 : ℝ)^849
        have hw : |(-413214341/2000000000 : ℝ)|=(413214341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206628787/10000000000 : ℝ)|^1105 ≤ (8553021883451/20000000000000 : ℝ)^849
        have hw : |(5206628787/10000000000 : ℝ)|=(5206628787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s2_2 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5358212413/10000000000 : ℝ)*x 0 + (2603315299/5000000000 : ℝ)*x 1 + (-2066072167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358212413/10000000000 : ℝ)^1105 ≤ (44392640278579/100000000000000 : ℝ)^849 := by
    have hnat : (5358212413 : ℕ)^1105*100000000000000^849 ≤ 44392640278579^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358212413 10000000000 44392640278579 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603315299/5000000000 : ℝ)^1105 ≤ (8553025755457/20000000000000 : ℝ)^849 := by
    have hnat : (2603315299 : ℕ)^1105*20000000000000^849 ≤ 8553025755457^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603315299 5000000000 8553025755457 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066072167/10000000000 : ℝ)^1105 ≤ (3210557731631/25000000000000 : ℝ)^849 := by
    have hnat : (2066072167 : ℕ)^1105*25000000000000^849 ≤ 3210557731631^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066072167 10000000000 3210557731631 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358212413/10000000000 : ℝ), (2603315299/5000000000 : ℝ), (-2066072167/10000000000 : ℝ)] ![(44392640278579/100000000000000 : ℝ), (8553025755457/20000000000000 : ℝ), (3210557731631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358212413/10000000000 : ℝ)|^1105 ≤ (44392640278579/100000000000000 : ℝ)^849
        have hw : |(5358212413/10000000000 : ℝ)|=(5358212413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603315299/5000000000 : ℝ)|^1105 ≤ (8553025755457/20000000000000 : ℝ)^849
        have hw : |(2603315299/5000000000 : ℝ)|=(2603315299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2066072167/10000000000 : ℝ)|^1105 ≤ (3210557731631/25000000000000 : ℝ)^849
        have hw : |(-2066072167/10000000000 : ℝ)|=(2066072167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s2_3 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (858572639/2000000000 : ℝ)*x 0 + (252025591/625000000 : ℝ)*x 1 + (2284058987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858572639/2000000000 : ℝ)^1105 ≤ (33266630975079/100000000000000 : ℝ)^849 := by
    have hnat : (858572639 : ℕ)^1105*100000000000000^849 ≤ 33266630975079^849*2000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858572639 2000000000 33266630975079 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252025591/625000000 : ℝ)^1105 ≤ (30664087618747/100000000000000 : ℝ)^849 := by
    have hnat : (252025591 : ℕ)^1105*100000000000000^849 ≤ 30664087618747^849*625000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252025591 625000000 30664087618747 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2284058987/5000000000 : ℝ)^1105 ≤ (36069281388919/100000000000000 : ℝ)^849 := by
    have hnat : (2284058987 : ℕ)^1105*100000000000000^849 ≤ 36069281388919^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284058987 5000000000 36069281388919 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(858572639/2000000000 : ℝ), (252025591/625000000 : ℝ), (2284058987/5000000000 : ℝ)] ![(33266630975079/100000000000000 : ℝ), (30664087618747/100000000000000 : ℝ), (36069281388919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(858572639/2000000000 : ℝ)|^1105 ≤ (33266630975079/100000000000000 : ℝ)^849
        have hw : |(858572639/2000000000 : ℝ)|=(858572639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252025591/625000000 : ℝ)|^1105 ≤ (30664087618747/100000000000000 : ℝ)^849
        have hw : |(252025591/625000000 : ℝ)|=(252025591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2284058987/5000000000 : ℝ)|^1105 ≤ (36069281388919/100000000000000 : ℝ)^849
        have hw : |(2284058987/5000000000 : ℝ)|=(2284058987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s2_4 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-121268921/625000000 : ℝ)*x 0 + (5207990043/10000000000 : ℝ)*x 1 + (2725053719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121268921/625000000 : ℝ)^1105 ≤ (11834227702139/100000000000000 : ℝ)^849 := by
    have hnat : (121268921 : ℕ)^1105*100000000000000^849 ≤ 11834227702139^849*625000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121268921 625000000 11834227702139 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5207990043/10000000000 : ℝ)^1105 ≤ (21389831073837/50000000000000 : ℝ)^849 := by
    have hnat : (5207990043 : ℕ)^1105*50000000000000^849 ≤ 21389831073837^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207990043 10000000000 21389831073837 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725053719/5000000000 : ℝ)^1105 ≤ (9077222026669/20000000000000 : ℝ)^849 := by
    have hnat : (2725053719 : ℕ)^1105*20000000000000^849 ≤ 9077222026669^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725053719 5000000000 9077222026669 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121268921/625000000 : ℝ), (5207990043/10000000000 : ℝ), (2725053719/5000000000 : ℝ)] ![(11834227702139/100000000000000 : ℝ), (21389831073837/50000000000000 : ℝ), (9077222026669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121268921/625000000 : ℝ)|^1105 ≤ (11834227702139/100000000000000 : ℝ)^849
        have hw : |(-121268921/625000000 : ℝ)|=(121268921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5207990043/10000000000 : ℝ)|^1105 ≤ (21389831073837/50000000000000 : ℝ)^849
        have hw : |(5207990043/10000000000 : ℝ)|=(5207990043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725053719/5000000000 : ℝ)|^1105 ≤ (9077222026669/20000000000000 : ℝ)^849
        have hw : |(2725053719/5000000000 : ℝ)|=(2725053719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s2_5 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5294364699/10000000000 : ℝ)*x 0 + (-1822591451/10000000000 : ℝ)*x 1 + (5450108601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294364699/10000000000 : ℝ)^1105 ≤ (1748216044781/4000000000000 : ℝ)^849 := by
    have hnat : (5294364699 : ℕ)^1105*4000000000000^849 ≤ 1748216044781^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294364699 10000000000 1748216044781 4000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1822591451/10000000000 : ℝ)^1105 ≤ (2181695224051/20000000000000 : ℝ)^849 := by
    have hnat : (1822591451 : ℕ)^1105*20000000000000^849 ≤ 2181695224051^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822591451 10000000000 2181695224051 20000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450108601/10000000000 : ℝ)^1105 ≤ (45386122738617/100000000000000 : ℝ)^849 := by
    have hnat : (5450108601 : ℕ)^1105*100000000000000^849 ≤ 45386122738617^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450108601 10000000000 45386122738617 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294364699/10000000000 : ℝ), (-1822591451/10000000000 : ℝ), (5450108601/10000000000 : ℝ)] ![(1748216044781/4000000000000 : ℝ), (2181695224051/20000000000000 : ℝ), (45386122738617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294364699/10000000000 : ℝ)|^1105 ≤ (1748216044781/4000000000000 : ℝ)^849
        have hw : |(5294364699/10000000000 : ℝ)|=(5294364699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1822591451/10000000000 : ℝ)|^1105 ≤ (2181695224051/20000000000000 : ℝ)^849
        have hw : |(-1822591451/10000000000 : ℝ)|=(1822591451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450108601/10000000000 : ℝ)|^1105 ≤ (45386122738617/100000000000000 : ℝ)^849
        have hw : |(5450108601/10000000000 : ℝ)|=(5450108601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s2_6 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2647181937/5000000000 : ℝ)*x 0 + (5450107637/10000000000 : ℝ)*x 1 + (-1822593931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647181937/5000000000 : ℝ)^1105 ≤ (1748215690221/4000000000000 : ℝ)^849 := by
    have hnat : (2647181937 : ℕ)^1105*4000000000000^849 ≤ 1748215690221^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647181937 5000000000 1748215690221 4000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450107637/10000000000 : ℝ)^1105 ≤ (45386112290223/100000000000000 : ℝ)^849 := by
    have hnat : (5450107637 : ℕ)^1105*100000000000000^849 ≤ 45386112290223^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450107637 10000000000 45386112290223 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1822593931/10000000000 : ℝ)^1105 ≤ (5454247719549/50000000000000 : ℝ)^849 := by
    have hnat : (1822593931 : ℕ)^1105*50000000000000^849 ≤ 5454247719549^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822593931 10000000000 5454247719549 50000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647181937/5000000000 : ℝ), (5450107637/10000000000 : ℝ), (-1822593931/10000000000 : ℝ)] ![(1748215690221/4000000000000 : ℝ), (45386112290223/100000000000000 : ℝ), (5454247719549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647181937/5000000000 : ℝ)|^1105 ≤ (1748215690221/4000000000000 : ℝ)^849
        have hw : |(2647181937/5000000000 : ℝ)|=(2647181937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450107637/10000000000 : ℝ)|^1105 ≤ (45386112290223/100000000000000 : ℝ)^849
        have hw : |(5450107637/10000000000 : ℝ)|=(5450107637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1822593931/10000000000 : ℝ)|^1105 ≤ (5454247719549/50000000000000 : ℝ)^849
        have hw : |(-1822593931/10000000000 : ℝ)|=(1822593931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1460_s2_7 (p : ℝ) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4292949677/10000000000 : ℝ)*x 0 + (4565147329/10000000000 : ℝ)*x 1 + (2017702597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4292949677/10000000000 : ℝ)^1105 ≤ (665350064599/2000000000000 : ℝ)^849 := by
    have hnat : (4292949677 : ℕ)^1105*2000000000000^849 ≤ 665350064599^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292949677 10000000000 665350064599 2000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4565147329/10000000000 : ℝ)^1105 ≤ (36038755878537/100000000000000 : ℝ)^849 := by
    have hnat : (4565147329 : ℕ)^1105*100000000000000^849 ≤ 36038755878537^849*10000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4565147329 10000000000 36038755878537 100000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017702597/5000000000 : ℝ)^1105 ≤ (7673435220127/25000000000000 : ℝ)^849 := by
    have hnat : (2017702597 : ℕ)^1105*25000000000000^849 ≤ 7673435220127^849*5000000000^1105 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017702597 5000000000 7673435220127 25000000000000 1105 849 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1105/256 : ℝ)) 1105 849 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4292949677/10000000000 : ℝ), (4565147329/10000000000 : ℝ), (2017702597/5000000000 : ℝ)] ![(665350064599/2000000000000 : ℝ), (36038755878537/100000000000000 : ℝ), (7673435220127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4292949677/10000000000 : ℝ)|^1105 ≤ (665350064599/2000000000000 : ℝ)^849
        have hw : |(4292949677/10000000000 : ℝ)|=(4292949677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4565147329/10000000000 : ℝ)|^1105 ≤ (36038755878537/100000000000000 : ℝ)^849
        have hw : |(4565147329/10000000000 : ℝ)|=(4565147329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2017702597/5000000000 : ℝ)|^1105 ≤ (7673435220127/25000000000000 : ℝ)^849
        have hw : |(2017702597/5000000000 : ℝ)|=(2017702597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1460_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3729/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10527/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15709/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3729/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3729/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3729/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3729/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3729/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3729/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7901/100000 : ℝ) ^ (4419/1024 : ℝ) ≤ (87497259105597/5000000000000000000 : ℝ) := by
    have hpowers : (7901/100000 : ℝ)^4419 ≤ (87497259105597/5000000000000000000 : ℝ)^1024 := by
      have hnat : (7901 : ℕ)^4419*5000000000000000000^1024 ≤ 87497259105597^1024*100000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7901 100000 87497259105597 5000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7901/100000 : ℝ)) (X := (87497259105597/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3729/20000 : ℝ) ^ (4419/1024 : ℝ) ≤ (14229618882316877/20000000000000000000 : ℝ) := by
    have hpowers : (3729/20000 : ℝ)^4419 ≤ (14229618882316877/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3729 : ℕ)^4419*20000000000000000000^1024 ≤ 14229618882316877^1024*20000^4419 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3729 20000 14229618882316877 20000000000000000000 4419 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3729/20000 : ℝ)) (X := (14229618882316877/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500087497259105597/2500000000000000000 : ℝ) ≤ (10000081100691353/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (2500087497259105597/2500000000000000000 : ℝ)^1024 ≤ (10000081100691353/10000000000000000 : ℝ)^4419 := by
      have hnat : (2500087497259105597 : ℕ)^1024*10000000000000000^4419 ≤ 10000081100691353^4419*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500087497259105597 2500000000000000000 10000081100691353 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000081100691353/10000000000000000 : ℝ)) (X := (2500087497259105597/2500000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002915921583747853/4000000000000000000 : ℝ) ≤ (2000337753781837/2000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (4002915921583747853/4000000000000000000 : ℝ)^1024 ≤ (2000337753781837/2000000000000000 : ℝ)^4419 := by
      have hnat : (4002915921583747853 : ℕ)^1024*2000000000000000^4419 ≤ 2000337753781837^4419*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002915921583747853 4000000000000000000 2000337753781837 2000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000337753781837/2000000000000000 : ℝ)) (X := (4002915921583747853/4000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10014229618882316877/10000000000000000000 : ℝ) ≤ (10003296437127017/10000000000000000 : ℝ) ^ (4419/1024 : ℝ) := by
    have hpowers : (10014229618882316877/10000000000000000000 : ℝ)^1024 ≤ (10003296437127017/10000000000000000 : ℝ)^4419 := by
      have hnat : (10014229618882316877 : ℕ)^1024*10000000000000000^4419 ≤ 10003296437127017^4419*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10014229618882316877 10000000000000000000 10003296437127017 10000000000000000 1024 4419 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003296437127017/10000000000000000 : ℝ)) (X := (10014229618882316877/10000000000000000000 : ℝ)) (by norm_num) 4419 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(87497259105597/5000000000000000000 : ℝ) ≤ ((789819610093012613/790000000000000000 : ℝ)+2*(11821089837/7900000000000 : ℝ)*(7901/100000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (789819610093012613/790000000000000000 : ℝ)+2*(11821089837/7900000000000 : ℝ)*(7901/100000 : ℝ)=(10000081100691353/10000000000000000 : ℝ) by norm_num, show 1+2*(87497259105597/5000000000000000000 : ℝ)=(2500087497259105597/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14229618882316877/20000000000000000000 : ℝ)+(87497259105597/5000000000000000000 : ℝ) ≤ ((789819610093012613/790000000000000000 : ℝ)+(11821089837/7900000000000 : ℝ)*((3729/20000 : ℝ)+(7901/100000 : ℝ)))^(4419/1024 : ℝ) := by
    rw [show (789819610093012613/790000000000000000 : ℝ)+(11821089837/7900000000000 : ℝ)*((3729/20000 : ℝ)+(7901/100000 : ℝ))=(2000337753781837/2000000000000000 : ℝ) by norm_num, show 1+(14229618882316877/20000000000000000000 : ℝ)+(87497259105597/5000000000000000000 : ℝ)=(4002915921583747853/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14229618882316877/20000000000000000000 : ℝ) ≤ ((789819610093012613/790000000000000000 : ℝ)+2*(11821089837/7900000000000 : ℝ)*(3729/20000 : ℝ))^(4419/1024 : ℝ) := by
    rw [show (789819610093012613/790000000000000000 : ℝ)+2*(11821089837/7900000000000 : ℝ)*(3729/20000 : ℝ)=(10003296437127017/10000000000000000 : ℝ) by norm_num, show 1+2*(14229618882316877/20000000000000000000 : ℝ)=(10014229618882316877/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (789819610093012613/790000000000000000 : ℝ)*(X 1 0+X 2 0)+(11821089837/7900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (7901/100000 : ℝ)) (hi := (3729/20000 : ℝ)) (c := (789819610093012613/790000000000000000 : ℝ)) (alpha := (11821089837/7900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (789819610093012613/790000000000000000 : ℝ)*(X 0 1+X 2 1)+(11821089837/7900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (7901/100000 : ℝ)) (hi := (3729/20000 : ℝ)) (c := (789819610093012613/790000000000000000 : ℝ)) (alpha := (11821089837/7900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (789819610093012613/790000000000000000 : ℝ)*(X 0 2+X 1 2)+(11821089837/7900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4419/1024 : ℝ)) (lo := (7901/100000 : ℝ)) (hi := (3729/20000 : ℝ)) (c := (789819610093012613/790000000000000000 : ℝ)) (alpha := (11821089837/7900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1940262567/10000000000 : ℝ)*X 0 0+(109029517/200000000 : ℝ)*X 0 1+(5206632471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071642911/2000000000 : ℝ)*X 1 0+(-413214341/2000000000 : ℝ)*X 1 1+(5206628787/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358212413/10000000000 : ℝ)*X 2 0+(2603315299/5000000000 : ℝ)*X 2 1+(-2066072167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((858572639/2000000000 : ℝ)*X 0 0+(252025591/625000000 : ℝ)*X 0 1+(2284058987/5000000000 : ℝ)*X 0 2+(858572639/2000000000 : ℝ)*X 1 0+(252025591/625000000 : ℝ)*X 1 1+(2284058987/5000000000 : ℝ)*X 1 2+(858572639/2000000000 : ℝ)*X 2 0+(252025591/625000000 : ℝ)*X 2 1+(2284058987/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-121268921/625000000 : ℝ)*X 0 0+(5207990043/10000000000 : ℝ)*X 0 1+(2725053719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294364699/10000000000 : ℝ)*X 1 0+(-1822591451/10000000000 : ℝ)*X 1 1+(5450108601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647181937/5000000000 : ℝ)*X 2 0+(5450107637/10000000000 : ℝ)*X 2 1+(-1822593931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4292949677/10000000000 : ℝ)*X 0 0+(4565147329/10000000000 : ℝ)*X 0 1+(2017702597/5000000000 : ℝ)*X 0 2+(4292949677/10000000000 : ℝ)*X 1 0+(4565147329/10000000000 : ℝ)*X 1 1+(2017702597/5000000000 : ℝ)*X 1 2+(4292949677/10000000000 : ℝ)*X 2 0+(4565147329/10000000000 : ℝ)*X 2 1+(2017702597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1460_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18379624114190729121683499/2468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49564207/20000000000000 : ℝ)*(base19) + (10058119/12500000000000 : ℝ)*(upper2) + (167248169/25000000000000 : ℝ)*(lower4) + (90854307/20000000000000 : ℝ)*(upper5) + (185967864662309/6250000000000 : ℝ)*(major0) + (185967864662309/6250000000000 : ℝ)*(major1) + (185967864662309/6250000000000 : ℝ)*(major2) + (510531442753059/12500000000000 : ℝ)*(sp0) + (2042097187895539/50000000000000 : ℝ)*(sp1) + (408419346363741/10000000000000 : ℝ)*(sp2) + (373341895824673/20000000000000 : ℝ)*(sp3) + (28459206179/50000000000000 : ℝ)*(sp5) + (58078387061/100000000000000 : ℝ)*(sp6) + (324996323/3125000000000 : ℝ)*(sp7) + (933359939502851/50000000000000 : ℝ)*(f.failure) + (510531442753059/12500000000000 : ℝ)*(f.sum) + (7895263565957/395000000000000000000000000 : ℝ)*base66 + (41916229990003417/4937500000000000000000000000000 : ℝ)*base67 + (29484092568621583/4937500000000000000000000000000 : ℝ)*base70 + (47805057889690917/4937500000000000000000000000000 : ℝ)*base71 + (46624193301/49375000000000000000000000 : ℝ)*base73 + (53361117723378417/4937500000000000000000000000000 : ℝ)*base75 + (76823930538309083/4937500000000000000000000000000 : ℝ)*base78 + (111709990482315917/4937500000000000000000000000000 : ℝ)*base79 + (458234192093/395000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17873033/5000000000000000000000 : ℝ)*base89 + (17873033/5000000000000000000000 : ℝ)*base91 + (17873033/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4572058378943394111590391/617187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (455963261/50000000000000 : ℝ)*(base19) + (495506663/100000000000000 : ℝ)*(base23) + (6001123/4000000000000 : ℝ)*(upper3) + (164491883/50000000000000 : ℝ)*(lower4) + (188060814865737/6250000000000 : ℝ)*(major0) + (188060814865737/6250000000000 : ℝ)*(major1) + (188060814865737/6250000000000 : ℝ)*(major2) + (2079885319/100000000000000 : ℝ)*(sp0) + (32687426473/100000000000000 : ℝ)*(sp1) + (5131783117/50000000000000 : ℝ)*(sp3) + (826043024650031/20000000000000 : ℝ)*(sp4) + (4130183603782479/100000000000000 : ℝ)*(sp5) + (1032554176907203/25000000000000 : ℝ)*(sp6) + (471929590518033/25000000000000 : ℝ)*(sp7) + (943864312819183/50000000000000 : ℝ)*(f.failure) + (2065108601567737/50000000000000 : ℝ)*(f.sum) + (1527489073291/395000000000000000000000000 : ℝ)*base66 + (77940915503628281/4937500000000000000000000000000 : ℝ)*base67 + (9996507718378281/4937500000000000000000000000000 : ℝ)*base69 + (42149543925065781/4937500000000000000000000000000 : ℝ)*base71 + (272133382053/197500000000000000000000000 : ℝ)*base74 + (70051646137815781/4937500000000000000000000000000 : ℝ)*base75 + (5453458187934219/4937500000000000000000000000000 : ℝ)*base78 + (67541629885440781/4937500000000000000000000000000 : ℝ)*base79 + (55040372821/24687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14866611/5000000000000000000000 : ℝ)*base90 + (14866611/5000000000000000000000 : ℝ)*base92 + (14866611/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1460_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3729/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15709/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1460_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1460_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15709/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1460_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1460_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1460_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4419/1024 : ℝ) ≤ p) (hpb : p ≤ (1105/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159396483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15709/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1460_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1181_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:24.907554+00:00
-- url     : https://prove2.me/submissions/ddfb0998-ea20-4823-9cd2-07d2706ac96e

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
theorem support_rectangle_w1181_s0_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-939764241/5000000000 : ℝ)*x 0 + (6045360057/10000000000 : ℝ)*x 1 + (4785384857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939764241/5000000000 : ℝ)^4187 ≤ (5470123452821/50000000000000 : ℝ)^3163 := by
    have hnat : (939764241 : ℕ)^4187*50000000000000^3163 ≤ 5470123452821^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939764241 5000000000 5470123452821 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6045360057/10000000000 : ℝ)^4187 ≤ (10272805479159/20000000000000 : ℝ)^3163 := by
    have hnat : (6045360057 : ℕ)^4187*20000000000000^3163 ≤ 10272805479159^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6045360057 10000000000 10272805479159 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4785384857/10000000000 : ℝ)^4187 ≤ (37695725682353/100000000000000 : ℝ)^3163 := by
    have hnat : (4785384857 : ℕ)^4187*100000000000000^3163 ≤ 37695725682353^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785384857 10000000000 37695725682353 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-939764241/5000000000 : ℝ), (6045360057/10000000000 : ℝ), (4785384857/10000000000 : ℝ)] ![(5470123452821/50000000000000 : ℝ), (10272805479159/20000000000000 : ℝ), (37695725682353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-939764241/5000000000 : ℝ)|^4187 ≤ (5470123452821/50000000000000 : ℝ)^3163
        have hw : |(-939764241/5000000000 : ℝ)|=(939764241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6045360057/10000000000 : ℝ)|^4187 ≤ (10272805479159/20000000000000 : ℝ)^3163
        have hw : |(6045360057/10000000000 : ℝ)|=(6045360057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4785384857/10000000000 : ℝ)|^4187 ≤ (37695725682353/100000000000000 : ℝ)^3163
        have hw : |(4785384857/10000000000 : ℝ)|=(4785384857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s0_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5514596387/10000000000 : ℝ)*x 0 + (-1300755901/5000000000 : ℝ)*x 1 + (598173107/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514596387/10000000000 : ℝ)^4187 ≤ (45481055945361/100000000000000 : ℝ)^3163 := by
    have hnat : (5514596387 : ℕ)^4187*100000000000000^3163 ≤ 45481055945361^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514596387 10000000000 45481055945361 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300755901/5000000000 : ℝ)^4187 ≤ (262862786921/1562500000000 : ℝ)^3163 := by
    have hnat : (1300755901 : ℕ)^4187*1562500000000^3163 ≤ 262862786921^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300755901 5000000000 262862786921 1562500000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598173107/1250000000 : ℝ)^4187 ≤ (1507829026877/4000000000000 : ℝ)^3163 := by
    have hnat : (598173107 : ℕ)^4187*4000000000000^3163 ≤ 1507829026877^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598173107 1250000000 1507829026877 4000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5514596387/10000000000 : ℝ), (-1300755901/5000000000 : ℝ), (598173107/1250000000 : ℝ)] ![(45481055945361/100000000000000 : ℝ), (262862786921/1562500000000 : ℝ), (1507829026877/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5514596387/10000000000 : ℝ)|^4187 ≤ (45481055945361/100000000000000 : ℝ)^3163
        have hw : |(5514596387/10000000000 : ℝ)|=(5514596387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1300755901/5000000000 : ℝ)|^4187 ≤ (262862786921/1562500000000 : ℝ)^3163
        have hw : |(-1300755901/5000000000 : ℝ)|=(1300755901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598173107/1250000000 : ℝ)|^4187 ≤ (1507829026877/4000000000000 : ℝ)^3163
        have hw : |(598173107/1250000000 : ℝ)|=(598173107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s0_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (344662273/625000000 : ℝ)*x 0 + (149543277/312500000 : ℝ)*x 1 + (-2601511817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344662273/625000000 : ℝ)^4187 ≤ (4548105573793/10000000000000 : ℝ)^3163 := by
    have hnat : (344662273 : ℕ)^4187*10000000000000^3163 ≤ 4548105573793^3163*625000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344662273 625000000 4548105573793 10000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149543277/312500000 : ℝ)^4187 ≤ (7539145151069/20000000000000 : ℝ)^3163 := by
    have hnat : (149543277 : ℕ)^4187*20000000000000^3163 ≤ 7539145151069^3163*312500000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149543277 312500000 7539145151069 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601511817/10000000000 : ℝ)^4187 ≤ (4205804622837/25000000000000 : ℝ)^3163 := by
    have hnat : (2601511817 : ℕ)^4187*25000000000000^3163 ≤ 4205804622837^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601511817 10000000000 4205804622837 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344662273/625000000 : ℝ), (149543277/312500000 : ℝ), (-2601511817/10000000000 : ℝ)] ![(4548105573793/10000000000000 : ℝ), (7539145151069/20000000000000 : ℝ), (4205804622837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344662273/625000000 : ℝ)|^4187 ≤ (4548105573793/10000000000000 : ℝ)^3163
        have hw : |(344662273/625000000 : ℝ)|=(344662273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149543277/312500000 : ℝ)|^4187 ≤ (7539145151069/20000000000000 : ℝ)^3163
        have hw : |(149543277/312500000 : ℝ)|=(149543277/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2601511817/10000000000 : ℝ)|^4187 ≤ (4205804622837/25000000000000 : ℝ)^3163
        have hw : |(-2601511817/10000000000 : ℝ)|=(2601511817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s0_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4197854931/10000000000 : ℝ)*x 0 + (1559670161/5000000000 : ℝ)*x 1 + (5645217977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197854931/10000000000 : ℝ)^4187 ≤ (31694586345851/100000000000000 : ℝ)^3163 := by
    have hnat : (4197854931 : ℕ)^4187*100000000000000^3163 ≤ 31694586345851^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197854931 10000000000 31694586345851 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559670161/5000000000 : ℝ)^4187 ≤ (21392866276007/100000000000000 : ℝ)^3163 := by
    have hnat : (1559670161 : ℕ)^4187*100000000000000^3163 ≤ 21392866276007^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559670161 5000000000 21392866276007 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5645217977/10000000000 : ℝ)^4187 ≤ (5864068420607/12500000000000 : ℝ)^3163 := by
    have hnat : (5645217977 : ℕ)^4187*12500000000000^3163 ≤ 5864068420607^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5645217977 10000000000 5864068420607 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197854931/10000000000 : ℝ), (1559670161/5000000000 : ℝ), (5645217977/10000000000 : ℝ)] ![(31694586345851/100000000000000 : ℝ), (21392866276007/100000000000000 : ℝ), (5864068420607/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197854931/10000000000 : ℝ)|^4187 ≤ (31694586345851/100000000000000 : ℝ)^3163
        have hw : |(4197854931/10000000000 : ℝ)|=(4197854931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1559670161/5000000000 : ℝ)|^4187 ≤ (21392866276007/100000000000000 : ℝ)^3163
        have hw : |(1559670161/5000000000 : ℝ)|=(1559670161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5645217977/10000000000 : ℝ)|^4187 ≤ (5864068420607/12500000000000 : ℝ)^3163
        have hw : |(5645217977/10000000000 : ℝ)|=(5645217977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s0_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1884560301/10000000000 : ℝ)*x 0 + (963573601/2000000000 : ℝ)*x 1 + (3005866033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1884560301/10000000000 : ℝ)^4187 ≤ (686189668517/6250000000000 : ℝ)^3163 := by
    have hnat : (1884560301 : ℕ)^4187*6250000000000^3163 ≤ 686189668517^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884560301 10000000000 686189668517 6250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963573601/2000000000 : ℝ)^4187 ≤ (38034814387117/100000000000000 : ℝ)^3163 := by
    have hnat : (963573601 : ℕ)^4187*100000000000000^3163 ≤ 38034814387117^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963573601 2000000000 38034814387117 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005866033/5000000000 : ℝ)^4187 ≤ (50986150909207/100000000000000 : ℝ)^3163 := by
    have hnat : (3005866033 : ℕ)^4187*100000000000000^3163 ≤ 50986150909207^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005866033 5000000000 50986150909207 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1884560301/10000000000 : ℝ), (963573601/2000000000 : ℝ), (3005866033/5000000000 : ℝ)] ![(686189668517/6250000000000 : ℝ), (38034814387117/100000000000000 : ℝ), (50986150909207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1884560301/10000000000 : ℝ)|^4187 ≤ (686189668517/6250000000000 : ℝ)^3163
        have hw : |(-1884560301/10000000000 : ℝ)|=(1884560301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(963573601/2000000000 : ℝ)|^4187 ≤ (38034814387117/100000000000000 : ℝ)^3163
        have hw : |(963573601/2000000000 : ℝ)|=(963573601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3005866033/5000000000 : ℝ)|^4187 ≤ (50986150909207/100000000000000 : ℝ)^3163
        have hw : |(3005866033/5000000000 : ℝ)|=(3005866033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s0_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2586023811/5000000000 : ℝ)*x 0 + (-137516481/1000000000 : ℝ)*x 1 + (3005865889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586023811/5000000000 : ℝ)^4187 ≤ (20889723051749/50000000000000 : ℝ)^3163 := by
    have hnat : (2586023811 : ℕ)^4187*50000000000000^3163 ≤ 20889723051749^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586023811 5000000000 20889723051749 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137516481/1000000000 : ℝ)^4187 ≤ (7234406192867/100000000000000 : ℝ)^3163 := by
    have hnat : (137516481 : ℕ)^4187*100000000000000^3163 ≤ 7234406192867^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137516481 1000000000 7234406192867 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005865889/5000000000 : ℝ)^4187 ≤ (25493073837943/50000000000000 : ℝ)^3163 := by
    have hnat : (3005865889 : ℕ)^4187*50000000000000^3163 ≤ 25493073837943^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005865889 5000000000 25493073837943 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586023811/5000000000 : ℝ), (-137516481/1000000000 : ℝ), (3005865889/5000000000 : ℝ)] ![(20889723051749/50000000000000 : ℝ), (7234406192867/100000000000000 : ℝ), (25493073837943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586023811/5000000000 : ℝ)|^4187 ≤ (20889723051749/50000000000000 : ℝ)^3163
        have hw : |(2586023811/5000000000 : ℝ)|=(2586023811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137516481/1000000000 : ℝ)|^4187 ≤ (7234406192867/100000000000000 : ℝ)^3163
        have hw : |(-137516481/1000000000 : ℝ)|=(137516481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3005865889/5000000000 : ℝ)|^4187 ≤ (25493073837943/50000000000000 : ℝ)^3163
        have hw : |(3005865889/5000000000 : ℝ)|=(3005865889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s0_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5172047569/10000000000 : ℝ)*x 0 + (751466491/1250000000 : ℝ)*x 1 + (-343791163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172047569/10000000000 : ℝ)^4187 ≤ (41779445536763/100000000000000 : ℝ)^3163 := by
    have hnat : (5172047569 : ℕ)^4187*100000000000000^3163 ≤ 41779445536763^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172047569 10000000000 41779445536763 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (751466491/1250000000 : ℝ)^4187 ≤ (50986149359907/100000000000000 : ℝ)^3163 := by
    have hnat : (751466491 : ℕ)^4187*100000000000000^3163 ≤ 50986149359907^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751466491 1250000000 50986149359907 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343791163/2500000000 : ℝ)^4187 ≤ (1808601273143/25000000000000 : ℝ)^3163 := by
    have hnat : (343791163 : ℕ)^4187*25000000000000^3163 ≤ 1808601273143^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343791163 2500000000 1808601273143 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172047569/10000000000 : ℝ), (751466491/1250000000 : ℝ), (-343791163/2500000000 : ℝ)] ![(41779445536763/100000000000000 : ℝ), (50986149359907/100000000000000 : ℝ), (1808601273143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172047569/10000000000 : ℝ)|^4187 ≤ (41779445536763/100000000000000 : ℝ)^3163
        have hw : |(5172047569/10000000000 : ℝ)|=(5172047569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(751466491/1250000000 : ℝ)|^4187 ≤ (50986149359907/100000000000000 : ℝ)^3163
        have hw : |(751466491/1250000000 : ℝ)|=(751466491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343791163/2500000000 : ℝ)|^4187 ≤ (1808601273143/25000000000000 : ℝ)^3163
        have hw : |(-343791163/2500000000 : ℝ)|=(343791163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s0_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4207942327/10000000000 : ℝ)*x 0 + (1395024623/2500000000 : ℝ)*x 1 + (398344353/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4207942327/10000000000 : ℝ)^4187 ≤ (15897722051571/50000000000000 : ℝ)^3163 := by
    have hnat : (4207942327 : ℕ)^4187*50000000000000^3163 ≤ 15897722051571^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4207942327 10000000000 15897722051571 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1395024623/2500000000 : ℝ)^4187 ≤ (23098771073041/50000000000000 : ℝ)^3163 := by
    have hnat : (1395024623 : ℕ)^4187*50000000000000^3163 ≤ 23098771073041^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395024623 2500000000 23098771073041 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398344353/1250000000 : ℝ)^4187 ≤ (2750876717559/12500000000000 : ℝ)^3163 := by
    have hnat : (398344353 : ℕ)^4187*12500000000000^3163 ≤ 2750876717559^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398344353 1250000000 2750876717559 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4207942327/10000000000 : ℝ), (1395024623/2500000000 : ℝ), (398344353/1250000000 : ℝ)] ![(15897722051571/50000000000000 : ℝ), (23098771073041/50000000000000 : ℝ), (2750876717559/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4207942327/10000000000 : ℝ)|^4187 ≤ (15897722051571/50000000000000 : ℝ)^3163
        have hw : |(4207942327/10000000000 : ℝ)|=(4207942327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1395024623/2500000000 : ℝ)|^4187 ≤ (23098771073041/50000000000000 : ℝ)^3163
        have hw : |(1395024623/2500000000 : ℝ)|=(1395024623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398344353/1250000000 : ℝ)|^4187 ≤ (2750876717559/12500000000000 : ℝ)^3163
        have hw : |(398344353/1250000000 : ℝ)|=(398344353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (573/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13833/50000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8373/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8373 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8373*1^2048 ≤ 0^2048*1^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8373/2048 : ℝ) ≤ (2360861242672668909/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8373 ≤ (2360861242672668909/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8373*100000000000000000000^2048 ≤ 2360861242672668909^2048*5^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2360861242672668909 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2360861242672668909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8373 := by
      have hnat : (1 : ℕ)^2048*1^8373 ≤ 1^8373*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102360861242672668909/100000000000000000000 : ℝ) ≤ (2514309434186671/2500000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (102360861242672668909/100000000000000000000 : ℝ)^2048 ≤ (2514309434186671/2500000000000000 : ℝ)^8373 := by
      have hnat : (102360861242672668909 : ℕ)^2048*2500000000000000^8373 ≤ 2514309434186671^8373*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102360861242672668909 100000000000000000000 2514309434186671 2500000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514309434186671/2500000000000000 : ℝ)) (X := (102360861242672668909/100000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52360861242672668909/50000000000000000000 : ℝ) ≤ (1264309434186671/1250000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (52360861242672668909/50000000000000000000 : ℝ)^2048 ≤ (1264309434186671/1250000000000000 : ℝ)^8373 := by
      have hnat : (52360861242672668909 : ℕ)^2048*1250000000000000^8373 ≤ 1264309434186671^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52360861242672668909 50000000000000000000 1264309434186671 1250000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264309434186671/1250000000000000 : ℝ)) (X := (52360861242672668909/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14309434186671/1000000000000000 : ℝ)*(0 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(14309434186671/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2360861242672668909/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14309434186671/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (1 : ℝ)+(14309434186671/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514309434186671/2500000000000000 : ℝ) by norm_num, show 1+(2360861242672668909/100000000000000000000 : ℝ)+(0 : ℝ)=(102360861242672668909/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2360861242672668909/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14309434186671/1000000000000000 : ℝ)*(2/5 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(14309434186671/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264309434186671/1250000000000000 : ℝ) by norm_num, show 1+2*(2360861242672668909/100000000000000000000 : ℝ)=(52360861242672668909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14309434186671/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14309434186671/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14309434186671/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14309434186671/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14309434186671/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14309434186671/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-939764241/5000000000 : ℝ)*X 0 0+(6045360057/10000000000 : ℝ)*X 0 1+(4785384857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5514596387/10000000000 : ℝ)*X 1 0+(-1300755901/5000000000 : ℝ)*X 1 1+(598173107/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344662273/625000000 : ℝ)*X 2 0+(149543277/312500000 : ℝ)*X 2 1+(-2601511817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4197854931/10000000000 : ℝ)*X 0 0+(1559670161/5000000000 : ℝ)*X 0 1+(5645217977/10000000000 : ℝ)*X 0 2+(4197854931/10000000000 : ℝ)*X 1 0+(1559670161/5000000000 : ℝ)*X 1 1+(5645217977/10000000000 : ℝ)*X 1 2+(4197854931/10000000000 : ℝ)*X 2 0+(1559670161/5000000000 : ℝ)*X 2 1+(5645217977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1884560301/10000000000 : ℝ)*X 0 0+(963573601/2000000000 : ℝ)*X 0 1+(3005866033/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586023811/5000000000 : ℝ)*X 1 0+(-137516481/1000000000 : ℝ)*X 1 1+(3005865889/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5172047569/10000000000 : ℝ)*X 2 0+(751466491/1250000000 : ℝ)*X 2 1+(-343791163/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4207942327/10000000000 : ℝ)*X 0 0+(1395024623/2500000000 : ℝ)*X 0 1+(398344353/1250000000 : ℝ)*X 0 2+(4207942327/10000000000 : ℝ)*X 1 0+(1395024623/2500000000 : ℝ)*X 1 1+(398344353/1250000000 : ℝ)*X 1 2+(4207942327/10000000000 : ℝ)*X 2 0+(1395024623/2500000000 : ℝ)*X 2 1+(398344353/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43205356678068908579841/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5694179/12500000000000 : ℝ)*(base1) + (106255487/10000000000000 : ℝ)*(base19) + (246933503/25000000000000 : ℝ)*(base23) + (36043171/50000000000000 : ℝ)*(base24) + (244775979/100000000000000 : ℝ)*(upper3) + (594788721740757/100000000000000 : ℝ)*(major0) + (594788721740757/100000000000000 : ℝ)*(major1) + (594788721740757/100000000000000 : ℝ)*(major2) + (31746800004443/4000000000000 : ℝ)*(sp0) + (396835617884249/50000000000000 : ℝ)*(sp1) + (396835619251507/50000000000000 : ℝ)*(sp2) + (395903087669673/100000000000000 : ℝ)*(sp3) + (1171882863/50000000000000 : ℝ)*(sp4) + (1867917179/100000000000000 : ℝ)*(sp7) + (395905001140283/100000000000000 : ℝ)*(f.failure) + (99209037290421/12500000000000 : ℝ)*(f.sum) + (79950464150053/50000000000000000000000000000 : ℝ)*base66 + (527480061050053/100000000000000000000000000000 : ℝ)*base68 + (754821813950053/100000000000000000000000000000 : ℝ)*base70 + (185718375350053/100000000000000000000000000000 : ℝ)*base72 + (148994162050053/50000000000000000000000000000 : ℝ)*base74 + (340967676349947/100000000000000000000000000000 : ℝ)*base75 + (37942017950053/100000000000000000000000000000 : ℝ)*base78 + (160945280150053/100000000000000000000000000000 : ℝ)*base80 + (454968222100053/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (40614721/10000000000000000000000 : ℝ)*base90 + (40614721/10000000000000000000000 : ℝ)*base92 + (40614721/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1076380893742555543389/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (8265659/20000000000000 : ℝ)*(base1) + (882656581/100000000000000 : ℝ)*(base19) + (109581389/12500000000000 : ℝ)*(base23) + (87956101/100000000000000 : ℝ)*(upper3) + (27418573/25000000000000 : ℝ)*(upper5) + (31386049715969/5000000000000 : ℝ)*(major0) + (31386049715969/5000000000000 : ℝ)*(major1) + (31386049715969/5000000000000 : ℝ)*(major2) + (350801553/20000000000000 : ℝ)*(sp1) + (358586131/20000000000000 : ℝ)*(sp2) + (167523287766383/20000000000000 : ℝ)*(sp4) + (418806880419637/50000000000000 : ℝ)*(sp5) + (837613727921853/100000000000000 : ℝ)*(sp6) + (208912717496439/50000000000000 : ℝ)*(sp7) + (208912738160587/50000000000000 : ℝ)*(f.failure) + (41880819875181/5000000000000 : ℝ)*(f.sum) + (1290723921699/2500000000000000000000000000 : ℝ)*base65 + (35388477894199/5000000000000000000000000000 : ℝ)*base67 + (15628926339199/5000000000000000000000000000 : ℝ)*base69 + (13765082704199/5000000000000000000000000000 : ℝ)*base71 + (3836451884199/2500000000000000000000000000 : ℝ)*base73 + (13609078229199/5000000000000000000000000000 : ℝ)*base75 + (24191908134199/5000000000000000000000000000 : ℝ)*base77 + (12607233249199/5000000000000000000000000000 : ℝ)*base79 + (4222307303301/2500000000000000000000000000 : ℝ)*base82 + (16150031/5000000000000000000000 : ℝ)*base89 + (16150031/5000000000000000000000 : ℝ)*base91 + (16150031/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1181_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (573/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13833/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1181_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1181_s1_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-416274627/2000000000 : ℝ)*x 0 + (2845601991/5000000000 : ℝ)*x 1 + (626291469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416274627/2000000000 : ℝ)^4187 ≤ (1252190252607/10000000000000 : ℝ)^3163 := by
    have hnat : (416274627 : ℕ)^4187*10000000000000^3163 ≤ 1252190252607^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416274627 2000000000 1252190252607 10000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2845601991/5000000000 : ℝ)^4187 ≤ (47419081819549/100000000000000 : ℝ)^3163 := by
    have hnat : (2845601991 : ℕ)^4187*100000000000000^3163 ≤ 47419081819549^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2845601991 5000000000 47419081819549 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626291469/1250000000 : ℝ)^4187 ≤ (20029507819737/50000000000000 : ℝ)^3163 := by
    have hnat : (626291469 : ℕ)^4187*50000000000000^3163 ≤ 20029507819737^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626291469 1250000000 20029507819737 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416274627/2000000000 : ℝ), (2845601991/5000000000 : ℝ), (626291469/1250000000 : ℝ)] ![(1252190252607/10000000000000 : ℝ), (47419081819549/100000000000000 : ℝ), (20029507819737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416274627/2000000000 : ℝ)|^4187 ≤ (1252190252607/10000000000000 : ℝ)^3163
        have hw : |(-416274627/2000000000 : ℝ)|=(416274627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2845601991/5000000000 : ℝ)|^4187 ≤ (47419081819549/100000000000000 : ℝ)^3163
        have hw : |(2845601991/5000000000 : ℝ)|=(2845601991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(626291469/1250000000 : ℝ)|^4187 ≤ (20029507819737/50000000000000 : ℝ)^3163
        have hw : |(626291469/1250000000 : ℝ)|=(626291469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s1_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5416982911/10000000000 : ℝ)*x 0 + (-2448084443/10000000000 : ℝ)*x 1 + (5010331951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416982911/10000000000 : ℝ)^4187 ≤ (22209216515271/50000000000000 : ℝ)^3163 := by
    have hnat : (5416982911 : ℕ)^4187*50000000000000^3163 ≤ 22209216515271^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416982911 10000000000 22209216515271 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2448084443/10000000000 : ℝ)^4187 ≤ (3880637301311/25000000000000 : ℝ)^3163 := by
    have hnat : (2448084443 : ℕ)^4187*25000000000000^3163 ≤ 3880637301311^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2448084443 10000000000 3880637301311 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5010331951/10000000000 : ℝ)^4187 ≤ (40059017745631/100000000000000 : ℝ)^3163 := by
    have hnat : (5010331951 : ℕ)^4187*100000000000000^3163 ≤ 40059017745631^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010331951 10000000000 40059017745631 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416982911/10000000000 : ℝ), (-2448084443/10000000000 : ℝ), (5010331951/10000000000 : ℝ)] ![(22209216515271/50000000000000 : ℝ), (3880637301311/25000000000000 : ℝ), (40059017745631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416982911/10000000000 : ℝ)|^4187 ≤ (22209216515271/50000000000000 : ℝ)^3163
        have hw : |(5416982911/10000000000 : ℝ)|=(5416982911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2448084443/10000000000 : ℝ)|^4187 ≤ (3880637301311/25000000000000 : ℝ)^3163
        have hw : |(-2448084443/10000000000 : ℝ)|=(2448084443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5010331951/10000000000 : ℝ)|^4187 ≤ (40059017745631/100000000000000 : ℝ)^3163
        have hw : |(5010331951/10000000000 : ℝ)|=(5010331951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s1_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2708491061/5000000000 : ℝ)*x 0 + (626291561/1250000000 : ℝ)*x 1 + (-2448084787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708491061/5000000000 : ℝ)^4187 ≤ (11104606116587/25000000000000 : ℝ)^3163 := by
    have hnat : (2708491061 : ℕ)^4187*25000000000000^3163 ≤ 11104606116587^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708491061 5000000000 11104606116587 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626291561/1250000000 : ℝ)^4187 ≤ (20029511714539/50000000000000 : ℝ)^3163 := by
    have hnat : (626291561 : ℕ)^4187*50000000000000^3163 ≤ 20029511714539^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626291561 1250000000 20029511714539 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2448084787/10000000000 : ℝ)^4187 ≤ (1552255209259/10000000000000 : ℝ)^3163 := by
    have hnat : (2448084787 : ℕ)^4187*10000000000000^3163 ≤ 1552255209259^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2448084787 10000000000 1552255209259 10000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708491061/5000000000 : ℝ), (626291561/1250000000 : ℝ), (-2448084787/10000000000 : ℝ)] ![(11104606116587/25000000000000 : ℝ), (20029511714539/50000000000000 : ℝ), (1552255209259/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708491061/5000000000 : ℝ)|^4187 ≤ (11104606116587/25000000000000 : ℝ)^3163
        have hw : |(2708491061/5000000000 : ℝ)|=(2708491061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626291561/1250000000 : ℝ)|^4187 ≤ (20029511714539/50000000000000 : ℝ)^3163
        have hw : |(626291561/1250000000 : ℝ)|=(626291561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2448084787/10000000000 : ℝ)|^4187 ≤ (1552255209259/10000000000000 : ℝ)^3163
        have hw : |(-2448084787/10000000000 : ℝ)|=(2448084787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s1_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (862823499/2000000000 : ℝ)*x 0 + (460539889/1250000000 : ℝ)*x 1 + (315579167/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862823499/2000000000 : ℝ)^4187 ≤ (32861750712503/100000000000000 : ℝ)^3163 := by
    have hnat : (862823499 : ℕ)^4187*100000000000000^3163 ≤ 32861750712503^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862823499 2000000000 32861750712503 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460539889/1250000000 : ℝ)^4187 ≤ (13333320319947/50000000000000 : ℝ)^3163 := by
    have hnat : (460539889 : ℕ)^4187*50000000000000^3163 ≤ 13333320319947^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460539889 1250000000 13333320319947 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315579167/625000000 : ℝ)^4187 ≤ (252947553939/625000000000 : ℝ)^3163 := by
    have hnat : (315579167 : ℕ)^4187*625000000000^3163 ≤ 252947553939^3163*625000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315579167 625000000 252947553939 625000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862823499/2000000000 : ℝ), (460539889/1250000000 : ℝ), (315579167/625000000 : ℝ)] ![(32861750712503/100000000000000 : ℝ), (13333320319947/50000000000000 : ℝ), (252947553939/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862823499/2000000000 : ℝ)|^4187 ≤ (32861750712503/100000000000000 : ℝ)^3163
        have hw : |(862823499/2000000000 : ℝ)|=(862823499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(460539889/1250000000 : ℝ)|^4187 ≤ (13333320319947/50000000000000 : ℝ)^3163
        have hw : |(460539889/1250000000 : ℝ)|=(460539889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315579167/625000000 : ℝ)|^4187 ≤ (252947553939/625000000000 : ℝ)^3163
        have hw : |(315579167/625000000 : ℝ)|=(315579167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s1_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082127283/10000000000 : ℝ)*x 0 + (200779633/400000000 : ℝ)*x 1 + (1136373079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082127283/10000000000 : ℝ)^4187 ≤ (12527908814667/100000000000000 : ℝ)^3163 := by
    have hnat : (2082127283 : ℕ)^4187*100000000000000^3163 ≤ 12527908814667^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082127283 10000000000 12527908814667 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200779633/400000000 : ℝ)^4187 ≤ (20077990600717/50000000000000 : ℝ)^3163 := by
    have hnat : (200779633 : ℕ)^4187*50000000000000^3163 ≤ 20077990600717^3163*400000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200779633 400000000 20077990600717 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136373079/2000000000 : ℝ)^4187 ≤ (5914513746207/12500000000000 : ℝ)^3163 := by
    have hnat : (1136373079 : ℕ)^4187*12500000000000^3163 ≤ 5914513746207^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136373079 2000000000 5914513746207 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082127283/10000000000 : ℝ), (200779633/400000000 : ℝ), (1136373079/2000000000 : ℝ)] ![(12527908814667/100000000000000 : ℝ), (20077990600717/50000000000000 : ℝ), (5914513746207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082127283/10000000000 : ℝ)|^4187 ≤ (12527908814667/100000000000000 : ℝ)^3163
        have hw : |(-2082127283/10000000000 : ℝ)|=(2082127283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200779633/400000000 : ℝ)|^4187 ≤ (20077990600717/50000000000000 : ℝ)^3163
        have hw : |(200779633/400000000 : ℝ)|=(200779633/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136373079/2000000000 : ℝ)|^4187 ≤ (5914513746207/12500000000000 : ℝ)^3163
        have hw : |(1136373079/2000000000 : ℝ)|=(1136373079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s1_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (655260247/1250000000 : ℝ)*x 0 + (-1776549403/10000000000 : ℝ)*x 1 + (5681867237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655260247/1250000000 : ℝ)^4187 ≤ (5316245933909/12500000000000 : ℝ)^3163 := by
    have hnat : (655260247 : ℕ)^4187*12500000000000^3163 ≤ 5316245933909^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655260247 1250000000 5316245933909 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1776549403/10000000000 : ℝ)^4187 ≤ (63461889021/625000000000 : ℝ)^3163 := by
    have hnat : (1776549403 : ℕ)^4187*625000000000^3163 ≤ 63461889021^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776549403 10000000000 63461889021 625000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5681867237/10000000000 : ℝ)^4187 ≤ (23658065137527/50000000000000 : ℝ)^3163 := by
    have hnat : (5681867237 : ℕ)^4187*50000000000000^3163 ≤ 23658065137527^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5681867237 10000000000 23658065137527 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655260247/1250000000 : ℝ), (-1776549403/10000000000 : ℝ), (5681867237/10000000000 : ℝ)] ![(5316245933909/12500000000000 : ℝ), (63461889021/625000000000 : ℝ), (23658065137527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655260247/1250000000 : ℝ)|^4187 ≤ (5316245933909/12500000000000 : ℝ)^3163
        have hw : |(655260247/1250000000 : ℝ)|=(655260247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1776549403/10000000000 : ℝ)|^4187 ≤ (63461889021/625000000000 : ℝ)^3163
        have hw : |(-1776549403/10000000000 : ℝ)|=(1776549403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5681867237/10000000000 : ℝ)|^4187 ≤ (23658065137527/50000000000000 : ℝ)^3163
        have hw : |(5681867237/10000000000 : ℝ)|=(5681867237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s1_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5242081599/10000000000 : ℝ)*x 0 + (710233523/1250000000 : ℝ)*x 1 + (-1776548557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242081599/10000000000 : ℝ)^4187 ≤ (21264981711189/50000000000000 : ℝ)^3163 := by
    have hnat : (5242081599 : ℕ)^4187*50000000000000^3163 ≤ 21264981711189^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242081599 10000000000 21264981711189 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (710233523/1250000000 : ℝ)^4187 ≤ (23658070357183/50000000000000 : ℝ)^3163 := by
    have hnat : (710233523 : ℕ)^4187*50000000000000^3163 ≤ 23658070357183^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710233523 1250000000 23658070357183 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1776548557/10000000000 : ℝ)^4187 ≤ (81231166741/800000000000 : ℝ)^3163 := by
    have hnat : (1776548557 : ℕ)^4187*800000000000^3163 ≤ 81231166741^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776548557 10000000000 81231166741 800000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242081599/10000000000 : ℝ), (710233523/1250000000 : ℝ), (-1776548557/10000000000 : ℝ)] ![(21264981711189/50000000000000 : ℝ), (23658070357183/50000000000000 : ℝ), (81231166741/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242081599/10000000000 : ℝ)|^4187 ≤ (21264981711189/50000000000000 : ℝ)^3163
        have hw : |(5242081599/10000000000 : ℝ)|=(5242081599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(710233523/1250000000 : ℝ)|^4187 ≤ (23658070357183/50000000000000 : ℝ)^3163
        have hw : |(710233523/1250000000 : ℝ)|=(710233523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1776548557/10000000000 : ℝ)|^4187 ≤ (81231166741/800000000000 : ℝ)^3163
        have hw : |(-1776548557/10000000000 : ℝ)|=(1776548557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s1_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2157813147/5000000000 : ℝ)*x 0 + (5030906121/10000000000 : ℝ)*x 1 + (3703036567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157813147/5000000000 : ℝ)^4187 ≤ (16438482619977/50000000000000 : ℝ)^3163 := by
    have hnat : (2157813147 : ℕ)^4187*50000000000000^3163 ≤ 16438482619977^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157813147 5000000000 16438482619977 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5030906121/10000000000 : ℝ)^4187 ≤ (20138456608077/50000000000000 : ℝ)^3163 := by
    have hnat : (5030906121 : ℕ)^4187*50000000000000^3163 ≤ 20138456608077^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030906121 10000000000 20138456608077 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3703036567/10000000000 : ℝ)^4187 ≤ (13423060767463/50000000000000 : ℝ)^3163 := by
    have hnat : (3703036567 : ℕ)^4187*50000000000000^3163 ≤ 13423060767463^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3703036567 10000000000 13423060767463 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157813147/5000000000 : ℝ), (5030906121/10000000000 : ℝ), (3703036567/10000000000 : ℝ)] ![(16438482619977/50000000000000 : ℝ), (20138456608077/50000000000000 : ℝ), (13423060767463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157813147/5000000000 : ℝ)|^4187 ≤ (16438482619977/50000000000000 : ℝ)^3163
        have hw : |(2157813147/5000000000 : ℝ)|=(2157813147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5030906121/10000000000 : ℝ)|^4187 ≤ (20138456608077/50000000000000 : ℝ)^3163
        have hw : |(5030906121/10000000000 : ℝ)|=(5030906121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3703036567/10000000000 : ℝ)|^4187 ≤ (13423060767463/50000000000000 : ℝ)^3163
        have hw : |(3703036567/10000000000 : ℝ)|=(3703036567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13833/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1173/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20263/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13833/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (573/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13833/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (573/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13833/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (573/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13833/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (573/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13833/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (573/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13833/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (573/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (573/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (17077592803/25000000000000000000 : ℝ) := by
    have hpowers : (573/100000 : ℝ)^8373 ≤ (17077592803/25000000000000000000 : ℝ)^2048 := by
      have hnat : (573 : ℕ)^8373*25000000000000000000^2048 ≤ 17077592803^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        573 100000 17077592803 25000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (573/100000 : ℝ)) (X := (17077592803/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13833/50000 : ℝ) ^ (8373/2048 : ℝ) ≤ (522956205990286311/100000000000000000000 : ℝ) := by
    have hpowers : (13833/50000 : ℝ)^8373 ≤ (522956205990286311/100000000000000000000 : ℝ)^2048 := by
      have hnat : (13833 : ℕ)^8373*100000000000000000000^2048 ≤ 522956205990286311^2048*50000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13833 50000 522956205990286311 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13833/50000 : ℝ)) (X := (522956205990286311/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000017077592803/12500000000000000000 : ℝ) ≤ (2000000000668337/2000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (12500000017077592803/12500000000000000000 : ℝ)^2048 ≤ (2000000000668337/2000000000000000 : ℝ)^8373 := by
      have hnat : (12500000017077592803 : ℕ)^2048*2000000000000000^8373 ≤ 2000000000668337^8373*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000017077592803 12500000000000000000 2000000000668337 2000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000668337/2000000000000000 : ℝ)) (X := (12500000017077592803/12500000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100522956274300657523/100000000000000000000 : ℝ) ≤ (2002553219667851/2000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (100522956274300657523/100000000000000000000 : ℝ)^2048 ≤ (2002553219667851/2000000000000000 : ℝ)^8373 := by
      have hnat : (100522956274300657523 : ℕ)^2048*2000000000000000^8373 ≤ 2002553219667851^8373*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100522956274300657523 100000000000000000000 2002553219667851 2000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002553219667851/2000000000000000 : ℝ)) (X := (100522956274300657523/100000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50522956205990286311/50000000000000000000 : ℝ) ≤ (401021287733473/400000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50522956205990286311/50000000000000000000 : ℝ)^2048 ≤ (401021287733473/400000000000000 : ℝ)^8373 := by
      have hnat : (50522956205990286311 : ℕ)^2048*400000000000000^8373 ≤ 401021287733473^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50522956205990286311 50000000000000000000 401021287733473 400000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401021287733473/400000000000000 : ℝ)) (X := (50522956205990286311/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(17077592803/25000000000000000000 : ℝ) ≤ ((18061024676377937099/18062000000000000000 : ℝ)+2*(425536499919/90310000000000 : ℝ)*(573/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (18061024676377937099/18062000000000000000 : ℝ)+2*(425536499919/90310000000000 : ℝ)*(573/100000 : ℝ)=(2000000000668337/2000000000000000 : ℝ) by norm_num, show 1+2*(17077592803/25000000000000000000 : ℝ)=(12500000017077592803/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(522956205990286311/100000000000000000000 : ℝ)+(17077592803/25000000000000000000 : ℝ) ≤ ((18061024676377937099/18062000000000000000 : ℝ)+(425536499919/90310000000000 : ℝ)*((13833/50000 : ℝ)+(573/100000 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (18061024676377937099/18062000000000000000 : ℝ)+(425536499919/90310000000000 : ℝ)*((13833/50000 : ℝ)+(573/100000 : ℝ))=(2002553219667851/2000000000000000 : ℝ) by norm_num, show 1+(522956205990286311/100000000000000000000 : ℝ)+(17077592803/25000000000000000000 : ℝ)=(100522956274300657523/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(522956205990286311/100000000000000000000 : ℝ) ≤ ((18061024676377937099/18062000000000000000 : ℝ)+2*(425536499919/90310000000000 : ℝ)*(13833/50000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (18061024676377937099/18062000000000000000 : ℝ)+2*(425536499919/90310000000000 : ℝ)*(13833/50000 : ℝ)=(401021287733473/400000000000000 : ℝ) by norm_num, show 1+2*(522956205990286311/100000000000000000000 : ℝ)=(50522956205990286311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18061024676377937099/18062000000000000000 : ℝ)*(X 1 0+X 2 0)+(425536499919/90310000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (573/100000 : ℝ)) (hi := (13833/50000 : ℝ)) (c := (18061024676377937099/18062000000000000000 : ℝ)) (alpha := (425536499919/90310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18061024676377937099/18062000000000000000 : ℝ)*(X 0 1+X 2 1)+(425536499919/90310000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (573/100000 : ℝ)) (hi := (13833/50000 : ℝ)) (c := (18061024676377937099/18062000000000000000 : ℝ)) (alpha := (425536499919/90310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18061024676377937099/18062000000000000000 : ℝ)*(X 0 2+X 1 2)+(425536499919/90310000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (573/100000 : ℝ)) (hi := (13833/50000 : ℝ)) (c := (18061024676377937099/18062000000000000000 : ℝ)) (alpha := (425536499919/90310000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416274627/2000000000 : ℝ)*X 0 0+(2845601991/5000000000 : ℝ)*X 0 1+(626291469/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5416982911/10000000000 : ℝ)*X 1 0+(-2448084443/10000000000 : ℝ)*X 1 1+(5010331951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2708491061/5000000000 : ℝ)*X 2 0+(626291561/1250000000 : ℝ)*X 2 1+(-2448084787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862823499/2000000000 : ℝ)*X 0 0+(460539889/1250000000 : ℝ)*X 0 1+(315579167/625000000 : ℝ)*X 0 2+(862823499/2000000000 : ℝ)*X 1 0+(460539889/1250000000 : ℝ)*X 1 1+(315579167/625000000 : ℝ)*X 1 2+(862823499/2000000000 : ℝ)*X 2 0+(460539889/1250000000 : ℝ)*X 2 1+(315579167/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2082127283/10000000000 : ℝ)*X 0 0+(200779633/400000000 : ℝ)*X 0 1+(1136373079/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((655260247/1250000000 : ℝ)*X 1 0+(-1776549403/10000000000 : ℝ)*X 1 1+(5681867237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5242081599/10000000000 : ℝ)*X 2 0+(710233523/1250000000 : ℝ)*X 2 1+(-1776548557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2157813147/5000000000 : ℝ)*X 0 0+(5030906121/10000000000 : ℝ)*X 0 1+(3703036567/10000000000 : ℝ)*X 0 2+(2157813147/5000000000 : ℝ)*X 1 0+(5030906121/10000000000 : ℝ)*X 1 1+(3703036567/10000000000 : ℝ)*X 1 2+(2157813147/5000000000 : ℝ)*X 2 0+(5030906121/10000000000 : ℝ)*X 2 1+(3703036567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1391719211635642550023357167/225775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5259313/20000000000000 : ℝ)*(base1) + (754434081/50000000000000 : ℝ)*(base19) + (64747229/5000000000000 : ℝ)*(base23) + (50820199/20000000000000 : ℝ)*(upper3) + (36660943/50000000000000 : ℝ)*(upper5) + (550339894249289/50000000000000 : ℝ)*(major0) + (550339894249289/50000000000000 : ℝ)*(major1) + (550339894249289/50000000000000 : ℝ)*(major2) + (36717851127933/2500000000000 : ℝ)*(sp0) + (1468720176377737/100000000000000 : ℝ)*(sp1) + (1468720390301319/100000000000000 : ℝ)*(sp2) + (732632919517069/100000000000000 : ℝ)*(sp3) + (958303143/12500000000000 : ℝ)*(sp4) + (2370232367/50000000000000 : ℝ)*(sp7) + (22894927696199/3125000000000 : ℝ)*(f.failure) + (1468721685245899/100000000000000 : ℝ)*(f.sum) + (313189964679/1806200000000000000000000000 : ℝ)*base65 + (1341576913118527389/903100000000000000000000000000000 : ℝ)*base68 + (9049349463081072611/903100000000000000000000000000000 : ℝ)*base69 + (3859955076275872611/903100000000000000000000000000000 : ℝ)*base71 + (41490047564217/9031000000000000000000000000 : ℝ)*base74 + (6228481963843372611/903100000000000000000000000000000 : ℝ)*base75 + (3854386100191772611/903100000000000000000000000000000 : ℝ)*base77 + (8956942331222272611/903100000000000000000000000000000 : ℝ)*base79 + (46364383420081/9031000000000000000000000000 : ℝ)*base81 + (194613/312500000000000000000 : ℝ)*base90 + (194613/312500000000000000000 : ℝ)*base92 + (194613/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (616627100840479803337896201/90310000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1259247737/50000000000000 : ℝ)*(base19) + (371295499/12500000000000 : ℝ)*(base23) + (2087183/1000000000000 : ℝ)*(upper2) + (123136447/25000000000000 : ℝ)*(upper3) + (26454081/10000000000000 : ℝ)*(upper5) + (113140162642233/10000000000000 : ℝ)*(major0) + (113140162642233/10000000000000 : ℝ)*(major1) + (113140162642233/10000000000000 : ℝ)*(major2) + (6500505129/50000000000000 : ℝ)*(sp1) + (279140777/1562500000000 : ℝ)*(sp2) + (1509716179741253/100000000000000 : ℝ)*(sp4) + (1509700660235521/100000000000000 : ℝ)*(sp5) + (377423836091883/25000000000000 : ℝ)*(sp6) + (753086845506939/100000000000000 : ℝ)*(sp7) + (753086845506939/100000000000000 : ℝ)*(f.failure) + (1509716179741253/100000000000000 : ℝ)*(f.sum) + (24482561022937/9031000000000000000000000000 : ℝ)*base66 + (1637032986332977933/180620000000000000000000000000000 : ℝ)*base68 + (153254210324542067/180620000000000000000000000000000 : ℝ)*base69 + (619934177711697933/180620000000000000000000000000000 : ℝ)*base72 + (212627005159/4515500000000000000000000000 : ℝ)*base73 + (15632515793457933/180620000000000000000000000000000 : ℝ)*base76 + (129357786599302067/180620000000000000000000000000000 : ℝ)*base77 + (192134654877717933/180620000000000000000000000000000 : ℝ)*base80 + (11305208651797/9031000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (73643007/10000000000000000000000 : ℝ)*base89 + (73643007/10000000000000000000000 : ℝ)*base91 + (73643007/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1181_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13833/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (573/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1173/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20263/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1181_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1181_s2_0 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213253277/1000000000 : ℝ)*x 0 + (5503549347/10000000000 : ℝ)*x 1 + (5165417749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213253277/1000000000 : ℝ)^4187 ≤ (12930943362859/100000000000000 : ℝ)^3163 := by
    have hnat : (213253277 : ℕ)^4187*100000000000000^3163 ≤ 12930943362859^3163*1000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213253277 1000000000 12930943362859 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503549347/10000000000 : ℝ)^4187 ≤ (45360489740967/100000000000000 : ℝ)^3163 := by
    have hnat : (5503549347 : ℕ)^4187*100000000000000^3163 ≤ 45360489740967^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503549347 10000000000 45360489740967 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5165417749/10000000000 : ℝ)^4187 ≤ (20854283436773/50000000000000 : ℝ)^3163 := by
    have hnat : (5165417749 : ℕ)^4187*50000000000000^3163 ≤ 20854283436773^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5165417749 10000000000 20854283436773 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213253277/1000000000 : ℝ), (5503549347/10000000000 : ℝ), (5165417749/10000000000 : ℝ)] ![(12930943362859/100000000000000 : ℝ), (45360489740967/100000000000000 : ℝ), (20854283436773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213253277/1000000000 : ℝ)|^4187 ≤ (12930943362859/100000000000000 : ℝ)^3163
        have hw : |(-213253277/1000000000 : ℝ)|=(213253277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503549347/10000000000 : ℝ)|^4187 ≤ (45360489740967/100000000000000 : ℝ)^3163
        have hw : |(5503549347/10000000000 : ℝ)|=(5503549347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5165417749/10000000000 : ℝ)|^4187 ≤ (20854283436773/50000000000000 : ℝ)^3163
        have hw : |(5165417749/10000000000 : ℝ)|=(5165417749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s2_1 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372207143/10000000000 : ℝ)*x 0 + (-115403261/500000000 : ℝ)*x 1 + (5165421229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372207143/10000000000 : ℝ)^4187 ≤ (43933066285333/100000000000000 : ℝ)^3163 := by
    have hnat : (5372207143 : ℕ)^4187*100000000000000^3163 ≤ 43933066285333^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372207143 10000000000 43933066285333 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115403261/500000000 : ℝ)^4187 ≤ (14358329631503/100000000000000 : ℝ)^3163 := by
    have hnat : (115403261 : ℕ)^4187*100000000000000^3163 ≤ 14358329631503^3163*500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115403261 500000000 14358329631503 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5165421229/10000000000 : ℝ)^4187 ≤ (8341720814023/20000000000000 : ℝ)^3163 := by
    have hnat : (5165421229 : ℕ)^4187*20000000000000^3163 ≤ 8341720814023^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5165421229 10000000000 8341720814023 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372207143/10000000000 : ℝ), (-115403261/500000000 : ℝ), (5165421229/10000000000 : ℝ)] ![(43933066285333/100000000000000 : ℝ), (14358329631503/100000000000000 : ℝ), (8341720814023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372207143/10000000000 : ℝ)|^4187 ≤ (43933066285333/100000000000000 : ℝ)^3163
        have hw : |(5372207143/10000000000 : ℝ)|=(5372207143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115403261/500000000 : ℝ)|^4187 ≤ (14358329631503/100000000000000 : ℝ)^3163
        have hw : |(-115403261/500000000 : ℝ)|=(115403261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5165421229/10000000000 : ℝ)|^4187 ≤ (8341720814023/20000000000000 : ℝ)^3163
        have hw : |(5165421229/10000000000 : ℝ)|=(5165421229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s2_2 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686104147/5000000000 : ℝ)*x 0 + (5165419553/10000000000 : ℝ)*x 1 + (-2308065881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686104147/5000000000 : ℝ)^4187 ≤ (2745817421583/6250000000000 : ℝ)^3163 := by
    have hnat : (2686104147 : ℕ)^4187*6250000000000^3163 ≤ 2745817421583^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686104147 5000000000 2745817421583 6250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5165419553/10000000000 : ℝ)^4187 ≤ (325848329343/781250000000 : ℝ)^3163 := by
    have hnat : (5165419553 : ℕ)^4187*781250000000^3163 ≤ 325848329343^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5165419553 10000000000 325848329343 781250000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2308065881/10000000000 : ℝ)^4187 ≤ (3589583768697/25000000000000 : ℝ)^3163 := by
    have hnat : (2308065881 : ℕ)^4187*25000000000000^3163 ≤ 3589583768697^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2308065881 10000000000 3589583768697 25000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686104147/5000000000 : ℝ), (5165419553/10000000000 : ℝ), (-2308065881/10000000000 : ℝ)] ![(2745817421583/6250000000000 : ℝ), (325848329343/781250000000 : ℝ), (3589583768697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686104147/5000000000 : ℝ)|^4187 ≤ (2745817421583/6250000000000 : ℝ)^3163
        have hw : |(2686104147/5000000000 : ℝ)|=(2686104147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5165419553/10000000000 : ℝ)|^4187 ≤ (325848329343/781250000000 : ℝ)^3163
        have hw : |(5165419553/10000000000 : ℝ)|=(5165419553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2308065881/10000000000 : ℝ)|^4187 ≤ (3589583768697/25000000000000 : ℝ)^3163
        have hw : |(-2308065881/10000000000 : ℝ)|=(2308065881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s2_3 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2174656311/5000000000 : ℝ)*x 0 + (1005839499/2500000000 : ℝ)*x 1 + (587650919/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174656311/5000000000 : ℝ)^4187 ≤ (4152137671069/12500000000000 : ℝ)^3163 := by
    have hnat : (2174656311 : ℕ)^4187*12500000000000^3163 ≤ 4152137671069^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174656311 5000000000 4152137671069 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005839499/2500000000 : ℝ)^4187 ≤ (1198496885371/4000000000000 : ℝ)^3163 := by
    have hnat : (1005839499 : ℕ)^4187*4000000000000^3163 ≤ 1198496885371^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005839499 2500000000 1198496885371 4000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587650919/1250000000 : ℝ)^4187 ≤ (36820476480731/100000000000000 : ℝ)^3163 := by
    have hnat : (587650919 : ℕ)^4187*100000000000000^3163 ≤ 36820476480731^3163*1250000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587650919 1250000000 36820476480731 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174656311/5000000000 : ℝ), (1005839499/2500000000 : ℝ), (587650919/1250000000 : ℝ)] ![(4152137671069/12500000000000 : ℝ), (1198496885371/4000000000000 : ℝ), (36820476480731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174656311/5000000000 : ℝ)|^4187 ≤ (4152137671069/12500000000000 : ℝ)^3163
        have hw : |(2174656311/5000000000 : ℝ)|=(2174656311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005839499/2500000000 : ℝ)|^4187 ≤ (1198496885371/4000000000000 : ℝ)^3163
        have hw : |(1005839499/2500000000 : ℝ)|=(1005839499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(587650919/1250000000 : ℝ)|^4187 ≤ (36820476480731/100000000000000 : ℝ)^3163
        have hw : |(587650919/1250000000 : ℝ)|=(587650919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s2_4 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-533156067/2500000000 : ℝ)*x 0 + (5167687449/10000000000 : ℝ)*x 1 + (5501258137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533156067/2500000000 : ℝ)^4187 ≤ (6465838898521/50000000000000 : ℝ)^3163 := by
    have hnat : (533156067 : ℕ)^4187*50000000000000^3163 ≤ 6465838898521^3163*2500000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533156067 2500000000 6465838898521 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5167687449/10000000000 : ℝ)^4187 ≤ (8346565733717/20000000000000 : ℝ)^3163 := by
    have hnat : (5167687449 : ℕ)^4187*20000000000000^3163 ≤ 8346565733717^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167687449 10000000000 8346565733717 20000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501258137/10000000000 : ℝ)^4187 ≤ (22667746762613/50000000000000 : ℝ)^3163 := by
    have hnat : (5501258137 : ℕ)^4187*50000000000000^3163 ≤ 22667746762613^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501258137 10000000000 22667746762613 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533156067/2500000000 : ℝ), (5167687449/10000000000 : ℝ), (5501258137/10000000000 : ℝ)] ![(6465838898521/50000000000000 : ℝ), (8346565733717/20000000000000 : ℝ), (22667746762613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533156067/2500000000 : ℝ)|^4187 ≤ (6465838898521/50000000000000 : ℝ)^3163
        have hw : |(-533156067/2500000000 : ℝ)|=(533156067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5167687449/10000000000 : ℝ)|^4187 ≤ (8346565733717/20000000000000 : ℝ)^3163
        have hw : |(5167687449/10000000000 : ℝ)|=(5167687449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501258137/10000000000 : ℝ)|^4187 ≤ (22667746762613/50000000000000 : ℝ)^3163
        have hw : |(5501258137/10000000000 : ℝ)|=(5501258137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s2_5 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211447753/400000000 : ℝ)*x 0 + (-986113447/5000000000 : ℝ)*x 1 + (2750629071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211447753/400000000 : ℝ)^4187 ≤ (43004362713491/100000000000000 : ℝ)^3163 := by
    have hnat : (211447753 : ℕ)^4187*100000000000000^3163 ≤ 43004362713491^3163*400000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211447753 400000000 43004362713491 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986113447/5000000000 : ℝ)^4187 ≤ (5830071843479/50000000000000 : ℝ)^3163 := by
    have hnat : (986113447 : ℕ)^4187*50000000000000^3163 ≤ 5830071843479^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986113447 5000000000 5830071843479 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750629071/5000000000 : ℝ)^4187 ≤ (45335493579771/100000000000000 : ℝ)^3163 := by
    have hnat : (2750629071 : ℕ)^4187*100000000000000^3163 ≤ 45335493579771^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750629071 5000000000 45335493579771 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211447753/400000000 : ℝ), (-986113447/5000000000 : ℝ), (2750629071/5000000000 : ℝ)] ![(43004362713491/100000000000000 : ℝ), (5830071843479/50000000000000 : ℝ), (45335493579771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211447753/400000000 : ℝ)|^4187 ≤ (43004362713491/100000000000000 : ℝ)^3163
        have hw : |(211447753/400000000 : ℝ)|=(211447753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-986113447/5000000000 : ℝ)|^4187 ≤ (5830071843479/50000000000000 : ℝ)^3163
        have hw : |(-986113447/5000000000 : ℝ)|=(986113447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750629071/5000000000 : ℝ)|^4187 ≤ (45335493579771/100000000000000 : ℝ)^3163
        have hw : |(2750629071/5000000000 : ℝ)|=(2750629071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s2_6 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643096987/5000000000 : ℝ)*x 0 + (1100251629/2000000000 : ℝ)*x 1 + (-394445337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643096987/5000000000 : ℝ)^4187 ≤ (2687772769879/6250000000000 : ℝ)^3163 := by
    have hnat : (2643096987 : ℕ)^4187*6250000000000^3163 ≤ 2687772769879^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643096987 5000000000 2687772769879 6250000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100251629/2000000000 : ℝ)^4187 ≤ (45335493612497/100000000000000 : ℝ)^3163 := by
    have hnat : (1100251629 : ℕ)^4187*100000000000000^3163 ≤ 45335493612497^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100251629 2000000000 45335493612497 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394445337/2000000000 : ℝ)^4187 ≤ (11660142051283/100000000000000 : ℝ)^3163 := by
    have hnat : (394445337 : ℕ)^4187*100000000000000^3163 ≤ 11660142051283^3163*2000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394445337 2000000000 11660142051283 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643096987/5000000000 : ℝ), (1100251629/2000000000 : ℝ), (-394445337/2000000000 : ℝ)] ![(2687772769879/6250000000000 : ℝ), (45335493612497/100000000000000 : ℝ), (11660142051283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643096987/5000000000 : ℝ)|^4187 ≤ (2687772769879/6250000000000 : ℝ)^3163
        have hw : |(2643096987/5000000000 : ℝ)|=(2643096987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100251629/2000000000 : ℝ)|^4187 ≤ (45335493612497/100000000000000 : ℝ)^3163
        have hw : |(1100251629/2000000000 : ℝ)|=(1100251629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394445337/2000000000 : ℝ)|^4187 ≤ (11660142051283/100000000000000 : ℝ)^3163
        have hw : |(-394445337/2000000000 : ℝ)|=(394445337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1181_s2_7 (p : ℝ) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2174748989/5000000000 : ℝ)*x 0 + (4696659881/10000000000 : ℝ)*x 1 + (4027948883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174748989/5000000000 : ℝ)^4187 ≤ (16609487651771/50000000000000 : ℝ)^3163 := by
    have hnat : (2174748989 : ℕ)^4187*50000000000000^3163 ≤ 16609487651771^3163*5000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174748989 5000000000 16609487651771 50000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4696659881/10000000000 : ℝ)^4187 ≤ (36773336903469/100000000000000 : ℝ)^3163 := by
    have hnat : (4696659881 : ℕ)^4187*100000000000000^3163 ≤ 36773336903469^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696659881 10000000000 36773336903469 100000000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027948883/10000000000 : ℝ)^4187 ≤ (3750960973559/12500000000000 : ℝ)^3163 := by
    have hnat : (4027948883 : ℕ)^4187*12500000000000^3163 ≤ 3750960973559^3163*10000000000^4187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027948883 10000000000 3750960973559 12500000000000 4187 3163 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4187/1024 : ℝ)) 4187 3163 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174748989/5000000000 : ℝ), (4696659881/10000000000 : ℝ), (4027948883/10000000000 : ℝ)] ![(16609487651771/50000000000000 : ℝ), (36773336903469/100000000000000 : ℝ), (3750960973559/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174748989/5000000000 : ℝ)|^4187 ≤ (16609487651771/50000000000000 : ℝ)^3163
        have hw : |(2174748989/5000000000 : ℝ)|=(2174748989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4696659881/10000000000 : ℝ)|^4187 ≤ (36773336903469/100000000000000 : ℝ)^3163
        have hw : |(4696659881/10000000000 : ℝ)|=(4696659881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027948883/10000000000 : ℝ)|^4187 ≤ (3750960973559/12500000000000 : ℝ)^3163
        have hw : |(4027948883/10000000000 : ℝ)|=(4027948883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1181_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20263/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1173/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16389/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20263/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1173/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20263/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1173/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20263/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1173/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20263/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1173/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20263/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1173/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20263/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1173/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1173/20000 : ℝ) ^ (8373/2048 : ℝ) ≤ (920900990966023/100000000000000000000 : ℝ) := by
    have hpowers : (1173/20000 : ℝ)^8373 ≤ (920900990966023/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1173 : ℕ)^8373*100000000000000000000^2048 ≤ 920900990966023^2048*20000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1173 20000 920900990966023 100000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1173/20000 : ℝ)) (X := (920900990966023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20263/100000 : ℝ) ^ (8373/2048 : ℝ) ≤ (73200191509535283/50000000000000000000 : ℝ) := by
    have hpowers : (20263/100000 : ℝ)^8373 ≤ (73200191509535283/50000000000000000000 : ℝ)^2048 := by
      have hnat : (20263 : ℕ)^8373*50000000000000000000^2048 ≤ 73200191509535283^2048*100000^8373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20263 100000 73200191509535283 50000000000000000000 8373 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20263/100000 : ℝ)) (X := (73200191509535283/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000920900990966023/50000000000000000000 : ℝ) ≤ (10000045049375603/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (50000920900990966023/50000000000000000000 : ℝ)^2048 ≤ (10000045049375603/10000000000000000 : ℝ)^8373 := by
      have hnat : (50000920900990966023 : ℕ)^2048*10000000000000000^8373 ≤ 10000045049375603^8373*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000920900990966023 50000000000000000000 10000045049375603 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000045049375603/10000000000000000 : ℝ)) (X := (50000920900990966023/50000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100147321284010036589/100000000000000000000 : ℝ) ≤ (10003601412275293/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (100147321284010036589/100000000000000000000 : ℝ)^2048 ≤ (10003601412275293/10000000000000000 : ℝ)^8373 := by
      have hnat : (100147321284010036589 : ℕ)^2048*10000000000000000^8373 ≤ 10003601412275293^8373*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100147321284010036589 100000000000000000000 10003601412275293 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003601412275293/10000000000000000 : ℝ)) (X := (100147321284010036589/100000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25073200191509535283/25000000000000000000 : ℝ) ≤ (10007157775174983/10000000000000000 : ℝ) ^ (8373/2048 : ℝ) := by
    have hpowers : (25073200191509535283/25000000000000000000 : ℝ)^2048 ≤ (10007157775174983/10000000000000000 : ℝ)^8373 := by
      have hnat : (25073200191509535283 : ℕ)^2048*10000000000000000^8373 ≤ 10007157775174983^8373*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25073200191509535283 25000000000000000000 10007157775174983 10000000000000000 2048 8373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007157775174983/10000000000000000 : ℝ)) (X := (25073200191509535283/25000000000000000000 : ℝ)) (by norm_num) 8373 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(920900990966023/100000000000000000000 : ℝ) ≤ ((3129107227915142789/3130000000000000000 : ℝ)+2*(355636289969/143980000000000 : ℝ)*(1173/20000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (3129107227915142789/3130000000000000000 : ℝ)+2*(355636289969/143980000000000 : ℝ)*(1173/20000 : ℝ)=(10000045049375603/10000000000000000 : ℝ) by norm_num, show 1+2*(920900990966023/100000000000000000000 : ℝ)=(50000920900990966023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73200191509535283/50000000000000000000 : ℝ)+(920900990966023/100000000000000000000 : ℝ) ≤ ((3129107227915142789/3130000000000000000 : ℝ)+(355636289969/143980000000000 : ℝ)*((20263/100000 : ℝ)+(1173/20000 : ℝ)))^(8373/2048 : ℝ) := by
    rw [show (3129107227915142789/3130000000000000000 : ℝ)+(355636289969/143980000000000 : ℝ)*((20263/100000 : ℝ)+(1173/20000 : ℝ))=(10003601412275293/10000000000000000 : ℝ) by norm_num, show 1+(73200191509535283/50000000000000000000 : ℝ)+(920900990966023/100000000000000000000 : ℝ)=(100147321284010036589/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73200191509535283/50000000000000000000 : ℝ) ≤ ((3129107227915142789/3130000000000000000 : ℝ)+2*(355636289969/143980000000000 : ℝ)*(20263/100000 : ℝ))^(8373/2048 : ℝ) := by
    rw [show (3129107227915142789/3130000000000000000 : ℝ)+2*(355636289969/143980000000000 : ℝ)*(20263/100000 : ℝ)=(10007157775174983/10000000000000000 : ℝ) by norm_num, show 1+2*(73200191509535283/50000000000000000000 : ℝ)=(25073200191509535283/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3129107227915142789/3130000000000000000 : ℝ)*(X 1 0+X 2 0)+(355636289969/143980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (1173/20000 : ℝ)) (hi := (20263/100000 : ℝ)) (c := (3129107227915142789/3130000000000000000 : ℝ)) (alpha := (355636289969/143980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3129107227915142789/3130000000000000000 : ℝ)*(X 0 1+X 2 1)+(355636289969/143980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (1173/20000 : ℝ)) (hi := (20263/100000 : ℝ)) (c := (3129107227915142789/3130000000000000000 : ℝ)) (alpha := (355636289969/143980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3129107227915142789/3130000000000000000 : ℝ)*(X 0 2+X 1 2)+(355636289969/143980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8373/2048 : ℝ)) (lo := (1173/20000 : ℝ)) (hi := (20263/100000 : ℝ)) (c := (3129107227915142789/3130000000000000000 : ℝ)) (alpha := (355636289969/143980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-213253277/1000000000 : ℝ)*X 0 0+(5503549347/10000000000 : ℝ)*X 0 1+(5165417749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372207143/10000000000 : ℝ)*X 1 0+(-115403261/500000000 : ℝ)*X 1 1+(5165421229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686104147/5000000000 : ℝ)*X 2 0+(5165419553/10000000000 : ℝ)*X 2 1+(-2308065881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174656311/5000000000 : ℝ)*X 0 0+(1005839499/2500000000 : ℝ)*X 0 1+(587650919/1250000000 : ℝ)*X 0 2+(2174656311/5000000000 : ℝ)*X 1 0+(1005839499/2500000000 : ℝ)*X 1 1+(587650919/1250000000 : ℝ)*X 1 2+(2174656311/5000000000 : ℝ)*X 2 0+(1005839499/2500000000 : ℝ)*X 2 1+(587650919/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-533156067/2500000000 : ℝ)*X 0 0+(5167687449/10000000000 : ℝ)*X 0 1+(5501258137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211447753/400000000 : ℝ)*X 1 0+(-986113447/5000000000 : ℝ)*X 1 1+(2750629071/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643096987/5000000000 : ℝ)*X 2 0+(1100251629/2000000000 : ℝ)*X 2 1+(-394445337/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174748989/5000000000 : ℝ)*X 0 0+(4696659881/10000000000 : ℝ)*X 0 1+(4027948883/10000000000 : ℝ)*X 0 2+(2174748989/5000000000 : ℝ)*X 1 0+(4696659881/10000000000 : ℝ)*X 1 1+(4027948883/10000000000 : ℝ)*X 1 2+(2174748989/5000000000 : ℝ)*X 2 0+(4696659881/10000000000 : ℝ)*X 2 1+(4027948883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1181_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5505362273373242918942287101/899875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14438509/2500000000000 : ℝ)*(base19) + (1023449573/100000000000000 : ℝ)*(base23) + (48350729/50000000000000 : ℝ)*(upper2) + (883481/200000000000 : ℝ)*(upper3) + (98778069/50000000000000 : ℝ)*(upper4) + (1108189245449739/50000000000000 : ℝ)*(major0) + (1108189245449739/50000000000000 : ℝ)*(major1) + (1108189245449739/50000000000000 : ℝ)*(major2) + (369682333222327/12500000000000 : ℝ)*(sp0) + (73937097364017/2500000000000 : ℝ)*(sp1) + (2957483448651467/100000000000000 : ℝ)*(sp2) + (1475260517149767/100000000000000 : ℝ)*(sp3) + (1032252897/4000000000000 : ℝ)*(sp4) + (2947154377/25000000000000 : ℝ)*(sp7) + (59010892230691/4000000000000 : ℝ)*(f.failure) + (36968555901263/1250000000000 : ℝ)*(f.sum) + (2864319632813/359950000000000000000000000 : ℝ)*base65 + (2552296076652987633/3599500000000000000000000000000000 : ℝ)*base67 + (31579304324797012367/3599500000000000000000000000000000 : ℝ)*base70 + (186330037093487633/3599500000000000000000000000000000 : ℝ)*base71 + (14917467017031/3599500000000000000000000000 : ℝ)*base73 + (20495388874658487633/3599500000000000000000000000000000 : ℝ)*base75 + (35498396693322487633/3599500000000000000000000000000000 : ℝ)*base77 + (19574955463589987633/3599500000000000000000000000000000 : ℝ)*base79 + (1429125298103/7199000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4477817/400000000000000000000 : ℝ)*base90 + (4477817/400000000000000000000 : ℝ)*base92 + (4477817/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13434225281256798236528953671/3599500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100344551/10000000000000 : ℝ)*(base19) + (9321431/781250000000 : ℝ)*(base23) + (2725771/10000000000000 : ℝ)*(upper2) + (33050571/25000000000000 : ℝ)*(upper3) + (81273941/100000000000000 : ℝ)*(upper5) + (2246639789002677/100000000000000 : ℝ)*(major0) + (2246639789002677/100000000000000 : ℝ)*(major1) + (2246639789002677/100000000000000 : ℝ)*(major2) + (9549899581/100000000000000 : ℝ)*(sp1) + (12845981981/100000000000000 : ℝ)*(sp2) + (2997864534457811/100000000000000 : ℝ)*(sp4) + (37473174763909/1250000000000 : ℝ)*(sp5) + (1498925247666331/50000000000000 : ℝ)*(sp6) + (747707459569641/50000000000000 : ℝ)*(sp7) + (747707459569641/50000000000000 : ℝ)*(f.failure) + (2997864534457811/100000000000000 : ℝ)*(f.sum) + (40104536164139/7199000000000000000000000000 : ℝ)*base66 + (27102723211872838481/7199000000000000000000000000000000 : ℝ)*base68 + (44012602121740838481/7199000000000000000000000000000000 : ℝ)*base70 + (61155240784174838481/7199000000000000000000000000000000 : ℝ)*base72 + (2930547769111/1439800000000000000000000000 : ℝ)*base73 + (87123188618958838481/7199000000000000000000000000000000 : ℝ)*base76 + (95844832572855838481/7199000000000000000000000000000000 : ℝ)*base78 + (66916017696328838481/7199000000000000000000000000000000 : ℝ)*base80 + (908711751661/899875000000000000000000000 : ℝ)*base81 + (53968533/5000000000000000000000 : ℝ)*base89 + (53968533/5000000000000000000000 : ℝ)*base91 + (53968533/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1181_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20263/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1173/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16389/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1181_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1181_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16389/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1181_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1181_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1181_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8373/2048 : ℝ) ≤ p) (hpb : p ≤ (4187/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150235213/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16389/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1181_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

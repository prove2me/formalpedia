-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1148_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:34:29.087691+00:00
-- url     : https://prove2.me/submissions/c453d2c5-bada-4d06-9686-81d4f578733e

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
theorem support_rectangle_w1148_s0_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-75596531/400000000 : ℝ)*x 0 + (378309027/625000000 : ℝ)*x 1 + (597653831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75596531/400000000 : ℝ)^8341 ≤ (2197841735891/20000000000000 : ℝ)^6293 := by
    have hnat : (75596531 : ℕ)^8341*20000000000000^6293 ≤ 2197841735891^6293*400000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75596531 400000000 2197841735891 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378309027/625000000 : ℝ)^8341 ≤ (25702757528661/50000000000000 : ℝ)^6293 := by
    have hnat : (378309027 : ℕ)^8341*50000000000000^6293 ≤ 25702757528661^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378309027 625000000 25702757528661 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (597653831/1250000000 : ℝ)^8341 ≤ (37605276246011/100000000000000 : ℝ)^6293 := by
    have hnat : (597653831 : ℕ)^8341*100000000000000^6293 ≤ 37605276246011^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597653831 1250000000 37605276246011 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-75596531/400000000 : ℝ), (378309027/625000000 : ℝ), (597653831/1250000000 : ℝ)] ![(2197841735891/20000000000000 : ℝ), (25702757528661/50000000000000 : ℝ), (37605276246011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-75596531/400000000 : ℝ)|^8341 ≤ (2197841735891/20000000000000 : ℝ)^6293
        have hw : |(-75596531/400000000 : ℝ)|=(75596531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(378309027/625000000 : ℝ)|^8341 ≤ (25702757528661/50000000000000 : ℝ)^6293
        have hw : |(378309027/625000000 : ℝ)|=(378309027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(597653831/1250000000 : ℝ)|^8341 ≤ (37605276246011/100000000000000 : ℝ)^6293
        have hw : |(597653831/1250000000 : ℝ)|=(597653831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s0_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516455531/10000000000 : ℝ)*x 0 + (-654889243/2500000000 : ℝ)*x 1 + (4781230717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516455531/10000000000 : ℝ)^8341 ≤ (22727713510089/50000000000000 : ℝ)^6293 := by
    have hnat : (5516455531 : ℕ)^8341*50000000000000^6293 ≤ 22727713510089^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516455531 10000000000 22727713510089 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654889243/2500000000 : ℝ)^8341 ≤ (8469648001259/50000000000000 : ℝ)^6293 := by
    have hnat : (654889243 : ℕ)^8341*50000000000000^6293 ≤ 8469648001259^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654889243 2500000000 8469648001259 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4781230717/10000000000 : ℝ)^8341 ≤ (1504211078613/4000000000000 : ℝ)^6293 := by
    have hnat : (4781230717 : ℕ)^8341*4000000000000^6293 ≤ 1504211078613^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4781230717 10000000000 1504211078613 4000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516455531/10000000000 : ℝ), (-654889243/2500000000 : ℝ), (4781230717/10000000000 : ℝ)] ![(22727713510089/50000000000000 : ℝ), (8469648001259/50000000000000 : ℝ), (1504211078613/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516455531/10000000000 : ℝ)|^8341 ≤ (22727713510089/50000000000000 : ℝ)^6293
        have hw : |(5516455531/10000000000 : ℝ)|=(5516455531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-654889243/2500000000 : ℝ)|^8341 ≤ (8469648001259/50000000000000 : ℝ)^6293
        have hw : |(-654889243/2500000000 : ℝ)|=(654889243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4781230717/10000000000 : ℝ)|^8341 ≤ (1504211078613/4000000000000 : ℝ)^6293
        have hw : |(4781230717/10000000000 : ℝ)|=(4781230717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s0_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (110329117/200000000 : ℝ)*x 0 + (2390615289/5000000000 : ℝ)*x 1 + (-1309778367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110329117/200000000 : ℝ)^8341 ≤ (45455430504167/100000000000000 : ℝ)^6293 := by
    have hnat : (110329117 : ℕ)^8341*100000000000000^6293 ≤ 45455430504167^6293*200000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110329117 200000000 45455430504167 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2390615289/5000000000 : ℝ)^8341 ≤ (2350329719767/6250000000000 : ℝ)^6293 := by
    have hnat : (2390615289 : ℕ)^8341*6250000000000^6293 ≤ 2350329719767^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390615289 5000000000 2350329719767 6250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309778367/5000000000 : ℝ)^8341 ≤ (16939293962637/100000000000000 : ℝ)^6293 := by
    have hnat : (1309778367 : ℕ)^8341*100000000000000^6293 ≤ 16939293962637^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309778367 5000000000 16939293962637 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110329117/200000000 : ℝ), (2390615289/5000000000 : ℝ), (-1309778367/5000000000 : ℝ)] ![(45455430504167/100000000000000 : ℝ), (2350329719767/6250000000000 : ℝ), (16939293962637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110329117/200000000 : ℝ)|^8341 ≤ (45455430504167/100000000000000 : ℝ)^6293
        have hw : |(110329117/200000000 : ℝ)|=(110329117/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2390615289/5000000000 : ℝ)|^8341 ≤ (2350329719767/6250000000000 : ℝ)^6293
        have hw : |(2390615289/5000000000 : ℝ)|=(2390615289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1309778367/5000000000 : ℝ)|^8341 ≤ (16939293962637/100000000000000 : ℝ)^6293
        have hw : |(-1309778367/5000000000 : ℝ)|=(1309778367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s0_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4200506039/10000000000 : ℝ)*x 0 + (1560401023/5000000000 : ℝ)*x 1 + (565382173/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200506039/10000000000 : ℝ)^8341 ≤ (15837204727617/50000000000000 : ℝ)^6293 := by
    have hnat : (4200506039 : ℕ)^8341*50000000000000^6293 ≤ 15837204727617^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200506039 10000000000 15837204727617 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560401023/5000000000 : ℝ)^8341 ≤ (21363860461757/100000000000000 : ℝ)^6293 := by
    have hnat : (1560401023 : ℕ)^8341*100000000000000^6293 ≤ 21363860461757^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560401023 5000000000 21363860461757 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565382173/1000000000 : ℝ)^8341 ≤ (11740432516497/25000000000000 : ℝ)^6293 := by
    have hnat : (565382173 : ℕ)^8341*25000000000000^6293 ≤ 11740432516497^6293*1000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565382173 1000000000 11740432516497 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200506039/10000000000 : ℝ), (1560401023/5000000000 : ℝ), (565382173/1000000000 : ℝ)] ![(15837204727617/50000000000000 : ℝ), (21363860461757/100000000000000 : ℝ), (11740432516497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200506039/10000000000 : ℝ)|^8341 ≤ (15837204727617/50000000000000 : ℝ)^6293
        have hw : |(4200506039/10000000000 : ℝ)|=(4200506039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560401023/5000000000 : ℝ)|^8341 ≤ (21363860461757/100000000000000 : ℝ)^6293
        have hw : |(1560401023/5000000000 : ℝ)|=(1560401023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565382173/1000000000 : ℝ)|^8341 ≤ (11740432516497/25000000000000 : ℝ)^6293
        have hw : |(565382173/1000000000 : ℝ)|=(565382173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s0_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-37900823/200000000 : ℝ)*x 0 + (962806859/2000000000 : ℝ)*x 1 + (6018987047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37900823/200000000 : ℝ)^8341 ≤ (11028746611389/100000000000000 : ℝ)^6293 := by
    have hnat : (37900823 : ℕ)^8341*100000000000000^6293 ≤ 11028746611389^6293*200000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37900823 200000000 11028746611389 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962806859/2000000000 : ℝ)^8341 ≤ (37947630275757/100000000000000 : ℝ)^6293 := by
    have hnat : (962806859 : ℕ)^8341*100000000000000^6293 ≤ 37947630275757^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962806859 2000000000 37947630275757 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6018987047/10000000000 : ℝ)^8341 ≤ (12755905773721/25000000000000 : ℝ)^6293 := by
    have hnat : (6018987047 : ℕ)^8341*25000000000000^6293 ≤ 12755905773721^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6018987047 10000000000 12755905773721 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37900823/200000000 : ℝ), (962806859/2000000000 : ℝ), (6018987047/10000000000 : ℝ)] ![(11028746611389/100000000000000 : ℝ), (37947630275757/100000000000000 : ℝ), (12755905773721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37900823/200000000 : ℝ)|^8341 ≤ (11028746611389/100000000000000 : ℝ)^6293
        have hw : |(-37900823/200000000 : ℝ)|=(37900823/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962806859/2000000000 : ℝ)|^8341 ≤ (37947630275757/100000000000000 : ℝ)^6293
        have hw : |(962806859/2000000000 : ℝ)|=(962806859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6018987047/10000000000 : ℝ)|^8341 ≤ (12755905773721/25000000000000 : ℝ)^6293
        have hw : |(6018987047/10000000000 : ℝ)|=(6018987047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s0_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2585436573/5000000000 : ℝ)*x 0 + (-1381800617/10000000000 : ℝ)*x 1 + (1504746723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585436573/5000000000 : ℝ)^8341 ≤ (41720147688587/100000000000000 : ℝ)^6293 := by
    have hnat : (2585436573 : ℕ)^8341*100000000000000^6293 ≤ 41720147688587^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585436573 5000000000 41720147688587 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381800617/10000000000 : ℝ)^8341 ≤ (7256230951589/100000000000000 : ℝ)^6293 := by
    have hnat : (1381800617 : ℕ)^8341*100000000000000^6293 ≤ 7256230951589^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381800617 10000000000 7256230951589 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1504746723/2500000000 : ℝ)^8341 ≤ (25511810676659/50000000000000 : ℝ)^6293 := by
    have hnat : (1504746723 : ℕ)^8341*50000000000000^6293 ≤ 25511810676659^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504746723 2500000000 25511810676659 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585436573/5000000000 : ℝ), (-1381800617/10000000000 : ℝ), (1504746723/2500000000 : ℝ)] ![(41720147688587/100000000000000 : ℝ), (7256230951589/100000000000000 : ℝ), (25511810676659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585436573/5000000000 : ℝ)|^8341 ≤ (41720147688587/100000000000000 : ℝ)^6293
        have hw : |(2585436573/5000000000 : ℝ)|=(2585436573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1381800617/10000000000 : ℝ)|^8341 ≤ (7256230951589/100000000000000 : ℝ)^6293
        have hw : |(-1381800617/10000000000 : ℝ)|=(1381800617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1504746723/2500000000 : ℝ)|^8341 ≤ (25511810676659/50000000000000 : ℝ)^6293
        have hw : |(1504746723/2500000000 : ℝ)|=(1504746723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s0_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170873139/10000000000 : ℝ)*x 0 + (1504746733/2500000000 : ℝ)*x 1 + (-690900281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170873139/10000000000 : ℝ)^8341 ≤ (1303754612929/3125000000000 : ℝ)^6293 := by
    have hnat : (5170873139 : ℕ)^8341*3125000000000^6293 ≤ 1303754612929^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170873139 10000000000 1303754612929 3125000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1504746733/2500000000 : ℝ)^8341 ≤ (10204724360551/20000000000000 : ℝ)^6293 := by
    have hnat : (1504746733 : ℕ)^8341*20000000000000^6293 ≤ 10204724360551^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504746733 2500000000 10204724360551 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690900281/5000000000 : ℝ)^8341 ≤ (3628115284387/50000000000000 : ℝ)^6293 := by
    have hnat : (690900281 : ℕ)^8341*50000000000000^6293 ≤ 3628115284387^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690900281 5000000000 3628115284387 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170873139/10000000000 : ℝ), (1504746733/2500000000 : ℝ), (-690900281/5000000000 : ℝ)] ![(1303754612929/3125000000000 : ℝ), (10204724360551/20000000000000 : ℝ), (3628115284387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170873139/10000000000 : ℝ)|^8341 ≤ (1303754612929/3125000000000 : ℝ)^6293
        have hw : |(5170873139/10000000000 : ℝ)|=(5170873139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1504746733/2500000000 : ℝ)|^8341 ≤ (10204724360551/20000000000000 : ℝ)^6293
        have hw : |(1504746733/2500000000 : ℝ)|=(1504746733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-690900281/5000000000 : ℝ)|^8341 ≤ (3628115284387/50000000000000 : ℝ)^6293
        have hw : |(-690900281/5000000000 : ℝ)|=(690900281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s0_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1052680023/2500000000 : ℝ)*x 0 + (223539309/400000000 : ℝ)*x 1 + (1594219623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052680023/2500000000 : ℝ)^8341 ≤ (1271061425727/4000000000000 : ℝ)^6293 := by
    have hnat : (1052680023 : ℕ)^8341*4000000000000^6293 ≤ 1271061425727^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052680023 2500000000 1271061425727 4000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223539309/400000000 : ℝ)^8341 ≤ (90319814849/195312500000 : ℝ)^6293 := by
    have hnat : (223539309 : ℕ)^8341*195312500000^6293 ≤ 90319814849^6293*400000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223539309 400000000 90319814849 195312500000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594219623/5000000000 : ℝ)^8341 ≤ (1373732445531/6250000000000 : ℝ)^6293 := by
    have hnat : (1594219623 : ℕ)^8341*6250000000000^6293 ≤ 1373732445531^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594219623 5000000000 1373732445531 6250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052680023/2500000000 : ℝ), (223539309/400000000 : ℝ), (1594219623/5000000000 : ℝ)] ![(1271061425727/4000000000000 : ℝ), (90319814849/195312500000 : ℝ), (1373732445531/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052680023/2500000000 : ℝ)|^8341 ≤ (1271061425727/4000000000000 : ℝ)^6293
        have hw : |(1052680023/2500000000 : ℝ)|=(1052680023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223539309/400000000 : ℝ)|^8341 ≤ (90319814849/195312500000 : ℝ)^6293
        have hw : |(223539309/400000000 : ℝ)|=(223539309/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594219623/5000000000 : ℝ)|^8341 ≤ (1373732445531/6250000000000 : ℝ)^6293
        have hw : |(1594219623/5000000000 : ℝ)|=(1594219623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (219/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1737/6250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2085/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2085 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2085*1^512 ≤ 0^512*1^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2085/512 : ℝ) ≤ (2395976653052897831/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2085 ≤ (2395976653052897831/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2085*100000000000000000000^512 ≤ 2395976653052897831^512*5^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2395976653052897831 100000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2395976653052897831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2085 := by
      have hnat : (1 : ℕ)^512*1^2085 ≤ 1^2085*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102395976653052897831/100000000000000000000 : ℝ) ≤ (402332480638989/400000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (102395976653052897831/100000000000000000000 : ℝ)^512 ≤ (402332480638989/400000000000000 : ℝ)^2085 := by
      have hnat : (102395976653052897831 : ℕ)^512*400000000000000^2085 ≤ 402332480638989^2085*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102395976653052897831 100000000000000000000 402332480638989 400000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (402332480638989/400000000000000 : ℝ)) (X := (102395976653052897831/100000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52395976653052897831/50000000000000000000 : ℝ) ≤ (202332480638989/200000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (52395976653052897831/50000000000000000000 : ℝ)^512 ≤ (202332480638989/200000000000000 : ℝ)^2085 := by
      have hnat : (52395976653052897831 : ℕ)^512*200000000000000^2085 ≤ 202332480638989^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52395976653052897831 50000000000000000000 202332480638989 200000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (202332480638989/200000000000000 : ℝ)) (X := (52395976653052897831/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2332480638989/160000000000000 : ℝ)*(0 : ℝ))^(2085/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(2332480638989/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2395976653052897831/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2332480638989/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (1 : ℝ)+(2332480638989/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(402332480638989/400000000000000 : ℝ) by norm_num, show 1+(2395976653052897831/100000000000000000000 : ℝ)+(0 : ℝ)=(102395976653052897831/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2395976653052897831/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2332480638989/160000000000000 : ℝ)*(2/5 : ℝ))^(2085/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(2332480638989/160000000000000 : ℝ)*(2/5 : ℝ)=(202332480638989/200000000000000 : ℝ) by norm_num, show 1+2*(2395976653052897831/100000000000000000000 : ℝ)=(52395976653052897831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2332480638989/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2332480638989/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2332480638989/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2332480638989/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2332480638989/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2332480638989/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-75596531/400000000 : ℝ)*X 0 0+(378309027/625000000 : ℝ)*X 0 1+(597653831/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516455531/10000000000 : ℝ)*X 1 0+(-654889243/2500000000 : ℝ)*X 1 1+(4781230717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((110329117/200000000 : ℝ)*X 2 0+(2390615289/5000000000 : ℝ)*X 2 1+(-1309778367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4200506039/10000000000 : ℝ)*X 0 0+(1560401023/5000000000 : ℝ)*X 0 1+(565382173/1000000000 : ℝ)*X 0 2+(4200506039/10000000000 : ℝ)*X 1 0+(1560401023/5000000000 : ℝ)*X 1 1+(565382173/1000000000 : ℝ)*X 1 2+(4200506039/10000000000 : ℝ)*X 2 0+(1560401023/5000000000 : ℝ)*X 2 1+(565382173/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-37900823/200000000 : ℝ)*X 0 0+(962806859/2000000000 : ℝ)*X 0 1+(6018987047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2585436573/5000000000 : ℝ)*X 1 0+(-1381800617/10000000000 : ℝ)*X 1 1+(1504746723/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5170873139/10000000000 : ℝ)*X 2 0+(1504746733/2500000000 : ℝ)*X 2 1+(-690900281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1052680023/2500000000 : ℝ)*X 0 0+(223539309/400000000 : ℝ)*X 0 1+(1594219623/5000000000 : ℝ)*X 0 2+(1052680023/2500000000 : ℝ)*X 1 0+(223539309/400000000 : ℝ)*X 1 1+(1594219623/5000000000 : ℝ)*X 1 2+(1052680023/2500000000 : ℝ)*X 2 0+(223539309/400000000 : ℝ)*X 2 1+(1594219623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43932951599039929369923/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2694797/5000000000000 : ℝ)*(base1) + (85963321/6250000000000 : ℝ)*(base19) + (1302502791/100000000000000 : ℝ)*(base23) + (118382399/100000000000000 : ℝ)*(base24) + (161114573/50000000000000 : ℝ)*(upper3) + (590568907585669/100000000000000 : ℝ)*(major0) + (590568907585669/100000000000000 : ℝ)*(major1) + (590568907585669/100000000000000 : ℝ)*(major2) + (786345034435129/100000000000000 : ℝ)*(sp0) + (78634663661227/10000000000000 : ℝ)*(sp1) + (98293323892527/12500000000000 : ℝ)*(sp2) + (98696779001257/25000000000000 : ℝ)*(sp3) + (3031486217/100000000000000 : ℝ)*(sp4) + (490038199/20000000000000 : ℝ)*(sp7) + (197394810045981/50000000000000 : ℝ)*(f.failure) + (393174006012703/50000000000000 : ℝ)*(f.sum) + (6869830192641/8000000000000000000000000000 : ℝ)*base65 + (39726619447359/16000000000000000000000000000 : ℝ)*base68 + (89867428967359/16000000000000000000000000000 : ℝ)*base70 + (15022436983359/16000000000000000000000000000 : ℝ)*base72 + (1738361264641/8000000000000000000000000000 : ℝ)*base73 + (5362353751359/16000000000000000000000000000 : ℝ)*base76 + (4505591336641/16000000000000000000000000000 : ℝ)*base77 + (20865197127359/16000000000000000000000000000 : ℝ)*base80 + (16589090279359/8000000000000000000000000000 : ℝ)*base82 + (25930991/5000000000000000000000 : ℝ)*base90 + (25930991/5000000000000000000000 : ℝ)*base92 + (25930991/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36132639581995660477179/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60497059/100000000000000 : ℝ)*(base1) + (1114855337/100000000000000 : ℝ)*(base19) + (278282427/25000000000000 : ℝ)*(base23) + (117847021/100000000000000 : ℝ)*(upper3) + (16645383/12500000000000 : ℝ)*(upper5) + (623283691555921/100000000000000 : ℝ)*(major0) + (623283691555921/100000000000000 : ℝ)*(major1) + (623283691555921/100000000000000 : ℝ)*(major2) + (2235510347/100000000000000 : ℝ)*(sp1) + (1113249173/50000000000000 : ℝ)*(sp2) + (414954077668123/50000000000000 : ℝ)*(sp4) + (414952372236751/50000000000000 : ℝ)*(sp5) + (829904755211133/100000000000000 : ℝ)*(sp6) + (16666363088917/4000000000000 : ℝ)*(sp7) + (26041196107499/6250000000000 : ℝ)*(f.failure) + (829908094839187/100000000000000 : ℝ)*(f.sum) + (4565816803869/8000000000000000000000000000 : ℝ)*base65 + (116005271283869/16000000000000000000000000000 : ℝ)*base67 + (84434615388131/16000000000000000000000000000 : ℝ)*base70 + (72169456019869/16000000000000000000000000000 : ℝ)*base71 + (21631861547869/8000000000000000000000000000 : ℝ)*base73 + (97590040275869/16000000000000000000000000000 : ℝ)*base75 + (40261871411869/16000000000000000000000000000 : ℝ)*base77 + (8981569299869/16000000000000000000000000000 : ℝ)*base79 + (40591860316131/8000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2023289/625000000000000000000 : ℝ)*base90 + (2023289/625000000000000000000 : ℝ)*base92 + (2023289/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1148_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (219/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1737/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1148_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1148_s1_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1047072437/5000000000 : ℝ)*x 0 + (569990627/1000000000 : ℝ)*x 1 + (1250880557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047072437/5000000000 : ℝ)^8341 ≤ (6295127047073/50000000000000 : ℝ)^6293 := by
    have hnat : (1047072437 : ℕ)^8341*50000000000000^6293 ≤ 6295127047073^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047072437 5000000000 6295127047073 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569990627/1000000000 : ℝ)^8341 ≤ (5933720425731/12500000000000 : ℝ)^6293 := by
    have hnat : (569990627 : ℕ)^8341*12500000000000^6293 ≤ 5933720425731^6293*1000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569990627 1000000000 5933720425731 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1250880557/2500000000 : ℝ)^8341 ≤ (39939982492431/100000000000000 : ℝ)^6293 := by
    have hnat : (1250880557 : ℕ)^8341*100000000000000^6293 ≤ 39939982492431^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250880557 2500000000 39939982492431 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1047072437/5000000000 : ℝ), (569990627/1000000000 : ℝ), (1250880557/2500000000 : ℝ)] ![(6295127047073/50000000000000 : ℝ), (5933720425731/12500000000000 : ℝ), (39939982492431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1047072437/5000000000 : ℝ)|^8341 ≤ (6295127047073/50000000000000 : ℝ)^6293
        have hw : |(-1047072437/5000000000 : ℝ)|=(1047072437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569990627/1000000000 : ℝ)|^8341 ≤ (5933720425731/12500000000000 : ℝ)^6293
        have hw : |(569990627/1000000000 : ℝ)|=(569990627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1250880557/2500000000 : ℝ)|^8341 ≤ (39939982492431/100000000000000 : ℝ)^6293
        have hw : |(1250880557/2500000000 : ℝ)|=(1250880557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (541879243/1000000000 : ℝ)*x 0 + (-1234918633/5000000000 : ℝ)*x 1 + (312720089/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541879243/1000000000 : ℝ)^8341 ≤ (44391875413957/100000000000000 : ℝ)^6293 := by
    have hnat : (541879243 : ℕ)^8341*100000000000000^6293 ≤ 44391875413957^6293*1000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541879243 1000000000 44391875413957 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1234918633/5000000000 : ℝ)^8341 ≤ (15668150579071/100000000000000 : ℝ)^6293 := by
    have hnat : (1234918633 : ℕ)^8341*100000000000000^6293 ≤ 15668150579071^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234918633 5000000000 15668150579071 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312720089/625000000 : ℝ)^8341 ≤ (39939973985979/100000000000000 : ℝ)^6293 := by
    have hnat : (312720089 : ℕ)^8341*100000000000000^6293 ≤ 39939973985979^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312720089 625000000 39939973985979 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541879243/1000000000 : ℝ), (-1234918633/5000000000 : ℝ), (312720089/625000000 : ℝ)] ![(44391875413957/100000000000000 : ℝ), (15668150579071/100000000000000 : ℝ), (39939973985979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541879243/1000000000 : ℝ)|^8341 ≤ (44391875413957/100000000000000 : ℝ)^6293
        have hw : |(541879243/1000000000 : ℝ)|=(541879243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1234918633/5000000000 : ℝ)|^8341 ≤ (15668150579071/100000000000000 : ℝ)^6293
        have hw : |(-1234918633/5000000000 : ℝ)|=(1234918633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(312720089/625000000 : ℝ)|^8341 ≤ (39939973985979/100000000000000 : ℝ)^6293
        have hw : |(312720089/625000000 : ℝ)|=(312720089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (338674653/625000000 : ℝ)*x 0 + (1250879907/2500000000 : ℝ)*x 1 + (-2469836921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338674653/625000000 : ℝ)^8341 ≤ (1387246791437/3125000000000 : ℝ)^6293 := by
    have hnat : (338674653 : ℕ)^8341*3125000000000^6293 ≤ 1387246791437^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338674653 625000000 1387246791437 3125000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250879907/2500000000 : ℝ)^8341 ≤ (7987990996801/20000000000000 : ℝ)^6293 := by
    have hnat : (1250879907 : ℕ)^8341*20000000000000^6293 ≤ 7987990996801^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250879907 2500000000 7987990996801 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2469836921/10000000000 : ℝ)^8341 ≤ (15668147678197/100000000000000 : ℝ)^6293 := by
    have hnat : (2469836921 : ℕ)^8341*100000000000000^6293 ≤ 15668147678197^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2469836921 10000000000 15668147678197 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338674653/625000000 : ℝ), (1250879907/2500000000 : ℝ), (-2469836921/10000000000 : ℝ)] ![(1387246791437/3125000000000 : ℝ), (7987990996801/20000000000000 : ℝ), (15668147678197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338674653/625000000 : ℝ)|^8341 ≤ (1387246791437/3125000000000 : ℝ)^6293
        have hw : |(338674653/625000000 : ℝ)|=(338674653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250879907/2500000000 : ℝ)|^8341 ≤ (7987990996801/20000000000000 : ℝ)^6293
        have hw : |(1250879907/2500000000 : ℝ)|=(1250879907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2469836921/10000000000 : ℝ)|^8341 ≤ (15668147678197/100000000000000 : ℝ)^6293
        have hw : |(-2469836921/10000000000 : ℝ)|=(2469836921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4316930551/10000000000 : ℝ)*x 0 + (919541589/2500000000 : ℝ)*x 1 + (1266307977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316930551/10000000000 : ℝ)^8341 ≤ (16421623317961/50000000000000 : ℝ)^6293 := by
    have hnat : (4316930551 : ℕ)^8341*50000000000000^6293 ≤ 16421623317961^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316930551 10000000000 16421623317961 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919541589/2500000000 : ℝ)^8341 ≤ (13281282808069/50000000000000 : ℝ)^6293 := by
    have hnat : (919541589 : ℕ)^8341*50000000000000^6293 ≤ 13281282808069^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919541589 2500000000 13281282808069 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1266307977/2500000000 : ℝ)^8341 ≤ (20297093867999/50000000000000 : ℝ)^6293 := by
    have hnat : (1266307977 : ℕ)^8341*50000000000000^6293 ≤ 20297093867999^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266307977 2500000000 20297093867999 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316930551/10000000000 : ℝ), (919541589/2500000000 : ℝ), (1266307977/2500000000 : ℝ)] ![(16421623317961/50000000000000 : ℝ), (13281282808069/50000000000000 : ℝ), (20297093867999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316930551/10000000000 : ℝ)|^8341 ≤ (16421623317961/50000000000000 : ℝ)^6293
        have hw : |(4316930551/10000000000 : ℝ)|=(4316930551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(919541589/2500000000 : ℝ)|^8341 ≤ (13281282808069/50000000000000 : ℝ)^6293
        have hw : |(919541589/2500000000 : ℝ)|=(919541589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1266307977/2500000000 : ℝ)|^8341 ≤ (20297093867999/50000000000000 : ℝ)^6293
        have hw : |(1266307977/2500000000 : ℝ)|=(1266307977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-261868413/1250000000 : ℝ)*x 0 + (5013009033/10000000000 : ℝ)*x 1 + (5690228573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261868413/1250000000 : ℝ)^8341 ≤ (629832441341/5000000000000 : ℝ)^6293 := by
    have hnat : (261868413 : ℕ)^8341*5000000000000^6293 ≤ 629832441341^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261868413 1250000000 629832441341 5000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5013009033/10000000000 : ℝ)^8341 ≤ (40040385405079/100000000000000 : ℝ)^6293 := by
    have hnat : (5013009033 : ℕ)^8341*100000000000000^6293 ≤ 40040385405079^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013009033 10000000000 40040385405079 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5690228573/10000000000 : ℝ)^8341 ≤ (23681482875699/50000000000000 : ℝ)^6293 := by
    have hnat : (5690228573 : ℕ)^8341*50000000000000^6293 ≤ 23681482875699^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690228573 10000000000 23681482875699 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261868413/1250000000 : ℝ), (5013009033/10000000000 : ℝ), (5690228573/10000000000 : ℝ)] ![(629832441341/5000000000000 : ℝ), (40040385405079/100000000000000 : ℝ), (23681482875699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261868413/1250000000 : ℝ)|^8341 ≤ (629832441341/5000000000000 : ℝ)^6293
        have hw : |(-261868413/1250000000 : ℝ)|=(261868413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5013009033/10000000000 : ℝ)|^8341 ≤ (40040385405079/100000000000000 : ℝ)^6293
        have hw : |(5013009033/10000000000 : ℝ)|=(5013009033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5690228573/10000000000 : ℝ)|^8341 ≤ (23681482875699/50000000000000 : ℝ)^6293
        have hw : |(5690228573/10000000000 : ℝ)|=(5690228573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (524019843/1000000000 : ℝ)*x 0 + (-89156299/500000000 : ℝ)*x 1 + (5690232241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524019843/1000000000 : ℝ)^8341 ≤ (42463128469927/100000000000000 : ℝ)^6293 := by
    have hnat : (524019843 : ℕ)^8341*100000000000000^6293 ≤ 42463128469927^6293*1000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524019843 1000000000 42463128469927 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89156299/500000000 : ℝ)^8341 ≤ (5086932649383/50000000000000 : ℝ)^6293 := by
    have hnat : (89156299 : ℕ)^8341*50000000000000^6293 ≤ 5086932649383^6293*500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89156299 500000000 5086932649383 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5690232241/10000000000 : ℝ)^8341 ≤ (9472601243641/20000000000000 : ℝ)^6293 := by
    have hnat : (5690232241 : ℕ)^8341*20000000000000^6293 ≤ 9472601243641^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690232241 10000000000 9472601243641 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524019843/1000000000 : ℝ), (-89156299/500000000 : ℝ), (5690232241/10000000000 : ℝ)] ![(42463128469927/100000000000000 : ℝ), (5086932649383/50000000000000 : ℝ), (9472601243641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524019843/1000000000 : ℝ)|^8341 ≤ (42463128469927/100000000000000 : ℝ)^6293
        have hw : |(524019843/1000000000 : ℝ)|=(524019843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89156299/500000000 : ℝ)|^8341 ≤ (5086932649383/50000000000000 : ℝ)^6293
        have hw : |(-89156299/500000000 : ℝ)|=(89156299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5690232241/10000000000 : ℝ)|^8341 ≤ (9472601243641/20000000000000 : ℝ)^6293
        have hw : |(5690232241/10000000000 : ℝ)|=(5690232241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048039417/2000000000 : ℝ)*x 0 + (2845117023/5000000000 : ℝ)*x 1 + (-222890657/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048039417/2000000000 : ℝ)^8341 ≤ (849262280479/2000000000000 : ℝ)^6293 := by
    have hnat : (1048039417 : ℕ)^8341*2000000000000^6293 ≤ 849262280479^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048039417 2000000000 849262280479 2000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2845117023/5000000000 : ℝ)^8341 ≤ (5920378266459/12500000000000 : ℝ)^6293 := by
    have hnat : (2845117023 : ℕ)^8341*12500000000000^6293 ≤ 5920378266459^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2845117023 5000000000 5920378266459 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222890657/1250000000 : ℝ)^8341 ≤ (1017385982353/10000000000000 : ℝ)^6293 := by
    have hnat : (222890657 : ℕ)^8341*10000000000000^6293 ≤ 1017385982353^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222890657 1250000000 1017385982353 10000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048039417/2000000000 : ℝ), (2845117023/5000000000 : ℝ), (-222890657/1250000000 : ℝ)] ![(849262280479/2000000000000 : ℝ), (5920378266459/12500000000000 : ℝ), (1017385982353/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048039417/2000000000 : ℝ)|^8341 ≤ (849262280479/2000000000000 : ℝ)^6293
        have hw : |(1048039417/2000000000 : ℝ)|=(1048039417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2845117023/5000000000 : ℝ)|^8341 ≤ (5920378266459/12500000000000 : ℝ)^6293
        have hw : |(2845117023/5000000000 : ℝ)|=(2845117023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222890657/1250000000 : ℝ)|^8341 ≤ (1017385982353/10000000000000 : ℝ)^6293
        have hw : |(-222890657/1250000000 : ℝ)|=(222890657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2159259007/5000000000 : ℝ)*x 0 + (201853457/400000000 : ℝ)*x 1 + (1848717013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159259007/5000000000 : ℝ)^8341 ≤ (8214813879493/25000000000000 : ℝ)^6293 := by
    have hnat : (2159259007 : ℕ)^8341*25000000000000^6293 ≤ 8214813879493^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159259007 5000000000 8214813879493 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201853457/400000000 : ℝ)^8341 ≤ (40393593253531/100000000000000 : ℝ)^6293 := by
    have hnat : (201853457 : ℕ)^8341*100000000000000^6293 ≤ 40393593253531^6293*400000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201853457 400000000 40393593253531 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1848717013/5000000000 : ℝ)^8341 ≤ (3343393903149/12500000000000 : ℝ)^6293 := by
    have hnat : (1848717013 : ℕ)^8341*12500000000000^6293 ≤ 3343393903149^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848717013 5000000000 3343393903149 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159259007/5000000000 : ℝ), (201853457/400000000 : ℝ), (1848717013/5000000000 : ℝ)] ![(8214813879493/25000000000000 : ℝ), (40393593253531/100000000000000 : ℝ), (3343393903149/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159259007/5000000000 : ℝ)|^8341 ≤ (8214813879493/25000000000000 : ℝ)^6293
        have hw : |(2159259007/5000000000 : ℝ)|=(2159259007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201853457/400000000 : ℝ)|^8341 ≤ (40393593253531/100000000000000 : ℝ)^6293
        have hw : |(201853457/400000000 : ℝ)|=(201853457/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1848717013/5000000000 : ℝ)|^8341 ≤ (3343393903149/12500000000000 : ℝ)^6293
        have hw : |(1848717013/5000000000 : ℝ)|=(1848717013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_8 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5920149/10000000000 : ℝ)*x 0 + (549036211/1000000000 : ℝ)*x 1 + (6354226511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5920149/10000000000 : ℝ)^8341 ≤ (5271296589/100000000000000 : ℝ)^6293 := by
    have hnat : (5920149 : ℕ)^8341*100000000000000^6293 ≤ 5271296589^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920149 10000000000 5271296589 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549036211/1000000000 : ℝ)^8341 ≤ (45170664861851/100000000000000 : ℝ)^6293 := by
    have hnat : (549036211 : ℕ)^8341*100000000000000^6293 ≤ 45170664861851^6293*1000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549036211 1000000000 45170664861851 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6354226511/10000000000 : ℝ)^8341 ≤ (1713251994771/3125000000000 : ℝ)^6293 := by
    have hnat : (6354226511 : ℕ)^8341*3125000000000^6293 ≤ 1713251994771^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6354226511 10000000000 1713251994771 3125000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5920149/10000000000 : ℝ), (549036211/1000000000 : ℝ), (6354226511/10000000000 : ℝ)] ![(5271296589/100000000000000 : ℝ), (45170664861851/100000000000000 : ℝ), (1713251994771/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5920149/10000000000 : ℝ)|^8341 ≤ (5271296589/100000000000000 : ℝ)^6293
        have hw : |(5920149/10000000000 : ℝ)|=(5920149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(549036211/1000000000 : ℝ)|^8341 ≤ (45170664861851/100000000000000 : ℝ)^6293
        have hw : |(549036211/1000000000 : ℝ)|=(549036211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6354226511/10000000000 : ℝ)|^8341 ≤ (1713251994771/3125000000000 : ℝ)^6293
        have hw : |(6354226511/10000000000 : ℝ)|=(6354226511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_9 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (490544991/5000000000 : ℝ)*x 0 + (-1101404781/2500000000 : ℝ)*x 1 + (1735625971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490544991/5000000000 : ℝ)^8341 ≤ (4608606119867/100000000000000 : ℝ)^6293 := by
    have hnat : (490544991 : ℕ)^8341*100000000000000^6293 ≤ 4608606119867^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490544991 5000000000 4608606119867 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101404781/2500000000 : ℝ)^8341 ≤ (16870277657749/50000000000000 : ℝ)^6293 := by
    have hnat : (1101404781 : ℕ)^8341*50000000000000^6293 ≤ 16870277657749^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101404781 2500000000 16870277657749 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1735625971/2500000000 : ℝ)^8341 ≤ (30825419274839/50000000000000 : ℝ)^6293 := by
    have hnat : (1735625971 : ℕ)^8341*50000000000000^6293 ≤ 30825419274839^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735625971 2500000000 30825419274839 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(490544991/5000000000 : ℝ), (-1101404781/2500000000 : ℝ), (1735625971/2500000000 : ℝ)] ![(4608606119867/100000000000000 : ℝ), (16870277657749/50000000000000 : ℝ), (30825419274839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(490544991/5000000000 : ℝ)|^8341 ≤ (4608606119867/100000000000000 : ℝ)^6293
        have hw : |(490544991/5000000000 : ℝ)|=(490544991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101404781/2500000000 : ℝ)|^8341 ≤ (16870277657749/50000000000000 : ℝ)^6293
        have hw : |(-1101404781/2500000000 : ℝ)|=(1101404781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1735625971/2500000000 : ℝ)|^8341 ≤ (30825419274839/50000000000000 : ℝ)^6293
        have hw : |(1735625971/2500000000 : ℝ)|=(1735625971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_10 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (490541091/5000000000 : ℝ)*x 0 + (1735621357/2500000000 : ℝ)*x 1 + (-1101411327/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490541091/5000000000 : ℝ)^8341 ≤ (921711511157/20000000000000 : ℝ)^6293 := by
    have hnat : (490541091 : ℕ)^8341*20000000000000^6293 ≤ 921711511157^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490541091 5000000000 921711511157 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1735621357/2500000000 : ℝ)^8341 ≤ (61650621319259/100000000000000 : ℝ)^6293 := by
    have hnat : (1735621357 : ℕ)^8341*100000000000000^6293 ≤ 61650621319259^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1735621357 2500000000 61650621319259 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101411327/2500000000 : ℝ)^8341 ≤ (6748164221521/20000000000000 : ℝ)^6293 := by
    have hnat : (1101411327 : ℕ)^8341*20000000000000^6293 ≤ 6748164221521^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101411327 2500000000 6748164221521 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(490541091/5000000000 : ℝ), (1735621357/2500000000 : ℝ), (-1101411327/2500000000 : ℝ)] ![(921711511157/20000000000000 : ℝ), (61650621319259/100000000000000 : ℝ), (6748164221521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(490541091/5000000000 : ℝ)|^8341 ≤ (921711511157/20000000000000 : ℝ)^6293
        have hw : |(490541091/5000000000 : ℝ)|=(490541091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1735621357/2500000000 : ℝ)|^8341 ≤ (61650621319259/100000000000000 : ℝ)^6293
        have hw : |(1735621357/2500000000 : ℝ)|=(1735621357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1101411327/2500000000 : ℝ)|^8341 ≤ (6748164221521/20000000000000 : ℝ)^6293
        have hw : |(-1101411327/2500000000 : ℝ)|=(1101411327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s1_11 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (23940177/125000000 : ℝ)*x 0 + (2905263303/5000000000 : ℝ)*x 1 + (5020592553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23940177/125000000 : ℝ)^8341 ≤ (5592312955391/50000000000000 : ℝ)^6293 := by
    have hnat : (23940177 : ℕ)^8341*50000000000000^6293 ≤ 5592312955391^6293*125000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23940177 125000000 5592312955391 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2905263303/5000000000 : ℝ)^8341 ≤ (48694684546707/100000000000000 : ℝ)^6293 := by
    have hnat : (2905263303 : ℕ)^8341*100000000000000^6293 ≤ 48694684546707^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2905263303 5000000000 48694684546707 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020592553/10000000000 : ℝ)^8341 ≤ (20060344764041/50000000000000 : ℝ)^6293 := by
    have hnat : (5020592553 : ℕ)^8341*50000000000000^6293 ≤ 20060344764041^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020592553 10000000000 20060344764041 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(23940177/125000000 : ℝ), (2905263303/5000000000 : ℝ), (5020592553/10000000000 : ℝ)] ![(5592312955391/50000000000000 : ℝ), (48694684546707/100000000000000 : ℝ), (20060344764041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(23940177/125000000 : ℝ)|^8341 ≤ (5592312955391/50000000000000 : ℝ)^6293
        have hw : |(23940177/125000000 : ℝ)|=(23940177/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2905263303/5000000000 : ℝ)|^8341 ≤ (48694684546707/100000000000000 : ℝ)^6293
        have hw : |(2905263303/5000000000 : ℝ)|=(2905263303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020592553/10000000000 : ℝ)|^8341 ≤ (20060344764041/50000000000000 : ℝ)^6293
        have hw : |(5020592553/10000000000 : ℝ)|=(5020592553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1737/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5683/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2041/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1737/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (219/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1737/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (219/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1737/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (219/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1737/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (219/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1737/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (219/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1737/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (219/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (219/50000 : ℝ) ^ (2085/512 : ℝ) ≤ (388397227/1562500000000000000 : ℝ) := by
    have hpowers : (219/50000 : ℝ)^2085 ≤ (388397227/1562500000000000000 : ℝ)^512 := by
      have hnat : (219 : ℕ)^2085*1562500000000000000^512 ≤ 388397227^512*50000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        219 50000 388397227 1562500000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (219/50000 : ℝ)) (X := (388397227/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1737/6250 : ℝ) ^ (2085/512 : ℝ) ≤ (16995883400460811/3125000000000000000 : ℝ) := by
    have hpowers : (1737/6250 : ℝ)^2085 ≤ (16995883400460811/3125000000000000000 : ℝ)^512 := by
      have hnat : (1737 : ℕ)^2085*3125000000000000000^512 ≤ 16995883400460811^512*6250^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1737 6250 16995883400460811 3125000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1737/6250 : ℝ)) (X := (16995883400460811/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (781250000388397227/781250000000000000 : ℝ) ≤ (625000000076301/625000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (781250000388397227/781250000000000000 : ℝ)^512 ≤ (625000000076301/625000000000000 : ℝ)^2085 := by
      have hnat : (781250000388397227 : ℕ)^512*625000000000000^2085 ≤ 625000000076301^2085*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781250000388397227 781250000000000000 625000000076301 625000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000000076301/625000000000000 : ℝ)) (X := (781250000388397227/781250000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (628399176835451053/625000000000000000 : ℝ) ≤ (1251666013760013/1250000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (628399176835451053/625000000000000000 : ℝ)^512 ≤ (1251666013760013/1250000000000000 : ℝ)^2085 := by
      have hnat : (628399176835451053 : ℕ)^512*1250000000000000^2085 ≤ 1251666013760013^2085*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        628399176835451053 625000000000000000 1251666013760013 1250000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251666013760013/1250000000000000 : ℝ)) (X := (628399176835451053/625000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1579495883400460811/1562500000000000000 : ℝ) ≤ (152994632247/152587890625 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (1579495883400460811/1562500000000000000 : ℝ)^512 ≤ (152994632247/152587890625 : ℝ)^2085 := by
      have hnat : (1579495883400460811 : ℕ)^512*152587890625^2085 ≤ 152994632247^2085*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1579495883400460811 1562500000000000000 152994632247 152587890625 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (152994632247/152587890625 : ℝ)) (X := (1579495883400460811/1562500000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(388397227/1562500000000000000 : ℝ) ≤ ((356156672669314407/356171875000000000 : ℝ)+2*(555337869137/113975000000000 : ℝ)*(219/50000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (356156672669314407/356171875000000000 : ℝ)+2*(555337869137/113975000000000 : ℝ)*(219/50000 : ℝ)=(625000000076301/625000000000000 : ℝ) by norm_num, show 1+2*(388397227/1562500000000000000 : ℝ)=(781250000388397227/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16995883400460811/3125000000000000000 : ℝ)+(388397227/1562500000000000000 : ℝ) ≤ ((356156672669314407/356171875000000000 : ℝ)+(555337869137/113975000000000 : ℝ)*((1737/6250 : ℝ)+(219/50000 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (356156672669314407/356171875000000000 : ℝ)+(555337869137/113975000000000 : ℝ)*((1737/6250 : ℝ)+(219/50000 : ℝ))=(1251666013760013/1250000000000000 : ℝ) by norm_num, show 1+(16995883400460811/3125000000000000000 : ℝ)+(388397227/1562500000000000000 : ℝ)=(628399176835451053/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16995883400460811/3125000000000000000 : ℝ) ≤ ((356156672669314407/356171875000000000 : ℝ)+2*(555337869137/113975000000000 : ℝ)*(1737/6250 : ℝ))^(2085/512 : ℝ) := by
    rw [show (356156672669314407/356171875000000000 : ℝ)+2*(555337869137/113975000000000 : ℝ)*(1737/6250 : ℝ)=(152994632247/152587890625 : ℝ) by norm_num, show 1+2*(16995883400460811/3125000000000000000 : ℝ)=(1579495883400460811/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (356156672669314407/356171875000000000 : ℝ)*(X 1 0+X 2 0)+(555337869137/113975000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (219/50000 : ℝ)) (hi := (1737/6250 : ℝ)) (c := (356156672669314407/356171875000000000 : ℝ)) (alpha := (555337869137/113975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (356156672669314407/356171875000000000 : ℝ)*(X 0 1+X 2 1)+(555337869137/113975000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (219/50000 : ℝ)) (hi := (1737/6250 : ℝ)) (c := (356156672669314407/356171875000000000 : ℝ)) (alpha := (555337869137/113975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (356156672669314407/356171875000000000 : ℝ)*(X 0 2+X 1 2)+(555337869137/113975000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (219/50000 : ℝ)) (hi := (1737/6250 : ℝ)) (c := (356156672669314407/356171875000000000 : ℝ)) (alpha := (555337869137/113975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1047072437/5000000000 : ℝ)*X 0 0+(569990627/1000000000 : ℝ)*X 0 1+(1250880557/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541879243/1000000000 : ℝ)*X 1 0+(-1234918633/5000000000 : ℝ)*X 1 1+(312720089/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((338674653/625000000 : ℝ)*X 2 0+(1250879907/2500000000 : ℝ)*X 2 1+(-2469836921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4316930551/10000000000 : ℝ)*X 0 0+(919541589/2500000000 : ℝ)*X 0 1+(1266307977/2500000000 : ℝ)*X 0 2+(4316930551/10000000000 : ℝ)*X 1 0+(919541589/2500000000 : ℝ)*X 1 1+(1266307977/2500000000 : ℝ)*X 1 2+(4316930551/10000000000 : ℝ)*X 2 0+(919541589/2500000000 : ℝ)*X 2 1+(1266307977/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-261868413/1250000000 : ℝ)*X 0 0+(5013009033/10000000000 : ℝ)*X 0 1+(5690228573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((524019843/1000000000 : ℝ)*X 1 0+(-89156299/500000000 : ℝ)*X 1 1+(5690232241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1048039417/2000000000 : ℝ)*X 2 0+(2845117023/5000000000 : ℝ)*X 2 1+(-222890657/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159259007/5000000000 : ℝ)*X 0 0+(201853457/400000000 : ℝ)*X 0 1+(1848717013/5000000000 : ℝ)*X 0 2+(2159259007/5000000000 : ℝ)*X 1 0+(201853457/400000000 : ℝ)*X 1 1+(1848717013/5000000000 : ℝ)*X 1 2+(2159259007/5000000000 : ℝ)*X 2 0+(201853457/400000000 : ℝ)*X 2 1+(1848717013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((5920149/10000000000 : ℝ)*X 0 0+(549036211/1000000000 : ℝ)*X 0 1+(6354226511/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((490544991/5000000000 : ℝ)*X 1 0+(-1101404781/2500000000 : ℝ)*X 1 1+(1735625971/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((490541091/5000000000 : ℝ)*X 2 0+(1735621357/2500000000 : ℝ)*X 2 1+(-1101411327/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((23940177/125000000 : ℝ)*X 0 0+(2905263303/5000000000 : ℝ)*X 0 1+(5020592553/10000000000 : ℝ)*X 0 2+(23940177/125000000 : ℝ)*X 1 0+(2905263303/5000000000 : ℝ)*X 1 1+(5020592553/10000000000 : ℝ)*X 1 2+(23940177/125000000 : ℝ)*X 2 0+(2905263303/5000000000 : ℝ)*X 2 1+(5020592553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (341370609924235023934671837/35617187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (6133803/10000000000000 : ℝ)*(lower2) + (539236153647609/50000000000000 : ℝ)*(major0) + (539236153647609/50000000000000 : ℝ)*(major1) + (1078472307295219/100000000000000 : ℝ)*(major2) + (717996039023519/50000000000000 : ℝ)*(sp0) + (1435991566828819/100000000000000 : ℝ)*(sp1) + (358997399718053/25000000000000 : ℝ)*(sp2) + (180236710026299/25000000000000 : ℝ)*(sp3) + (3878929447/100000000000000 : ℝ)*(sp4) + (14642743/390625000000 : ℝ)*(sp5) + (2631327991/50000000000000 : ℝ)*(sp6) + (641605459/100000000000000 : ℝ)*(sp9) + (1095448291/100000000000000 : ℝ)*(sp10) + (374506897/25000000000000 : ℝ)*(sp11) + (720948338132783/100000000000000 : ℝ)*(f.failure) + (287199191395297/20000000000000 : ℝ)*(f.sum) + (74057462471091/11397500000000000000000000000 : ℝ)*base66 + (689617816888347923/71234375000000000000000000000000 : ℝ)*base68 + (46266602363362141/71234375000000000000000000000000 : ℝ)*base69 + (450928869301447399/35617187500000000000000000000000 : ℝ)*base72 + (430569308749/2849375000000000000000000000 : ℝ)*base74 + (190145955957811117/35617187500000000000000000000000 : ℝ)*base76 + (233615100213984637/17808593750000000000000000000000 : ℝ)*base78 + (91363561642312631/8904296875000000000000000000000 : ℝ)*base80 + (16432516519059/5698750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4264213/10000000000000000000000 : ℝ)*base90 + (4264213/10000000000000000000000 : ℝ)*base92 + (104264213/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (594607550475296910523310001/71234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1732789960901/156250000000 : ℝ)*(major0) + (1732789960901/156250000000 : ℝ)*(major1) + (1108985574976641/100000000000000 : ℝ)*(major2) + (4962457849/100000000000000 : ℝ)*(sp1) + (8018818613/100000000000000 : ℝ)*(sp2) + (979057357/100000000000000 : ℝ)*(sp3) + (369155170824889/25000000000000 : ℝ)*(sp4) + (738309607775377/50000000000000 : ℝ)*(sp5) + (73830824866639/5000000000000 : ℝ)*(sp6) + (92667905948857/12500000000000 : ℝ)*(sp7) + (251566477/6250000000000 : ℝ)*(sp8) + (66294323/12500000000000 : ℝ)*(sp9) + (38442359/20000000000000 : ℝ)*(sp10) + (387340377/20000000000000 : ℝ)*(sp11) + (370673081675049/50000000000000 : ℝ)*(f.failure) + (1476624708363187/100000000000000 : ℝ)*(f.sum) + (21151490006169/22795000000000000000000000000 : ℝ)*base65 + (3684312085939969/445214843750000000000000000000 : ℝ)*base68 + (512150414986899/71234375000000000000000000000000 : ℝ)*base69 + (84497983404582133/14246875000000000000000000000000 : ℝ)*base72 + (4242140153723/11397500000000000000000000000 : ℝ)*base74 + (350802957728205649/71234375000000000000000000000000 : ℝ)*base75 + (122199365757640883/14246875000000000000000000000000 : ℝ)*base78 + (62128459702506379/7123437500000000000000000000000 : ℝ)*base80 + (756862165401/569875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (21523661/5000000000000000000000 : ℝ)*base89 + (21523661/5000000000000000000000 : ℝ)*base91 + (28476339/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1148_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1737/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5683/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2041/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1148_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1148_s2_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-134190949/625000000 : ℝ)*x 0 + (1377417571/2500000000 : ℝ)*x 1 + (1032021513/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134190949/625000000 : ℝ)^8341 ≤ (13013604822683/100000000000000 : ℝ)^6293 := by
    have hnat : (134190949 : ℕ)^8341*100000000000000^6293 ≤ 13013604822683^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134190949 625000000 13013604822683 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377417571/2500000000 : ℝ)^8341 ≤ (11345334036613/25000000000000 : ℝ)^6293 := by
    have hnat : (1377417571 : ℕ)^8341*25000000000000^6293 ≤ 11345334036613^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377417571 2500000000 11345334036613 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032021513/2000000000 : ℝ)^8341 ≤ (41605059012983/100000000000000 : ℝ)^6293 := by
    have hnat : (1032021513 : ℕ)^8341*100000000000000^6293 ≤ 41605059012983^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032021513 2000000000 41605059012983 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134190949/625000000 : ℝ), (1377417571/2500000000 : ℝ), (1032021513/2000000000 : ℝ)] ![(13013604822683/100000000000000 : ℝ), (11345334036613/25000000000000 : ℝ), (41605059012983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134190949/625000000 : ℝ)|^8341 ≤ (13013604822683/100000000000000 : ℝ)^6293
        have hw : |(-134190949/625000000 : ℝ)|=(134190949/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1377417571/2500000000 : ℝ)|^8341 ≤ (11345334036613/25000000000000 : ℝ)^6293
        have hw : |(1377417571/2500000000 : ℝ)|=(1377417571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032021513/2000000000 : ℝ)|^8341 ≤ (41605059012983/100000000000000 : ℝ)^6293
        have hw : |(1032021513/2000000000 : ℝ)|=(1032021513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s2_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686803191/5000000000 : ℝ)*x 0 + (-465750091/2000000000 : ℝ)*x 1 + (5160109771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686803191/5000000000 : ℝ)^8341 ≤ (1097547481997/2500000000000 : ℝ)^6293 := by
    have hnat : (2686803191 : ℕ)^8341*2500000000000^6293 ≤ 1097547481997^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686803191 5000000000 1097547481997 2500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465750091/2000000000 : ℝ)^8341 ≤ (3623254528847/25000000000000 : ℝ)^6293 := by
    have hnat : (465750091 : ℕ)^8341*25000000000000^6293 ≤ 3623254528847^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465750091 2000000000 3623254528847 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5160109771/10000000000 : ℝ)^8341 ≤ (4160508258807/10000000000000 : ℝ)^6293 := by
    have hnat : (5160109771 : ℕ)^8341*10000000000000^6293 ≤ 4160508258807^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160109771 10000000000 4160508258807 10000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686803191/5000000000 : ℝ), (-465750091/2000000000 : ℝ), (5160109771/10000000000 : ℝ)] ![(1097547481997/2500000000000 : ℝ), (3623254528847/25000000000000 : ℝ), (4160508258807/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686803191/5000000000 : ℝ)|^8341 ≤ (1097547481997/2500000000000 : ℝ)^6293
        have hw : |(2686803191/5000000000 : ℝ)|=(2686803191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-465750091/2000000000 : ℝ)|^8341 ≤ (3623254528847/25000000000000 : ℝ)^6293
        have hw : |(-465750091/2000000000 : ℝ)|=(465750091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5160109771/10000000000 : ℝ)|^8341 ≤ (4160508258807/10000000000000 : ℝ)^6293
        have hw : |(5160109771/10000000000 : ℝ)|=(5160109771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s2_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671700807/1250000000 : ℝ)*x 0 + (10320219/20000000 : ℝ)*x 1 + (-582187677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671700807/1250000000 : ℝ)^8341 ≤ (43901900081207/100000000000000 : ℝ)^6293 := by
    have hnat : (671700807 : ℕ)^8341*100000000000000^6293 ≤ 43901900081207^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671700807 1250000000 43901900081207 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10320219/20000000 : ℝ)^8341 ≤ (20802539845973/50000000000000 : ℝ)^6293 := by
    have hnat : (10320219 : ℕ)^8341*50000000000000^6293 ≤ 20802539845973^6293*20000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10320219 20000000 20802539845973 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582187677/2500000000 : ℝ)^8341 ≤ (14493020202361/100000000000000 : ℝ)^6293 := by
    have hnat : (582187677 : ℕ)^8341*100000000000000^6293 ≤ 14493020202361^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582187677 2500000000 14493020202361 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671700807/1250000000 : ℝ), (10320219/20000000 : ℝ), (-582187677/2500000000 : ℝ)] ![(43901900081207/100000000000000 : ℝ), (20802539845973/50000000000000 : ℝ), (14493020202361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671700807/1250000000 : ℝ)|^8341 ≤ (43901900081207/100000000000000 : ℝ)^6293
        have hw : |(671700807/1250000000 : ℝ)|=(671700807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10320219/20000000 : ℝ)|^8341 ≤ (20802539845973/50000000000000 : ℝ)^6293
        have hw : |(10320219/20000000 : ℝ)|=(10320219/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-582187677/2500000000 : ℝ)|^8341 ≤ (14493020202361/100000000000000 : ℝ)^6293
        have hw : |(-582187677/2500000000 : ℝ)|=(582187677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s2_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870648819/2000000000 : ℝ)*x 0 + (1004722533/2500000000 : ℝ)*x 1 + (1178787453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870648819/2000000000 : ℝ)^8341 ≤ (16604965746779/50000000000000 : ℝ)^6293 := by
    have hnat : (870648819 : ℕ)^8341*50000000000000^6293 ≤ 16604965746779^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870648819 2000000000 16604965746779 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004722533/2500000000 : ℝ)^8341 ≤ (3734015052251/12500000000000 : ℝ)^6293 := by
    have hnat : (1004722533 : ℕ)^8341*12500000000000^6293 ≤ 3734015052251^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004722533 2500000000 3734015052251 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1178787453/2500000000 : ℝ)^8341 ≤ (36917948075091/100000000000000 : ℝ)^6293 := by
    have hnat : (1178787453 : ℕ)^8341*100000000000000^6293 ≤ 36917948075091^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178787453 2500000000 36917948075091 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870648819/2000000000 : ℝ), (1004722533/2500000000 : ℝ), (1178787453/2500000000 : ℝ)] ![(16604965746779/50000000000000 : ℝ), (3734015052251/12500000000000 : ℝ), (36917948075091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870648819/2000000000 : ℝ)|^8341 ≤ (16604965746779/50000000000000 : ℝ)^6293
        have hw : |(870648819/2000000000 : ℝ)|=(870648819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004722533/2500000000 : ℝ)|^8341 ≤ (3734015052251/12500000000000 : ℝ)^6293
        have hw : |(1004722533/2500000000 : ℝ)|=(1004722533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1178787453/2500000000 : ℝ)|^8341 ≤ (36917948075091/100000000000000 : ℝ)^6293
        have hw : |(1178787453/2500000000 : ℝ)|=(1178787453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s2_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-536789049/2500000000 : ℝ)*x 0 + (5162508083/10000000000 : ℝ)*x 1 + (5507245747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536789049/2500000000 : ℝ)^8341 ≤ (13014416327481/100000000000000 : ℝ)^6293 := by
    have hnat : (536789049 : ℕ)^8341*100000000000000^6293 ≤ 13014416327481^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536789049 2500000000 13014416327481 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5162508083/10000000000 : ℝ)^8341 ≤ (4163071481613/10000000000000 : ℝ)^6293 := by
    have hnat : (5162508083 : ℕ)^8341*10000000000000^6293 ≤ 4163071481613^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162508083 10000000000 4163071481613 10000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5507245747/10000000000 : ℝ)^8341 ≤ (5669358604801/12500000000000 : ℝ)^6293 := by
    have hnat : (5507245747 : ℕ)^8341*12500000000000^6293 ≤ 5669358604801^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507245747 10000000000 5669358604801 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-536789049/2500000000 : ℝ), (5162508083/10000000000 : ℝ), (5507245747/10000000000 : ℝ)] ![(13014416327481/100000000000000 : ℝ), (4163071481613/10000000000000 : ℝ), (5669358604801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-536789049/2500000000 : ℝ)|^8341 ≤ (13014416327481/100000000000000 : ℝ)^6293
        have hw : |(-536789049/2500000000 : ℝ)|=(536789049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5162508083/10000000000 : ℝ)|^8341 ≤ (4163071481613/10000000000000 : ℝ)^6293
        have hw : |(5162508083/10000000000 : ℝ)|=(5162508083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5507245747/10000000000 : ℝ)|^8341 ≤ (5669358604801/12500000000000 : ℝ)^6293
        have hw : |(5507245747/10000000000 : ℝ)|=(5507245747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s2_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321219429/2500000000 : ℝ)*x 0 + (-1981612257/10000000000 : ℝ)*x 1 + (5507246481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321219429/2500000000 : ℝ)^8341 ≤ (83874357443/195312500000 : ℝ)^6293 := by
    have hnat : (1321219429 : ℕ)^8341*195312500000^6293 ≤ 83874357443^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321219429 2500000000 83874357443 195312500000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981612257/10000000000 : ℝ)^8341 ≤ (11701452118053/100000000000000 : ℝ)^6293 := by
    have hnat : (1981612257 : ℕ)^8341*100000000000000^6293 ≤ 11701452118053^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981612257 10000000000 11701452118053 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5507246481/10000000000 : ℝ)^8341 ≤ (90709753701/200000000000 : ℝ)^6293 := by
    have hnat : (5507246481 : ℕ)^8341*200000000000^6293 ≤ 90709753701^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507246481 10000000000 90709753701 200000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321219429/2500000000 : ℝ), (-1981612257/10000000000 : ℝ), (5507246481/10000000000 : ℝ)] ![(83874357443/195312500000 : ℝ), (11701452118053/100000000000000 : ℝ), (90709753701/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321219429/2500000000 : ℝ)|^8341 ≤ (83874357443/195312500000 : ℝ)^6293
        have hw : |(1321219429/2500000000 : ℝ)|=(1321219429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1981612257/10000000000 : ℝ)|^8341 ≤ (11701452118053/100000000000000 : ℝ)^6293
        have hw : |(-1981612257/10000000000 : ℝ)|=(1981612257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5507246481/10000000000 : ℝ)|^8341 ≤ (90709753701/200000000000 : ℝ)^6293
        have hw : |(5507246481/10000000000 : ℝ)|=(5507246481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s2_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056975221/2000000000 : ℝ)*x 0 + (688405779/1250000000 : ℝ)*x 1 + (-1981614821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056975221/2000000000 : ℝ)^8341 ≤ (42943653659991/100000000000000 : ℝ)^6293 := by
    have hnat : (1056975221 : ℕ)^8341*100000000000000^6293 ≤ 42943653659991^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056975221 2000000000 42943653659991 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688405779/1250000000 : ℝ)^8341 ≤ (22677437066251/50000000000000 : ℝ)^6293 := by
    have hnat : (688405779 : ℕ)^8341*50000000000000^6293 ≤ 22677437066251^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688405779 1250000000 22677437066251 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981614821/10000000000 : ℝ)^8341 ≤ (2340294437169/20000000000000 : ℝ)^6293 := by
    have hnat : (1981614821 : ℕ)^8341*20000000000000^6293 ≤ 2340294437169^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981614821 10000000000 2340294437169 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056975221/2000000000 : ℝ), (688405779/1250000000 : ℝ), (-1981614821/10000000000 : ℝ)] ![(42943653659991/100000000000000 : ℝ), (22677437066251/50000000000000 : ℝ), (2340294437169/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056975221/2000000000 : ℝ)|^8341 ≤ (42943653659991/100000000000000 : ℝ)^6293
        have hw : |(1056975221/2000000000 : ℝ)|=(1056975221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688405779/1250000000 : ℝ)|^8341 ≤ (22677437066251/50000000000000 : ℝ)^6293
        have hw : |(688405779/1250000000 : ℝ)|=(688405779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981614821/10000000000 : ℝ)|^8341 ≤ (2340294437169/20000000000000 : ℝ)^6293
        have hw : |(-1981614821/10000000000 : ℝ)|=(1981614821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s2_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176722101/5000000000 : ℝ)*x 0 + (588796289/1250000000 : ℝ)*x 1 + (1005929393/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176722101/5000000000 : ℝ)^8341 ≤ (33211954889521/100000000000000 : ℝ)^6293 := by
    have hnat : (2176722101 : ℕ)^8341*100000000000000^6293 ≤ 33211954889521^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176722101 5000000000 33211954889521 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (588796289/1250000000 : ℝ)^8341 ≤ (2304272243021/6250000000000 : ℝ)^6293 := by
    have hnat : (588796289 : ℕ)^8341*6250000000000^6293 ≤ 2304272243021^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588796289 1250000000 2304272243021 6250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005929393/2500000000 : ℝ)^8341 ≤ (29919689201689/100000000000000 : ℝ)^6293 := by
    have hnat : (1005929393 : ℕ)^8341*100000000000000^6293 ≤ 29919689201689^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005929393 2500000000 29919689201689 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176722101/5000000000 : ℝ), (588796289/1250000000 : ℝ), (1005929393/2500000000 : ℝ)] ![(33211954889521/100000000000000 : ℝ), (2304272243021/6250000000000 : ℝ), (29919689201689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176722101/5000000000 : ℝ)|^8341 ≤ (33211954889521/100000000000000 : ℝ)^6293
        have hw : |(2176722101/5000000000 : ℝ)|=(2176722101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(588796289/1250000000 : ℝ)|^8341 ≤ (2304272243021/6250000000000 : ℝ)^6293
        have hw : |(588796289/1250000000 : ℝ)|=(588796289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005929393/2500000000 : ℝ)|^8341 ≤ (29919689201689/100000000000000 : ℝ)^6293
        have hw : |(1005929393/2500000000 : ℝ)|=(1005929393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9097/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3297/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2041/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5683/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2041/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5683/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2041/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5683/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2041/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5683/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2041/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5683/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2041/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5683/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5683/100000 : ℝ) ^ (2085/512 : ℝ) ≤ (105978901375621/12500000000000000000 : ℝ) := by
    have hpowers : (5683/100000 : ℝ)^2085 ≤ (105978901375621/12500000000000000000 : ℝ)^512 := by
      have hnat : (5683 : ℕ)^2085*12500000000000000000^512 ≤ 105978901375621^512*100000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5683 100000 105978901375621 12500000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5683/100000 : ℝ)) (X := (105978901375621/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2041/10000 : ℝ) ^ (2085/512 : ℝ) ≤ (154702521471160463/100000000000000000000 : ℝ) := by
    have hpowers : (2041/10000 : ℝ)^2085 ≤ (154702521471160463/100000000000000000000 : ℝ)^512 := by
      have hnat : (2041 : ℕ)^2085*100000000000000000000^512 ≤ 154702521471160463^512*10000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2041 10000 154702521471160463 100000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2041/10000 : ℝ)) (X := (154702521471160463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250105978901375621/6250000000000000000 : ℝ) ≤ (2500010409755479/2500000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (6250105978901375621/6250000000000000000 : ℝ)^512 ≤ (2500010409755479/2500000000000000 : ℝ)^2085 := by
      have hnat : (6250105978901375621 : ℕ)^512*2500000000000000^2085 ≤ 2500010409755479^2085*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250105978901375621 6250000000000000000 2500010409755479 2500000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500010409755479/2500000000000000 : ℝ)) (X := (6250105978901375621/6250000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100155550352682165431/100000000000000000000 : ℝ) ≤ (10003817510411791/10000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (100155550352682165431/100000000000000000000 : ℝ)^512 ≤ (10003817510411791/10000000000000000 : ℝ)^2085 := by
      have hnat : (100155550352682165431 : ℕ)^512*10000000000000000^2085 ≤ 10003817510411791^2085*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100155550352682165431 100000000000000000000 10003817510411791 10000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003817510411791/10000000000000000 : ℝ)) (X := (100155550352682165431/100000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50154702521471160463/50000000000000000000 : ℝ) ≤ (5003796690900833/5000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (50154702521471160463/50000000000000000000 : ℝ)^512 ≤ (5003796690900833/5000000000000000 : ℝ)^2085 := by
      have hnat : (50154702521471160463 : ℕ)^512*5000000000000000^2085 ≤ 5003796690900833^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50154702521471160463 50000000000000000000 5003796690900833 5000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003796690900833/5000000000000000 : ℝ)) (X := (50154702521471160463/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(105978901375621/12500000000000000000 : ℝ) ≤ ((24537949443943072947/24545000000000000000 : ℝ)+2*(10068990373/3927200000000 : ℝ)*(5683/100000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (24537949443943072947/24545000000000000000 : ℝ)+2*(10068990373/3927200000000 : ℝ)*(5683/100000 : ℝ)=(2500010409755479/2500000000000000 : ℝ) by norm_num, show 1+2*(105978901375621/12500000000000000000 : ℝ)=(6250105978901375621/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(154702521471160463/100000000000000000000 : ℝ)+(105978901375621/12500000000000000000 : ℝ) ≤ ((24537949443943072947/24545000000000000000 : ℝ)+(10068990373/3927200000000 : ℝ)*((2041/10000 : ℝ)+(5683/100000 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (24537949443943072947/24545000000000000000 : ℝ)+(10068990373/3927200000000 : ℝ)*((2041/10000 : ℝ)+(5683/100000 : ℝ))=(10003817510411791/10000000000000000 : ℝ) by norm_num, show 1+(154702521471160463/100000000000000000000 : ℝ)+(105978901375621/12500000000000000000 : ℝ)=(100155550352682165431/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(154702521471160463/100000000000000000000 : ℝ) ≤ ((24537949443943072947/24545000000000000000 : ℝ)+2*(10068990373/3927200000000 : ℝ)*(2041/10000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (24537949443943072947/24545000000000000000 : ℝ)+2*(10068990373/3927200000000 : ℝ)*(2041/10000 : ℝ)=(5003796690900833/5000000000000000 : ℝ) by norm_num, show 1+2*(154702521471160463/100000000000000000000 : ℝ)=(50154702521471160463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24537949443943072947/24545000000000000000 : ℝ)*(X 1 0+X 2 0)+(10068990373/3927200000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (5683/100000 : ℝ)) (hi := (2041/10000 : ℝ)) (c := (24537949443943072947/24545000000000000000 : ℝ)) (alpha := (10068990373/3927200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24537949443943072947/24545000000000000000 : ℝ)*(X 0 1+X 2 1)+(10068990373/3927200000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (5683/100000 : ℝ)) (hi := (2041/10000 : ℝ)) (c := (24537949443943072947/24545000000000000000 : ℝ)) (alpha := (10068990373/3927200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24537949443943072947/24545000000000000000 : ℝ)*(X 0 2+X 1 2)+(10068990373/3927200000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (5683/100000 : ℝ)) (hi := (2041/10000 : ℝ)) (c := (24537949443943072947/24545000000000000000 : ℝ)) (alpha := (10068990373/3927200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-134190949/625000000 : ℝ)*X 0 0+(1377417571/2500000000 : ℝ)*X 0 1+(1032021513/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686803191/5000000000 : ℝ)*X 1 0+(-465750091/2000000000 : ℝ)*X 1 1+(5160109771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671700807/1250000000 : ℝ)*X 2 0+(10320219/20000000 : ℝ)*X 2 1+(-582187677/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870648819/2000000000 : ℝ)*X 0 0+(1004722533/2500000000 : ℝ)*X 0 1+(1178787453/2500000000 : ℝ)*X 0 2+(870648819/2000000000 : ℝ)*X 1 0+(1004722533/2500000000 : ℝ)*X 1 1+(1178787453/2500000000 : ℝ)*X 1 2+(870648819/2000000000 : ℝ)*X 2 0+(1004722533/2500000000 : ℝ)*X 2 1+(1178787453/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-536789049/2500000000 : ℝ)*X 0 0+(5162508083/10000000000 : ℝ)*X 0 1+(5507245747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1321219429/2500000000 : ℝ)*X 1 0+(-1981612257/10000000000 : ℝ)*X 1 1+(5507246481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056975221/2000000000 : ℝ)*X 2 0+(688405779/1250000000 : ℝ)*X 2 1+(-1981614821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176722101/5000000000 : ℝ)*X 0 0+(588796289/1250000000 : ℝ)*X 0 1+(1005929393/2500000000 : ℝ)*X 0 2+(2176722101/5000000000 : ℝ)*X 1 0+(588796289/1250000000 : ℝ)*X 1 1+(1005929393/2500000000 : ℝ)*X 1 2+(2176722101/5000000000 : ℝ)*X 2 0+(588796289/1250000000 : ℝ)*X 2 1+(1005929393/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (498652035907320478167095037/49090000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (233695693/20000000000000 : ℝ)*(base19) + (879647743/100000000000000 : ℝ)*(base23) + (388231/10000000000000 : ℝ)*(upper2) + (403264503/100000000000000 : ℝ)*(upper3) + (36051649/20000000000000 : ℝ)*(upper4) + (537128670056577/25000000000000 : ℝ)*(major0) + (537128670056577/25000000000000 : ℝ)*(major1) + (2148514680226309/100000000000000 : ℝ)*(major2) + (286074482136819/10000000000000 : ℝ)*(sp0) + (2860766506947221/100000000000000 : ℝ)*(sp1) + (1430383397888971/50000000000000 : ℝ)*(sp2) + (1436251583181049/100000000000000 : ℝ)*(sp3) + (4570811499/20000000000000 : ℝ)*(sp4) + (2440812179/25000000000000 : ℝ)*(sp7) + (287252269285953/20000000000000 : ℝ)*(f.failure) + (1430383837712843/50000000000000 : ℝ)*(f.sum) + (64588594137399/9818000000000000000000000000 : ℝ)*base65 + (3766189695638440081/613625000000000000000000000000000 : ℝ)*base68 + (4470933450916937377/2454500000000000000000000000000000 : ℝ)*base70 + (3889490769242940081/613625000000000000000000000000000 : ℝ)*base72 + (818647910607/1963600000000000000000000000 : ℝ)*base73 + (10758909045858937377/2454500000000000000000000000000000 : ℝ)*base76 + (3028248591597002581/613625000000000000000000000000000 : ℝ)*base78 + (1606346322858127581/613625000000000000000000000000000 : ℝ)*base80 + (3525952120517/613625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (15886917/2000000000000000000000 : ℝ)*base89 + (15886917/2000000000000000000000 : ℝ)*base91 + (4113083/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2608065029835273454777536267/245450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (940777711/50000000000000 : ℝ)*(base19) + (65271387/5000000000000 : ℝ)*(base23) + (343126801/100000000000000 : ℝ)*(upper2) + (127443289/100000000000000 : ℝ)*(upper3) + (3180759/1000000000000 : ℝ)*(upper5) + (435708668806813/20000000000000 : ℝ)*(major0) + (435708668806813/20000000000000 : ℝ)*(major1) + (435708668806813/20000000000000 : ℝ)*(major2) + (13406941551/50000000000000 : ℝ)*(sp1) + (6494234119/100000000000000 : ℝ)*(sp2) + (362593889406189/12500000000000 : ℝ)*(sp4) + (725180604952747/25000000000000 : ℝ)*(sp5) + (725185828896913/25000000000000 : ℝ)*(sp6) + (1456335218630383/100000000000000 : ℝ)*(sp7) + (1456335218630383/100000000000000 : ℝ)*(f.failure) + (362593889406189/12500000000000 : ℝ)*(f.sum) + (4925057879601/4909000000000000000000000000 : ℝ)*base66 + (1599679554156962089/490900000000000000000000000000000 : ℝ)*base68 + (2425788538829837911/490900000000000000000000000000000 : ℝ)*base69 + (2416621375031637911/490900000000000000000000000000000 : ℝ)*base71 + (5270946722081/981800000000000000000000000 : ℝ)*base74 + (2298779057775562089/490900000000000000000000000000000 : ℝ)*base76 + (355122487934837911/490900000000000000000000000000000 : ℝ)*base77 + (5392232577481837911/490900000000000000000000000000000 : ℝ)*base79 + (13200047557537/4909000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7657813/10000000000000000000000 : ℝ)*base90 + (7657813/10000000000000000000000 : ℝ)*base92 + (7657813/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1148_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9097/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1148_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1148_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9097/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1148_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1148_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1148_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9097/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3297/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1148_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

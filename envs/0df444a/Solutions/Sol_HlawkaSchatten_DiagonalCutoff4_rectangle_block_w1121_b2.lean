-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1121_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:09:36.815283+00:00
-- url     : https://prove2.me/submissions/13f0b10e-8332-4dc0-9a18-2c7bb84487c0

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
theorem support_rectangle_w1121_s6_0 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-272116973/1250000000 : ℝ)*x 0 + (674225067/1250000000 : ℝ)*x 1 + (5265026559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272116973/1250000000 : ℝ)^4157 ≤ (3306472508581/25000000000000 : ℝ)^3133 := by
    have hnat : (272116973 : ℕ)^4157*25000000000000^3133 ≤ 3306472508581^3133*1250000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272116973 1250000000 3306472508581 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674225067/1250000000 : ℝ)^4157 ≤ (44082531413201/100000000000000 : ℝ)^3133 := by
    have hnat : (674225067 : ℕ)^4157*100000000000000^3133 ≤ 44082531413201^3133*1250000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674225067 1250000000 44082531413201 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265026559/10000000000 : ℝ)^4157 ≤ (42691578530643/100000000000000 : ℝ)^3133 := by
    have hnat : (5265026559 : ℕ)^4157*100000000000000^3133 ≤ 42691578530643^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265026559 10000000000 42691578530643 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272116973/1250000000 : ℝ), (674225067/1250000000 : ℝ), (5265026559/10000000000 : ℝ)] ![(3306472508581/25000000000000 : ℝ), (44082531413201/100000000000000 : ℝ), (42691578530643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272116973/1250000000 : ℝ)|^4157 ≤ (3306472508581/25000000000000 : ℝ)^3133
        have hw : |(-272116973/1250000000 : ℝ)|=(272116973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674225067/1250000000 : ℝ)|^4157 ≤ (44082531413201/100000000000000 : ℝ)^3133
        have hw : |(674225067/1250000000 : ℝ)|=(674225067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265026559/10000000000 : ℝ)|^4157 ≤ (42691578530643/100000000000000 : ℝ)^3133
        have hw : |(5265026559/10000000000 : ℝ)|=(5265026559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s6_1 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534492881/1000000000 : ℝ)*x 0 + (-560565769/2500000000 : ℝ)*x 1 + (5265026559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534492881/1000000000 : ℝ)^4157 ≤ (43553350596943/100000000000000 : ℝ)^3133 := by
    have hnat : (534492881 : ℕ)^4157*100000000000000^3133 ≤ 43553350596943^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534492881 1000000000 43553350596943 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560565769/2500000000 : ℝ)^4157 ≤ (6877535426697/50000000000000 : ℝ)^3133 := by
    have hnat : (560565769 : ℕ)^4157*50000000000000^3133 ≤ 6877535426697^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560565769 2500000000 6877535426697 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265026559/10000000000 : ℝ)^4157 ≤ (42691578530643/100000000000000 : ℝ)^3133 := by
    have hnat : (5265026559 : ℕ)^4157*100000000000000^3133 ≤ 42691578530643^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265026559 10000000000 42691578530643 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534492881/1000000000 : ℝ), (-560565769/2500000000 : ℝ), (5265026559/10000000000 : ℝ)] ![(43553350596943/100000000000000 : ℝ), (6877535426697/50000000000000 : ℝ), (42691578530643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534492881/1000000000 : ℝ)|^4157 ≤ (43553350596943/100000000000000 : ℝ)^3133
        have hw : |(534492881/1000000000 : ℝ)|=(534492881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560565769/2500000000 : ℝ)|^4157 ≤ (6877535426697/50000000000000 : ℝ)^3133
        have hw : |(-560565769/2500000000 : ℝ)|=(560565769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265026559/10000000000 : ℝ)|^4157 ≤ (42691578530643/100000000000000 : ℝ)^3133
        have hw : |(5265026559/10000000000 : ℝ)|=(5265026559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s6_2 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534492881/1000000000 : ℝ)*x 0 + (5265026559/10000000000 : ℝ)*x 1 + (-560565769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534492881/1000000000 : ℝ)^4157 ≤ (43553350596943/100000000000000 : ℝ)^3133 := by
    have hnat : (534492881 : ℕ)^4157*100000000000000^3133 ≤ 43553350596943^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534492881 1000000000 43553350596943 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265026559/10000000000 : ℝ)^4157 ≤ (42691578530643/100000000000000 : ℝ)^3133 := by
    have hnat : (5265026559 : ℕ)^4157*100000000000000^3133 ≤ 42691578530643^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265026559 10000000000 42691578530643 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560565769/2500000000 : ℝ)^4157 ≤ (6877535426697/50000000000000 : ℝ)^3133 := by
    have hnat : (560565769 : ℕ)^4157*50000000000000^3133 ≤ 6877535426697^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560565769 2500000000 6877535426697 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534492881/1000000000 : ℝ), (5265026559/10000000000 : ℝ), (-560565769/2500000000 : ℝ)] ![(43553350596943/100000000000000 : ℝ), (42691578530643/100000000000000 : ℝ), (6877535426697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534492881/1000000000 : ℝ)|^4157 ≤ (43553350596943/100000000000000 : ℝ)^3133
        have hw : |(534492881/1000000000 : ℝ)|=(534492881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265026559/10000000000 : ℝ)|^4157 ≤ (42691578530643/100000000000000 : ℝ)^3133
        have hw : |(5265026559/10000000000 : ℝ)|=(5265026559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560565769/2500000000 : ℝ)|^4157 ≤ (6877535426697/50000000000000 : ℝ)^3133
        have hw : |(-560565769/2500000000 : ℝ)|=(560565769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s6_3 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218381033/500000000 : ℝ)*x 0 + (1060478709/2500000000 : ℝ)*x 1 + (4497052497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218381033/500000000 : ℝ)^4157 ≤ (33316653963699/100000000000000 : ℝ)^3133 := by
    have hnat : (218381033 : ℕ)^4157*100000000000000^3133 ≤ 33316653963699^3133*500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218381033 500000000 33316653963699 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060478709/2500000000 : ℝ)^4157 ≤ (8012592898163/25000000000000 : ℝ)^3133 := by
    have hnat : (1060478709 : ℕ)^4157*25000000000000^3133 ≤ 8012592898163^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060478709 2500000000 8012592898163 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497052497/10000000000 : ℝ)^4157 ≤ (34632974424929/100000000000000 : ℝ)^3133 := by
    have hnat : (4497052497 : ℕ)^4157*100000000000000^3133 ≤ 34632974424929^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497052497 10000000000 34632974424929 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218381033/500000000 : ℝ), (1060478709/2500000000 : ℝ), (4497052497/10000000000 : ℝ)] ![(33316653963699/100000000000000 : ℝ), (8012592898163/25000000000000 : ℝ), (34632974424929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218381033/500000000 : ℝ)|^4157 ≤ (33316653963699/100000000000000 : ℝ)^3133
        have hw : |(218381033/500000000 : ℝ)|=(218381033/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060478709/2500000000 : ℝ)|^4157 ≤ (8012592898163/25000000000000 : ℝ)^3133
        have hw : |(1060478709/2500000000 : ℝ)|=(1060478709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497052497/10000000000 : ℝ)|^4157 ≤ (34632974424929/100000000000000 : ℝ)^3133
        have hw : |(4497052497/10000000000 : ℝ)|=(4497052497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s6_4 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-136058807/625000000 : ℝ)*x 0 + (164542239/312500000 : ℝ)*x 1 + (2696737093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136058807/625000000 : ℝ)^4157 ≤ (132259313721/1000000000000 : ℝ)^3133 := by
    have hnat : (136058807 : ℕ)^4157*1000000000000^3133 ≤ 132259313721^3133*625000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136058807 625000000 132259313721 1000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164542239/312500000 : ℝ)^4157 ≤ (42695076112869/100000000000000 : ℝ)^3133 := by
    have hnat : (164542239 : ℕ)^4157*100000000000000^3133 ≤ 42695076112869^3133*312500000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164542239 312500000 42695076112869 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696737093/5000000000 : ℝ)^4157 ≤ (44078992494417/100000000000000 : ℝ)^3133 := by
    have hnat : (2696737093 : ℕ)^4157*100000000000000^3133 ≤ 44078992494417^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696737093 5000000000 44078992494417 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136058807/625000000 : ℝ), (164542239/312500000 : ℝ), (2696737093/5000000000 : ℝ)] ![(132259313721/1000000000000 : ℝ), (42695076112869/100000000000000 : ℝ), (44078992494417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136058807/625000000 : ℝ)|^4157 ≤ (132259313721/1000000000000 : ℝ)^3133
        have hw : |(-136058807/625000000 : ℝ)|=(136058807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164542239/312500000 : ℝ)|^4157 ≤ (42695076112869/100000000000000 : ℝ)^3133
        have hw : |(164542239/312500000 : ℝ)|=(164542239/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696737093/5000000000 : ℝ)|^4157 ≤ (44078992494417/100000000000000 : ℝ)^3133
        have hw : |(2696737093/5000000000 : ℝ)|=(2696737093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s6_5 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656177329/5000000000 : ℝ)*x 0 + (-1056907717/5000000000 : ℝ)*x 1 + (5393474169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656177329/5000000000 : ℝ)^4157 ≤ (1728060623677/4000000000000 : ℝ)^3133 := by
    have hnat : (2656177329 : ℕ)^4157*4000000000000^3133 ≤ 1728060623677^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656177329 5000000000 1728060623677 4000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056907717/5000000000 : ℝ)^4157 ≤ (2543898416793/20000000000000 : ℝ)^3133 := by
    have hnat : (1056907717 : ℕ)^4157*20000000000000^3133 ≤ 2543898416793^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056907717 5000000000 2543898416793 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393474169/10000000000 : ℝ)^4157 ≤ (5509874038759/12500000000000 : ℝ)^3133 := by
    have hnat : (5393474169 : ℕ)^4157*12500000000000^3133 ≤ 5509874038759^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393474169 10000000000 5509874038759 12500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656177329/5000000000 : ℝ), (-1056907717/5000000000 : ℝ), (5393474169/10000000000 : ℝ)] ![(1728060623677/4000000000000 : ℝ), (2543898416793/20000000000000 : ℝ), (5509874038759/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656177329/5000000000 : ℝ)|^4157 ≤ (1728060623677/4000000000000 : ℝ)^3133
        have hw : |(2656177329/5000000000 : ℝ)|=(2656177329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056907717/5000000000 : ℝ)|^4157 ≤ (2543898416793/20000000000000 : ℝ)^3133
        have hw : |(-1056907717/5000000000 : ℝ)|=(1056907717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393474169/10000000000 : ℝ)|^4157 ≤ (5509874038759/12500000000000 : ℝ)^3133
        have hw : |(5393474169/10000000000 : ℝ)|=(5393474169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s6_6 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328088677/2500000000 : ℝ)*x 0 + (5393474051/10000000000 : ℝ)*x 1 + (-2113815527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328088677/2500000000 : ℝ)^4157 ≤ (21600758065719/50000000000000 : ℝ)^3133 := by
    have hnat : (1328088677 : ℕ)^4157*50000000000000^3133 ≤ 21600758065719^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328088677 2500000000 21600758065719 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393474051/10000000000 : ℝ)^4157 ≤ (88157982061/200000000000 : ℝ)^3133 := by
    have hnat : (5393474051 : ℕ)^4157*200000000000^3133 ≤ 88157982061^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393474051 10000000000 88157982061 200000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113815527/10000000000 : ℝ)^4157 ≤ (158993660331/1250000000000 : ℝ)^3133 := by
    have hnat : (2113815527 : ℕ)^4157*1250000000000^3133 ≤ 158993660331^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113815527 10000000000 158993660331 1250000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328088677/2500000000 : ℝ), (5393474051/10000000000 : ℝ), (-2113815527/10000000000 : ℝ)] ![(21600758065719/50000000000000 : ℝ), (88157982061/200000000000 : ℝ), (158993660331/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328088677/2500000000 : ℝ)|^4157 ≤ (21600758065719/50000000000000 : ℝ)^3133
        have hw : |(1328088677/2500000000 : ℝ)|=(1328088677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393474051/10000000000 : ℝ)|^4157 ≤ (88157982061/200000000000 : ℝ)^3133
        have hw : |(5393474051/10000000000 : ℝ)|=(5393474051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2113815527/10000000000 : ℝ)|^4157 ≤ (158993660331/1250000000000 : ℝ)^3133
        have hw : |(-2113815527/10000000000 : ℝ)|=(2113815527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s6_7 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (873526123/2000000000 : ℝ)*x 0 + (2248204097/5000000000 : ℝ)*x 1 + (169702459/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873526123/2000000000 : ℝ)^4157 ≤ (33316754721231/100000000000000 : ℝ)^3133 := by
    have hnat : (873526123 : ℕ)^4157*100000000000000^3133 ≤ 33316754721231^3133*2000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873526123 2000000000 33316754721231 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248204097/5000000000 : ℝ)^4157 ≤ (34626390855059/100000000000000 : ℝ)^3133 := by
    have hnat : (2248204097 : ℕ)^4157*100000000000000^3133 ≤ 34626390855059^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248204097 5000000000 34626390855059 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169702459/400000000 : ℝ)^4157 ≤ (32056854405237/100000000000000 : ℝ)^3133 := by
    have hnat : (169702459 : ℕ)^4157*100000000000000^3133 ≤ 32056854405237^3133*400000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169702459 400000000 32056854405237 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873526123/2000000000 : ℝ), (2248204097/5000000000 : ℝ), (169702459/400000000 : ℝ)] ![(33316754721231/100000000000000 : ℝ), (34626390855059/100000000000000 : ℝ), (32056854405237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873526123/2000000000 : ℝ)|^4157 ≤ (33316754721231/100000000000000 : ℝ)^3133
        have hw : |(873526123/2000000000 : ℝ)|=(873526123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248204097/5000000000 : ℝ)|^4157 ≤ (34626390855059/100000000000000 : ℝ)^3133
        have hw : |(2248204097/5000000000 : ℝ)|=(2248204097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169702459/400000000 : ℝ)|^4157 ≤ (32056854405237/100000000000000 : ℝ)^3133
        have hw : |(169702459/400000000 : ℝ)|=(169702459/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1121_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5659/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2809/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2821/25000 : ℝ) ^ (8313/2048 : ℝ) ≤ (14251806062301837/100000000000000000000 : ℝ) := by
    have hpowers : (2821/25000 : ℝ)^8313 ≤ (14251806062301837/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2821 : ℕ)^8313*100000000000000000000^2048 ≤ 14251806062301837^2048*25000^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 25000 14251806062301837 100000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/25000 : ℝ)) (X := (14251806062301837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (88/625 : ℝ) ^ (8313/2048 : ℝ) ≤ (2187702947919543/6250000000000000000 : ℝ) := by
    have hpowers : (88/625 : ℝ)^8313 ≤ (2187702947919543/6250000000000000000 : ℝ)^2048 := by
      have hnat : (88 : ℕ)^8313*6250000000000000000^2048 ≤ 2187702947919543^2048*625^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88 625 2187702947919543 6250000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88/625 : ℝ)) (X := (2187702947919543/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014251806062301837/50000000000000000000 : ℝ) ≤ (10000702142773253/10000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (50014251806062301837/50000000000000000000 : ℝ)^2048 ≤ (10000702142773253/10000000000000000 : ℝ)^8313 := by
      have hnat : (50014251806062301837 : ℕ)^2048*10000000000000000^8313 ≤ 10000702142773253^8313*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014251806062301837 50000000000000000000 10000702142773253 10000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000702142773253/10000000000000000 : ℝ)) (X := (50014251806062301837/50000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001970202129160581/4000000000000000000 : ℝ) ≤ (250030330696457/250000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (4001970202129160581/4000000000000000000 : ℝ)^2048 ≤ (250030330696457/250000000000000 : ℝ)^8313 := by
      have hnat : (4001970202129160581 : ℕ)^2048*250000000000000^8313 ≤ 250030330696457^8313*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001970202129160581 4000000000000000000 250030330696457 250000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250030330696457/250000000000000 : ℝ)) (X := (4001970202129160581/4000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127187702947919543/3125000000000000000 : ℝ) ≤ (10001724312943307/10000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (3127187702947919543/3125000000000000000 : ℝ)^2048 ≤ (10001724312943307/10000000000000000 : ℝ)^8313 := by
      have hnat : (3127187702947919543 : ℕ)^2048*10000000000000000^8313 ≤ 10001724312943307^8313*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127187702947919543 3125000000000000000 10001724312943307 10000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001724312943307/10000000000000000 : ℝ)) (X := (3127187702947919543/3125000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14251806062301837/100000000000000000000 : ℝ) ≤ ((9996576903789387/10000000000000000 : ℝ)+2*(731166073/400000000000 : ℝ)*(2821/25000 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (9996576903789387/10000000000000000 : ℝ)+2*(731166073/400000000000 : ℝ)*(2821/25000 : ℝ)=(10000702142773253/10000000000000000 : ℝ) by norm_num, show 1+2*(14251806062301837/100000000000000000000 : ℝ)=(50014251806062301837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2187702947919543/6250000000000000000 : ℝ)+(14251806062301837/100000000000000000000 : ℝ) ≤ ((9996576903789387/10000000000000000 : ℝ)+(731166073/400000000000 : ℝ)*((88/625 : ℝ)+(2821/25000 : ℝ)))^(8313/2048 : ℝ) := by
    rw [show (9996576903789387/10000000000000000 : ℝ)+(731166073/400000000000 : ℝ)*((88/625 : ℝ)+(2821/25000 : ℝ))=(250030330696457/250000000000000 : ℝ) by norm_num, show 1+(2187702947919543/6250000000000000000 : ℝ)+(14251806062301837/100000000000000000000 : ℝ)=(4001970202129160581/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2187702947919543/6250000000000000000 : ℝ) ≤ ((9996576903789387/10000000000000000 : ℝ)+2*(731166073/400000000000 : ℝ)*(88/625 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (9996576903789387/10000000000000000 : ℝ)+2*(731166073/400000000000 : ℝ)*(88/625 : ℝ)=(10001724312943307/10000000000000000 : ℝ) by norm_num, show 1+2*(2187702947919543/6250000000000000000 : ℝ)=(3127187702947919543/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9996576903789387/10000000000000000 : ℝ)*(X 1 0+X 2 0)+(731166073/400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (88/625 : ℝ)) (c := (9996576903789387/10000000000000000 : ℝ)) (alpha := (731166073/400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9996576903789387/10000000000000000 : ℝ)*(X 0 1+X 2 1)+(731166073/400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (88/625 : ℝ)) (c := (9996576903789387/10000000000000000 : ℝ)) (alpha := (731166073/400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9996576903789387/10000000000000000 : ℝ)*(X 0 2+X 1 2)+(731166073/400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (88/625 : ℝ)) (c := (9996576903789387/10000000000000000 : ℝ)) (alpha := (731166073/400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-272116973/1250000000 : ℝ)*X 0 0+(674225067/1250000000 : ℝ)*X 0 1+(5265026559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534492881/1000000000 : ℝ)*X 1 0+(-560565769/2500000000 : ℝ)*X 1 1+(5265026559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534492881/1000000000 : ℝ)*X 2 0+(5265026559/10000000000 : ℝ)*X 2 1+(-560565769/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218381033/500000000 : ℝ)*X 0 0+(1060478709/2500000000 : ℝ)*X 0 1+(4497052497/10000000000 : ℝ)*X 0 2+(218381033/500000000 : ℝ)*X 1 0+(1060478709/2500000000 : ℝ)*X 1 1+(4497052497/10000000000 : ℝ)*X 1 2+(218381033/500000000 : ℝ)*X 2 0+(1060478709/2500000000 : ℝ)*X 2 1+(4497052497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-136058807/625000000 : ℝ)*X 0 0+(164542239/312500000 : ℝ)*X 0 1+(2696737093/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656177329/5000000000 : ℝ)*X 1 0+(-1056907717/5000000000 : ℝ)*X 1 1+(5393474169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328088677/2500000000 : ℝ)*X 2 0+(5393474051/10000000000 : ℝ)*X 2 1+(-2113815527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873526123/2000000000 : ℝ)*X 0 0+(2248204097/5000000000 : ℝ)*X 0 1+(169702459/400000000 : ℝ)*X 0 2+(873526123/2000000000 : ℝ)*X 1 0+(2248204097/5000000000 : ℝ)*X 1 1+(169702459/400000000 : ℝ)*X 1 2+(873526123/2000000000 : ℝ)*X 2 0+(2248204097/5000000000 : ℝ)*X 2 1+(169702459/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1132568263535786695665003/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (457732681/100000000000000 : ℝ)*(base19) + (426004111/100000000000000 : ℝ)*(base23) + (8479347/50000000000000 : ℝ)*(lower2) + (14619809/25000000000000 : ℝ)*(upper3) + (34940881/100000000000000 : ℝ)*(upper5) + (5842517471513559/100000000000000 : ℝ)*(major0) + (5842517471513559/100000000000000 : ℝ)*(major1) + (5842517471513559/100000000000000 : ℝ)*(major2) + (7765557040332969/100000000000000 : ℝ)*(sp0) + (1553113780652341/20000000000000 : ℝ)*(sp1) + (3882784467495137/50000000000000 : ℝ)*(sp2) + (489932346947979/12500000000000 : ℝ)*(sp3) + (12320661417/100000000000000 : ℝ)*(sp4) + (6730944343/100000000000000 : ℝ)*(sp7) + (244966594158011/6250000000000 : ℝ)*(f.failure) + (1553113872198877/20000000000000 : ℝ)*(f.sum) + (148404782507/20000000000000000000000000 : ℝ)*base65 + (118605851973333/1000000000000000000000000000000 : ℝ)*base67 + (6262100883973333/1000000000000000000000000000000 : ℝ)*base69 + (4570269430973333/1000000000000000000000000000000 : ℝ)*base71 + (25112813527/20000000000000000000000000 : ℝ)*base73 + (733483021973333/1000000000000000000000000000000 : ℝ)*base75 + (2022096540973333/1000000000000000000000000000000 : ℝ)*base77 + (1363555285973333/1000000000000000000000000000000 : ℝ)*base79 + (88298451707/20000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (879759/312500000000000000000 : ℝ)*base89 + (879759/312500000000000000000 : ℝ)*base91 + (879759/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112480757046003953842521/31250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (987893499/100000000000000 : ℝ)*(base19) + (1124792061/100000000000000 : ℝ)*(base23) + (54121509/100000000000000 : ℝ)*(upper2) + (70090303/100000000000000 : ℝ)*(upper3) + (164068001/100000000000000 : ℝ)*(upper5) + (734025898927761/12500000000000 : ℝ)*(major0) + (734025898927761/12500000000000 : ℝ)*(major1) + (734025898927761/12500000000000 : ℝ)*(major2) + (231513431/800000000000 : ℝ)*(sp1) + (22670043801/100000000000000 : ℝ)*(sp2) + (1561006268679623/20000000000000 : ℝ)*(sp4) + (390250070816287/5000000000000 : ℝ)*(sp5) + (7805007548562253/100000000000000 : ℝ)*(sp6) + (1969691459733289/50000000000000 : ℝ)*(sp7) + (1969691459733289/50000000000000 : ℝ)*(f.failure) + (1561006268679623/20000000000000 : ℝ)*(f.sum) + (5591895539/1250000000000000000000000 : ℝ)*base65 + (1380053071202493/125000000000000000000000000000 : ℝ)*base68 + (113897857202493/125000000000000000000000000000 : ℝ)*base70 + (572501507202493/125000000000000000000000000000 : ℝ)*base72 + (2761821127/2500000000000000000000000 : ℝ)*base74 + (969478168422507/125000000000000000000000000000 : ℝ)*base75 + (624658790202493/125000000000000000000000000000 : ℝ)*base78 + (4022123588952493/125000000000000000000000000000 : ℝ)*base80 + (20990163391/5000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (17344941/2500000000000000000000 : ℝ)*base89 + (17344941/2500000000000000000000 : ℝ)*base91 + (17344941/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1121_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1121_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1121_s7_0 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21769651/100000000 : ℝ)*x 0 + (5393443327/10000000000 : ℝ)*x 1 + (1316341157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21769651/100000000 : ℝ)^4157 ≤ (13226126356561/100000000000000 : ℝ)^3133 := by
    have hnat : (21769651 : ℕ)^4157*100000000000000^3133 ≤ 13226126356561^3133*100000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21769651 100000000 13226126356561 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393443327/10000000000 : ℝ)^4157 ≤ (1377458058281/3125000000000 : ℝ)^3133 := by
    have hnat : (5393443327 : ℕ)^4157*3125000000000^3133 ≤ 1377458058281^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393443327 10000000000 1377458058281 3125000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316341157/2500000000 : ℝ)^4157 ≤ (8539043152829/20000000000000 : ℝ)^3133 := by
    have hnat : (1316341157 : ℕ)^4157*20000000000000^3133 ≤ 8539043152829^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316341157 2500000000 8539043152829 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21769651/100000000 : ℝ), (5393443327/10000000000 : ℝ), (1316341157/2500000000 : ℝ)] ![(13226126356561/100000000000000 : ℝ), (1377458058281/3125000000000 : ℝ), (8539043152829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21769651/100000000 : ℝ)|^4157 ≤ (13226126356561/100000000000000 : ℝ)^3133
        have hw : |(-21769651/100000000 : ℝ)|=(21769651/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393443327/10000000000 : ℝ)|^4157 ≤ (1377458058281/3125000000000 : ℝ)^3133
        have hw : |(5393443327/10000000000 : ℝ)|=(5393443327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316341157/2500000000 : ℝ)|^4157 ≤ (8539043152829/20000000000000 : ℝ)^3133
        have hw : |(1316341157/2500000000 : ℝ)|=(1316341157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s7_1 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344839689/10000000000 : ℝ)*x 0 + (-2241934403/10000000000 : ℝ)*x 1 + (2632682383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344839689/10000000000 : ℝ)^4157 ≤ (21776193519159/50000000000000 : ℝ)^3133 := by
    have hnat : (5344839689 : ℕ)^4157*50000000000000^3133 ≤ 21776193519159^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344839689 10000000000 21776193519159 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241934403/10000000000 : ℝ)^4157 ≤ (13752395694877/100000000000000 : ℝ)^3133 := by
    have hnat : (2241934403 : ℕ)^4157*100000000000000^3133 ≤ 13752395694877^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241934403 10000000000 13752395694877 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632682383/5000000000 : ℝ)^4157 ≤ (21347608624441/50000000000000 : ℝ)^3133 := by
    have hnat : (2632682383 : ℕ)^4157*50000000000000^3133 ≤ 21347608624441^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632682383 5000000000 21347608624441 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344839689/10000000000 : ℝ), (-2241934403/10000000000 : ℝ), (2632682383/5000000000 : ℝ)] ![(21776193519159/50000000000000 : ℝ), (13752395694877/100000000000000 : ℝ), (21347608624441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344839689/10000000000 : ℝ)|^4157 ≤ (21776193519159/50000000000000 : ℝ)^3133
        have hw : |(5344839689/10000000000 : ℝ)|=(5344839689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2241934403/10000000000 : ℝ)|^4157 ≤ (13752395694877/100000000000000 : ℝ)^3133
        have hw : |(-2241934403/10000000000 : ℝ)|=(2241934403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632682383/5000000000 : ℝ)|^4157 ≤ (21347608624441/50000000000000 : ℝ)^3133
        have hw : |(2632682383/5000000000 : ℝ)|=(2632682383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s7_2 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336209943/2500000000 : ℝ)*x 0 + (329085293/625000000 : ℝ)*x 1 + (-2241934397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336209943/2500000000 : ℝ)^4157 ≤ (8710477587139/20000000000000 : ℝ)^3133 := by
    have hnat : (1336209943 : ℕ)^4157*20000000000000^3133 ≤ 8710477587139^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336209943 2500000000 8710477587139 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329085293/625000000 : ℝ)^4157 ≤ (42695216409683/100000000000000 : ℝ)^3133 := by
    have hnat : (329085293 : ℕ)^4157*100000000000000^3133 ≤ 42695216409683^3133*625000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329085293 625000000 42695216409683 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241934397/10000000000 : ℝ)^4157 ≤ (13752395646043/100000000000000 : ℝ)^3133 := by
    have hnat : (2241934397 : ℕ)^4157*100000000000000^3133 ≤ 13752395646043^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241934397 10000000000 13752395646043 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336209943/2500000000 : ℝ), (329085293/625000000 : ℝ), (-2241934397/10000000000 : ℝ)] ![(8710477587139/20000000000000 : ℝ), (42695216409683/100000000000000 : ℝ), (13752395646043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336209943/2500000000 : ℝ)|^4157 ≤ (8710477587139/20000000000000 : ℝ)^3133
        have hw : |(1336209943/2500000000 : ℝ)|=(1336209943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329085293/625000000 : ℝ)|^4157 ≤ (42695216409683/100000000000000 : ℝ)^3133
        have hw : |(329085293/625000000 : ℝ)|=(329085293/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2241934397/10000000000 : ℝ)|^4157 ≤ (13752395646043/100000000000000 : ℝ)^3133
        have hw : |(-2241934397/10000000000 : ℝ)|=(2241934397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s7_3 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2183819263/5000000000 : ℝ)*x 0 + (1060650321/2500000000 : ℝ)*x 1 + (4496361297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183819263/5000000000 : ℝ)^4157 ≤ (16658417395441/50000000000000 : ℝ)^3133 := by
    have hnat : (2183819263 : ℕ)^4157*50000000000000^3133 ≤ 16658417395441^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183819263 5000000000 16658417395441 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060650321/2500000000 : ℝ)^4157 ≤ (32057253516813/100000000000000 : ℝ)^3133 := by
    have hnat : (1060650321 : ℕ)^4157*100000000000000^3133 ≤ 32057253516813^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060650321 2500000000 32057253516813 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496361297/10000000000 : ℝ)^4157 ≤ (8656477916899/25000000000000 : ℝ)^3133 := by
    have hnat : (4496361297 : ℕ)^4157*25000000000000^3133 ≤ 8656477916899^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496361297 10000000000 8656477916899 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183819263/5000000000 : ℝ), (1060650321/2500000000 : ℝ), (4496361297/10000000000 : ℝ)] ![(16658417395441/50000000000000 : ℝ), (32057253516813/100000000000000 : ℝ), (8656477916899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183819263/5000000000 : ℝ)|^4157 ≤ (16658417395441/50000000000000 : ℝ)^3133
        have hw : |(2183819263/5000000000 : ℝ)|=(2183819263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060650321/2500000000 : ℝ)|^4157 ≤ (32057253516813/100000000000000 : ℝ)^3133
        have hw : |(1060650321/2500000000 : ℝ)|=(1060650321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496361297/10000000000 : ℝ)|^4157 ≤ (8656477916899/25000000000000 : ℝ)^3133
        have hw : |(4496361297/10000000000 : ℝ)|=(4496361297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s7_4 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-17415759/80000000 : ℝ)*x 0 + (5265686427/10000000000 : ℝ)*x 1 + (539312049/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17415759/80000000 : ℝ)^4157 ≤ (2645232969781/20000000000000 : ℝ)^3133 := by
    have hnat : (17415759 : ℕ)^4157*20000000000000^3133 ≤ 2645232969781^3133*80000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17415759 80000000 2645232969781 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265686427/10000000000 : ℝ)^4157 ≤ (42698678022073/100000000000000 : ℝ)^3133 := by
    have hnat : (5265686427 : ℕ)^4157*100000000000000^3133 ≤ 42698678022073^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265686427 10000000000 42698678022073 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539312049/1000000000 : ℝ)^4157 ≤ (44075157116367/100000000000000 : ℝ)^3133 := by
    have hnat : (539312049 : ℕ)^4157*100000000000000^3133 ≤ 44075157116367^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539312049 1000000000 44075157116367 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17415759/80000000 : ℝ), (5265686427/10000000000 : ℝ), (539312049/1000000000 : ℝ)] ![(2645232969781/20000000000000 : ℝ), (42698678022073/100000000000000 : ℝ), (44075157116367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17415759/80000000 : ℝ)|^4157 ≤ (2645232969781/20000000000000 : ℝ)^3133
        have hw : |(-17415759/80000000 : ℝ)|=(17415759/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265686427/10000000000 : ℝ)|^4157 ≤ (42698678022073/100000000000000 : ℝ)^3133
        have hw : |(5265686427/10000000000 : ℝ)|=(5265686427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539312049/1000000000 : ℝ)|^4157 ≤ (44075157116367/100000000000000 : ℝ)^3133
        have hw : |(539312049/1000000000 : ℝ)|=(539312049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s7_5 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312441313/10000000000 : ℝ)*x 0 + (-2114178669/10000000000 : ℝ)*x 1 + (539312049/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312441313/10000000000 : ℝ)^4157 ≤ (43202450623627/100000000000000 : ℝ)^3133 := by
    have hnat : (5312441313 : ℕ)^4157*100000000000000^3133 ≤ 43202450623627^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312441313 10000000000 43202450623627 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114178669/10000000000 : ℝ)^4157 ≤ (12722392245703/100000000000000 : ℝ)^3133 := by
    have hnat : (2114178669 : ℕ)^4157*100000000000000^3133 ≤ 12722392245703^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114178669 10000000000 12722392245703 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539312049/1000000000 : ℝ)^4157 ≤ (44075157116367/100000000000000 : ℝ)^3133 := by
    have hnat : (539312049 : ℕ)^4157*100000000000000^3133 ≤ 44075157116367^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539312049 1000000000 44075157116367 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312441313/10000000000 : ℝ), (-2114178669/10000000000 : ℝ), (539312049/1000000000 : ℝ)] ![(43202450623627/100000000000000 : ℝ), (12722392245703/100000000000000 : ℝ), (44075157116367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312441313/10000000000 : ℝ)|^4157 ≤ (43202450623627/100000000000000 : ℝ)^3133
        have hw : |(5312441313/10000000000 : ℝ)|=(5312441313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114178669/10000000000 : ℝ)|^4157 ≤ (12722392245703/100000000000000 : ℝ)^3133
        have hw : |(-2114178669/10000000000 : ℝ)|=(2114178669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539312049/1000000000 : ℝ)|^4157 ≤ (44075157116367/100000000000000 : ℝ)^3133
        have hw : |(539312049/1000000000 : ℝ)|=(539312049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s7_6 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312441313/10000000000 : ℝ)*x 0 + (539312049/1000000000 : ℝ)*x 1 + (-2114178669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312441313/10000000000 : ℝ)^4157 ≤ (43202450623627/100000000000000 : ℝ)^3133 := by
    have hnat : (5312441313 : ℕ)^4157*100000000000000^3133 ≤ 43202450623627^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312441313 10000000000 43202450623627 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539312049/1000000000 : ℝ)^4157 ≤ (44075157116367/100000000000000 : ℝ)^3133 := by
    have hnat : (539312049 : ℕ)^4157*100000000000000^3133 ≤ 44075157116367^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539312049 1000000000 44075157116367 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114178669/10000000000 : ℝ)^4157 ≤ (12722392245703/100000000000000 : ℝ)^3133 := by
    have hnat : (2114178669 : ℕ)^4157*100000000000000^3133 ≤ 12722392245703^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114178669 10000000000 12722392245703 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312441313/10000000000 : ℝ), (539312049/1000000000 : ℝ), (-2114178669/10000000000 : ℝ)] ![(43202450623627/100000000000000 : ℝ), (44075157116367/100000000000000 : ℝ), (12722392245703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312441313/10000000000 : ℝ)|^4157 ≤ (43202450623627/100000000000000 : ℝ)^3133
        have hw : |(5312441313/10000000000 : ℝ)|=(5312441313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539312049/1000000000 : ℝ)|^4157 ≤ (44075157116367/100000000000000 : ℝ)^3133
        have hw : |(539312049/1000000000 : ℝ)|=(539312049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2114178669/10000000000 : ℝ)|^4157 ≤ (12722392245703/100000000000000 : ℝ)^3133
        have hw : |(-2114178669/10000000000 : ℝ)|=(2114178669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s7_7 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2183824093/5000000000 : ℝ)*x 0 + (4495723963/10000000000 : ℝ)*x 1 + (1060810263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183824093/5000000000 : ℝ)^4157 ≤ (832923314069/2500000000000 : ℝ)^3133 := by
    have hnat : (2183824093 : ℕ)^4157*2500000000000^3133 ≤ 832923314069^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183824093 5000000000 832923314069 2500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495723963/10000000000 : ℝ)^4157 ≤ (34619399633399/100000000000000 : ℝ)^3133 := by
    have hnat : (4495723963 : ℕ)^4157*100000000000000^3133 ≤ 34619399633399^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495723963 10000000000 34619399633399 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060810263/2500000000 : ℝ)^4157 ≤ (8015916945599/25000000000000 : ℝ)^3133 := by
    have hnat : (1060810263 : ℕ)^4157*25000000000000^3133 ≤ 8015916945599^3133*2500000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060810263 2500000000 8015916945599 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183824093/5000000000 : ℝ), (4495723963/10000000000 : ℝ), (1060810263/2500000000 : ℝ)] ![(832923314069/2500000000000 : ℝ), (34619399633399/100000000000000 : ℝ), (8015916945599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183824093/5000000000 : ℝ)|^4157 ≤ (832923314069/2500000000000 : ℝ)^3133
        have hw : |(2183824093/5000000000 : ℝ)|=(2183824093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495723963/10000000000 : ℝ)|^4157 ≤ (34619399633399/100000000000000 : ℝ)^3133
        have hw : |(4495723963/10000000000 : ℝ)|=(4495723963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060810263/2500000000 : ℝ)|^4157 ≤ (8015916945599/25000000000000 : ℝ)^3133
        have hw : |(1060810263/2500000000 : ℝ)|=(1060810263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1121_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (453/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7019/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5659/50000 : ℝ) ^ (8313/2048 : ℝ) ≤ (14426917544214921/100000000000000000000 : ℝ) := by
    have hpowers : (5659/50000 : ℝ)^8313 ≤ (14426917544214921/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5659 : ℕ)^8313*100000000000000000000^2048 ≤ 14426917544214921^2048*50000^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5659 50000 14426917544214921 100000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5659/50000 : ℝ)) (X := (14426917544214921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2809/20000 : ℝ) ^ (8313/2048 : ℝ) ≤ (17325701648295931/50000000000000000000 : ℝ) := by
    have hpowers : (2809/20000 : ℝ)^8313 ≤ (17325701648295931/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2809 : ℕ)^8313*50000000000000000000^2048 ≤ 17325701648295931^2048*20000^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 20000 17325701648295931 50000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/20000 : ℝ)) (X := (17325701648295931/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014426917544214921/50000000000000000000 : ℝ) ≤ (10000710769041091/10000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (50014426917544214921/50000000000000000000 : ℝ)^2048 ≤ (10000710769041091/10000000000000000 : ℝ)^8313 := by
      have hnat : (50014426917544214921 : ℕ)^2048*10000000000000000^8313 ≤ 10000710769041091^8313*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014426917544214921 50000000000000000000 10000710769041091 10000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000710769041091/10000000000000000 : ℝ)) (X := (50014426917544214921/50000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049078320840806783/100000000000000000000 : ℝ) ≤ (5000604437735991/5000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (100049078320840806783/100000000000000000000 : ℝ)^2048 ≤ (5000604437735991/5000000000000000 : ℝ)^8313 := by
      have hnat : (100049078320840806783 : ℕ)^2048*5000000000000000^8313 ≤ 5000604437735991^8313*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049078320840806783 100000000000000000000 5000604437735991 5000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000604437735991/5000000000000000 : ℝ)) (X := (100049078320840806783/100000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017325701648295931/25000000000000000000 : ℝ) ≤ (10001706981902873/10000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (25017325701648295931/25000000000000000000 : ℝ)^2048 ≤ (10001706981902873/10000000000000000 : ℝ)^8313 := by
      have hnat : (25017325701648295931 : ℕ)^2048*10000000000000000^8313 ≤ 10001706981902873^8313*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017325701648295931 25000000000000000000 10001706981902873 10000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001706981902873/10000000000000000 : ℝ)) (X := (25017325701648295931/25000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14426917544214921/100000000000000000000 : ℝ) ≤ ((27260663130005406481/27270000000000000000 : ℝ)+2*(498106430891/272700000000000 : ℝ)*(5659/50000 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (27260663130005406481/27270000000000000000 : ℝ)+2*(498106430891/272700000000000 : ℝ)*(5659/50000 : ℝ)=(10000710769041091/10000000000000000 : ℝ) by norm_num, show 1+2*(14426917544214921/100000000000000000000 : ℝ)=(50014426917544214921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17325701648295931/50000000000000000000 : ℝ)+(14426917544214921/100000000000000000000 : ℝ) ≤ ((27260663130005406481/27270000000000000000 : ℝ)+(498106430891/272700000000000 : ℝ)*((2809/20000 : ℝ)+(5659/50000 : ℝ)))^(8313/2048 : ℝ) := by
    rw [show (27260663130005406481/27270000000000000000 : ℝ)+(498106430891/272700000000000 : ℝ)*((2809/20000 : ℝ)+(5659/50000 : ℝ))=(5000604437735991/5000000000000000 : ℝ) by norm_num, show 1+(17325701648295931/50000000000000000000 : ℝ)+(14426917544214921/100000000000000000000 : ℝ)=(100049078320840806783/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17325701648295931/50000000000000000000 : ℝ) ≤ ((27260663130005406481/27270000000000000000 : ℝ)+2*(498106430891/272700000000000 : ℝ)*(2809/20000 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (27260663130005406481/27270000000000000000 : ℝ)+2*(498106430891/272700000000000 : ℝ)*(2809/20000 : ℝ)=(10001706981902873/10000000000000000 : ℝ) by norm_num, show 1+2*(17325701648295931/50000000000000000000 : ℝ)=(25017325701648295931/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27260663130005406481/27270000000000000000 : ℝ)*(X 1 0+X 2 0)+(498106430891/272700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (27260663130005406481/27270000000000000000 : ℝ)) (alpha := (498106430891/272700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27260663130005406481/27270000000000000000 : ℝ)*(X 0 1+X 2 1)+(498106430891/272700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (27260663130005406481/27270000000000000000 : ℝ)) (alpha := (498106430891/272700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27260663130005406481/27270000000000000000 : ℝ)*(X 0 2+X 1 2)+(498106430891/272700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (27260663130005406481/27270000000000000000 : ℝ)) (alpha := (498106430891/272700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-21769651/100000000 : ℝ)*X 0 0+(5393443327/10000000000 : ℝ)*X 0 1+(1316341157/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344839689/10000000000 : ℝ)*X 1 0+(-2241934403/10000000000 : ℝ)*X 1 1+(2632682383/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336209943/2500000000 : ℝ)*X 2 0+(329085293/625000000 : ℝ)*X 2 1+(-2241934397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183819263/5000000000 : ℝ)*X 0 0+(1060650321/2500000000 : ℝ)*X 0 1+(4496361297/10000000000 : ℝ)*X 0 2+(2183819263/5000000000 : ℝ)*X 1 0+(1060650321/2500000000 : ℝ)*X 1 1+(4496361297/10000000000 : ℝ)*X 1 2+(2183819263/5000000000 : ℝ)*X 2 0+(1060650321/2500000000 : ℝ)*X 2 1+(4496361297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17415759/80000000 : ℝ)*X 0 0+(5265686427/10000000000 : ℝ)*X 0 1+(539312049/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312441313/10000000000 : ℝ)*X 1 0+(-2114178669/10000000000 : ℝ)*X 1 1+(539312049/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312441313/10000000000 : ℝ)*X 2 0+(539312049/1000000000 : ℝ)*X 2 1+(-2114178669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183824093/5000000000 : ℝ)*X 0 0+(4495723963/10000000000 : ℝ)*X 0 1+(1060810263/2500000000 : ℝ)*X 0 2+(2183824093/5000000000 : ℝ)*X 1 0+(4495723963/10000000000 : ℝ)*X 1 1+(1060810263/2500000000 : ℝ)*X 1 2+(2183824093/5000000000 : ℝ)*X 2 0+(4495723963/10000000000 : ℝ)*X 2 1+(1060810263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4431003529815818773699/1515000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1100731441/100000000000000 : ℝ)*(base19) + (1115086651/100000000000000 : ℝ)*(base23) + (139503/80000000000 : ℝ)*(upper3) + (57131851/100000000000000 : ℝ)*(upper4) + (129963933/100000000000000 : ℝ)*(upper5) + (734283432308121/12500000000000 : ℝ)*(major0) + (734283432308121/12500000000000 : ℝ)*(major1) + (734283432308121/12500000000000 : ℝ)*(major2) + (975966773470507/12500000000000 : ℝ)*(sp0) + (1951942166157439/25000000000000 : ℝ)*(sp1) + (3903884325137273/50000000000000 : ℝ)*(sp2) + (985186762453487/25000000000000 : ℝ)*(sp3) + (17788798571/50000000000000 : ℝ)*(sp4) + (3600852591/20000000000000 : ℝ)*(sp7) + (1970382527038451/50000000000000 : ℝ)*(f.failure) + (3903884882680599/50000000000000 : ℝ)*(f.sum) + (3999445946191/1136250000000000000000000000 : ℝ)*base66 + (81394132463303437/12625000000000000000000000000000 : ℝ)*base68 + (81190565509071563/12625000000000000000000000000000 : ℝ)*base69 + (98365292740678437/12625000000000000000000000000000 : ℝ)*base72 + (5202201454691/4545000000000000000000000000 : ℝ)*base73 + (140279020365571563/12625000000000000000000000000000 : ℝ)*base75 + (4896379705821563/12625000000000000000000000000000 : ℝ)*base77 + (172629776951053437/12625000000000000000000000000000 : ℝ)*base80 + (5175533656033/2272500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4414881/2500000000000000000000 : ℝ)*base90 + (4414881/2500000000000000000000 : ℝ)*base92 + (4414881/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4117027034213982647462792273/454500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1662869101/100000000000000 : ℝ)*(base19) + (903869333/50000000000000 : ℝ)*(base23) + (90821127/50000000000000 : ℝ)*(upper3) + (65946751/100000000000000 : ℝ)*(lower4) + (92590313/50000000000000 : ℝ)*(upper5) + (5903928826331189/100000000000000 : ℝ)*(major0) + (5903928826331189/100000000000000 : ℝ)*(major1) + (5903928826331189/100000000000000 : ℝ)*(major2) + (45745230583/100000000000000 : ℝ)*(sp1) + (49144767443/100000000000000 : ℝ)*(sp2) + (490449618983161/6250000000000 : ℝ)*(sp4) + (1961786623907723/25000000000000 : ℝ)*(sp5) + (7847142951224467/100000000000000 : ℝ)*(sp6) + (1980331723493141/50000000000000 : ℝ)*(sp7) + (1980331723493141/50000000000000 : ℝ)*(f.failure) + (490449618983161/6250000000000 : ℝ)*(f.sum) + (5625358086379/13635000000000000000000000000 : ℝ)*base65 + (2095077344025215101/303000000000000000000000000000000 : ℝ)*base67 + (3062137178067215101/303000000000000000000000000000000 : ℝ)*base69 + (2763414498474215101/303000000000000000000000000000000 : ℝ)*base71 + (155091328681/213046875000000000000000000 : ℝ)*base73 + (4113270412413215101/303000000000000000000000000000000 : ℝ)*base75 + (2663576518422215101/303000000000000000000000000000000 : ℝ)*base77 + (2336510876439215101/303000000000000000000000000000000 : ℝ)*base79 + (10705702980551/13635000000000000000000000000 : ℝ)*base82 + (18961271/2500000000000000000000 : ℝ)*base90 + (18961271/2500000000000000000000 : ℝ)*base92 + (18961271/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1121_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1121_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1121_s8_0 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2176970087/10000000000 : ℝ)*x 0 + (67417151/125000000 : ℝ)*x 1 + (52654327/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176970087/10000000000 : ℝ)^4157 ≤ (2645233311577/20000000000000 : ℝ)^3133 := by
    have hnat : (2176970087 : ℕ)^4157*20000000000000^3133 ≤ 2645233311577^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176970087 10000000000 2645233311577 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67417151/125000000 : ℝ)^4157 ≤ (44077885277777/100000000000000 : ℝ)^3133 := by
    have hnat : (67417151 : ℕ)^4157*100000000000000^3133 ≤ 44077885277777^3133*125000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67417151 125000000 44077885277777 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52654327/100000000 : ℝ)^4157 ≤ (42695948149783/100000000000000 : ℝ)^3133 := by
    have hnat : (52654327 : ℕ)^4157*100000000000000^3133 ≤ 42695948149783^3133*100000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52654327 100000000 42695948149783 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2176970087/10000000000 : ℝ), (67417151/125000000 : ℝ), (52654327/100000000 : ℝ)] ![(2645233311577/20000000000000 : ℝ), (44077885277777/100000000000000 : ℝ), (42695948149783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2176970087/10000000000 : ℝ)|^4157 ≤ (2645233311577/20000000000000 : ℝ)^3133
        have hw : |(-2176970087/10000000000 : ℝ)|=(2176970087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67417151/125000000 : ℝ)|^4157 ≤ (44077885277777/100000000000000 : ℝ)^3133
        have hw : |(67417151/125000000 : ℝ)|=(67417151/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52654327/100000000 : ℝ)|^4157 ≤ (42695948149783/100000000000000 : ℝ)^3133
        have hw : |(52654327/100000000 : ℝ)|=(52654327/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s8_1 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133620553/250000000 : ℝ)*x 0 + (-1120933981/5000000000 : ℝ)*x 1 + (5265432683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133620553/250000000 : ℝ)^4157 ≤ (8710439417277/20000000000000 : ℝ)^3133 := by
    have hnat : (133620553 : ℕ)^4157*20000000000000^3133 ≤ 8710439417277^3133*250000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133620553 250000000 8710439417277 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120933981/5000000000 : ℝ)^4157 ≤ (13751854929167/100000000000000 : ℝ)^3133 := by
    have hnat : (1120933981 : ℕ)^4157*100000000000000^3133 ≤ 13751854929167^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120933981 5000000000 13751854929167 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265432683/10000000000 : ℝ)^4157 ≤ (266849674793/625000000000 : ℝ)^3133 := by
    have hnat : (5265432683 : ℕ)^4157*625000000000^3133 ≤ 266849674793^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265432683 10000000000 266849674793 625000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133620553/250000000 : ℝ), (-1120933981/5000000000 : ℝ), (5265432683/10000000000 : ℝ)] ![(8710439417277/20000000000000 : ℝ), (13751854929167/100000000000000 : ℝ), (266849674793/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133620553/250000000 : ℝ)|^4157 ≤ (8710439417277/20000000000000 : ℝ)^3133
        have hw : |(133620553/250000000 : ℝ)|=(133620553/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1120933981/5000000000 : ℝ)|^4157 ≤ (13751854929167/100000000000000 : ℝ)^3133
        have hw : |(-1120933981/5000000000 : ℝ)|=(1120933981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265432683/10000000000 : ℝ)|^4157 ≤ (266849674793/625000000000 : ℝ)^3133
        have hw : |(5265432683/10000000000 : ℝ)|=(5265432683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s8_2 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672411061/5000000000 : ℝ)*x 0 + (5265432689/10000000000 : ℝ)*x 1 + (-2241867953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672411061/5000000000 : ℝ)^4157 ≤ (5444024638501/12500000000000 : ℝ)^3133 := by
    have hnat : (2672411061 : ℕ)^4157*12500000000000^3133 ≤ 5444024638501^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672411061 5000000000 5444024638501 12500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265432689/10000000000 : ℝ)^4157 ≤ (21347974015717/50000000000000 : ℝ)^3133 := by
    have hnat : (5265432689 : ℕ)^4157*50000000000000^3133 ≤ 21347974015717^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265432689 10000000000 21347974015717 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241867953/10000000000 : ℝ)^4157 ≤ (3437963713979/25000000000000 : ℝ)^3133 := by
    have hnat : (2241867953 : ℕ)^4157*25000000000000^3133 ≤ 3437963713979^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241867953 10000000000 3437963713979 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672411061/5000000000 : ℝ), (5265432689/10000000000 : ℝ), (-2241867953/10000000000 : ℝ)] ![(5444024638501/12500000000000 : ℝ), (21347974015717/50000000000000 : ℝ), (3437963713979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672411061/5000000000 : ℝ)|^4157 ≤ (5444024638501/12500000000000 : ℝ)^3133
        have hw : |(2672411061/5000000000 : ℝ)|=(2672411061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265432689/10000000000 : ℝ)|^4157 ≤ (21347974015717/50000000000000 : ℝ)^3133
        have hw : |(5265432689/10000000000 : ℝ)|=(5265432689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2241867953/10000000000 : ℝ)|^4157 ≤ (3437963713979/25000000000000 : ℝ)^3133
        have hw : |(-2241867953/10000000000 : ℝ)|=(2241867953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s8_3 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4367641929/10000000000 : ℝ)*x 0 + (132585589/312500000 : ℝ)*x 1 + (89924459/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367641929/10000000000 : ℝ)^4157 ≤ (333168692337/1000000000000 : ℝ)^3133 := by
    have hnat : (4367641929 : ℕ)^4157*1000000000000^3133 ≤ 333168692337^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367641929 10000000000 333168692337 1000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132585589/312500000 : ℝ)^4157 ≤ (6411726539279/20000000000000 : ℝ)^3133 := by
    have hnat : (132585589 : ℕ)^4157*20000000000000^3133 ≤ 6411726539279^3133*312500000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132585589 312500000 6411726539279 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89924459/200000000 : ℝ)^4157 ≤ (34624498065411/100000000000000 : ℝ)^3133 := by
    have hnat : (89924459 : ℕ)^4157*100000000000000^3133 ≤ 34624498065411^3133*200000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89924459 200000000 34624498065411 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367641929/10000000000 : ℝ), (132585589/312500000 : ℝ), (89924459/200000000 : ℝ)] ![(333168692337/1000000000000 : ℝ), (6411726539279/20000000000000 : ℝ), (34624498065411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367641929/10000000000 : ℝ)|^4157 ≤ (333168692337/1000000000000 : ℝ)^3133
        have hw : |(4367641929/10000000000 : ℝ)|=(4367641929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132585589/312500000 : ℝ)|^4157 ≤ (6411726539279/20000000000000 : ℝ)^3133
        have hw : |(132585589/312500000 : ℝ)|=(132585589/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89924459/200000000 : ℝ)|^4157 ≤ (34624498065411/100000000000000 : ℝ)^3133
        have hw : |(89924459/200000000 : ℝ)|=(89924459/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s8_4 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-68030471/312500000 : ℝ)*x 0 + (2632876793/5000000000 : ℝ)*x 1 + (539304999/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68030471/312500000 : ℝ)^4157 ≤ (13226206743117/100000000000000 : ℝ)^3133 := by
    have hnat : (68030471 : ℕ)^4157*100000000000000^3133 ≤ 13226206743117^3133*312500000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68030471 312500000 13226206743117 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632876793/5000000000 : ℝ)^4157 ≤ (4269940059917/10000000000000 : ℝ)^3133 := by
    have hnat : (2632876793 : ℕ)^4157*10000000000000^3133 ≤ 4269940059917^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632876793 5000000000 4269940059917 10000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539304999/1000000000 : ℝ)^4157 ≤ (44074392644399/100000000000000 : ℝ)^3133 := by
    have hnat : (539304999 : ℕ)^4157*100000000000000^3133 ≤ 44074392644399^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539304999 1000000000 44074392644399 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68030471/312500000 : ℝ), (2632876793/5000000000 : ℝ), (539304999/1000000000 : ℝ)] ![(13226206743117/100000000000000 : ℝ), (4269940059917/10000000000000 : ℝ), (44074392644399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68030471/312500000 : ℝ)|^4157 ≤ (13226206743117/100000000000000 : ℝ)^3133
        have hw : |(-68030471/312500000 : ℝ)|=(68030471/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632876793/5000000000 : ℝ)|^4157 ≤ (4269940059917/10000000000000 : ℝ)^3133
        have hw : |(2632876793/5000000000 : ℝ)|=(2632876793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539304999/1000000000 : ℝ)|^4157 ≤ (44074392644399/100000000000000 : ℝ)^3133
        have hw : |(539304999/1000000000 : ℝ)|=(539304999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s8_5 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531245917/1000000000 : ℝ)*x 0 + (-2114250081/10000000000 : ℝ)*x 1 + (2696525069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531245917/1000000000 : ℝ)^4157 ≤ (21601321653137/50000000000000 : ℝ)^3133 := by
    have hnat : (531245917 : ℕ)^4157*50000000000000^3133 ≤ 21601321653137^3133*1000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531245917 1000000000 21601321653137 50000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114250081/10000000000 : ℝ)^4157 ≤ (254459248733/2000000000000 : ℝ)^3133 := by
    have hnat : (2114250081 : ℕ)^4157*2000000000000^3133 ≤ 254459248733^3133*10000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114250081 10000000000 254459248733 2000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696525069/5000000000 : ℝ)^4157 ≤ (8814878849849/20000000000000 : ℝ)^3133 := by
    have hnat : (2696525069 : ℕ)^4157*20000000000000^3133 ≤ 8814878849849^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696525069 5000000000 8814878849849 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531245917/1000000000 : ℝ), (-2114250081/10000000000 : ℝ), (2696525069/5000000000 : ℝ)] ![(21601321653137/50000000000000 : ℝ), (254459248733/2000000000000 : ℝ), (8814878849849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531245917/1000000000 : ℝ)|^4157 ≤ (21601321653137/50000000000000 : ℝ)^3133
        have hw : |(531245917/1000000000 : ℝ)|=(531245917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114250081/10000000000 : ℝ)|^4157 ≤ (254459248733/2000000000000 : ℝ)^3133
        have hw : |(-2114250081/10000000000 : ℝ)|=(2114250081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696525069/5000000000 : ℝ)|^4157 ≤ (8814878849849/20000000000000 : ℝ)^3133
        have hw : |(2696525069/5000000000 : ℝ)|=(2696525069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s8_6 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664057293/1250000000 : ℝ)*x 0 + (2696525029/5000000000 : ℝ)*x 1 + (-422850261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664057293/1250000000 : ℝ)^4157 ≤ (4320263439347/10000000000000 : ℝ)^3133 := by
    have hnat : (664057293 : ℕ)^4157*10000000000000^3133 ≤ 4320263439347^3133*1250000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664057293 1250000000 4320263439347 10000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696525029/5000000000 : ℝ)^4157 ≤ (44074393381761/100000000000000 : ℝ)^3133 := by
    have hnat : (2696525029 : ℕ)^4157*100000000000000^3133 ≤ 44074393381761^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696525029 5000000000 44074393381761 100000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422850261/2000000000 : ℝ)^4157 ≤ (3180743052441/25000000000000 : ℝ)^3133 := by
    have hnat : (422850261 : ℕ)^4157*25000000000000^3133 ≤ 3180743052441^3133*2000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422850261 2000000000 3180743052441 25000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664057293/1250000000 : ℝ), (2696525029/5000000000 : ℝ), (-422850261/2000000000 : ℝ)] ![(4320263439347/10000000000000 : ℝ), (44074393381761/100000000000000 : ℝ), (3180743052441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664057293/1250000000 : ℝ)|^4157 ≤ (4320263439347/10000000000000 : ℝ)^3133
        have hw : |(664057293/1250000000 : ℝ)|=(664057293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696525029/5000000000 : ℝ)|^4157 ≤ (44074393381761/100000000000000 : ℝ)^3133
        have hw : |(2696525029/5000000000 : ℝ)|=(2696525029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422850261/2000000000 : ℝ)|^4157 ≤ (3180743052441/25000000000000 : ℝ)^3133
        have hw : |(-422850261/2000000000 : ℝ)|=(422850261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1121_s8_7 (p : ℝ) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2183825503/5000000000 : ℝ)*x 0 + (2247793521/5000000000 : ℝ)*x 1 + (530422217/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183825503/5000000000 : ℝ)^4157 ≤ (266535688839/800000000000 : ℝ)^3133 := by
    have hnat : (2183825503 : ℕ)^4157*800000000000^3133 ≤ 266535688839^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183825503 5000000000 266535688839 800000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247793521/5000000000 : ℝ)^4157 ≤ (6923600133309/20000000000000 : ℝ)^3133 := by
    have hnat : (2247793521 : ℕ)^4157*20000000000000^3133 ≤ 6923600133309^3133*5000000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247793521 5000000000 6923600133309 20000000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530422217/1250000000 : ℝ)^4157 ≤ (4008129775853/12500000000000 : ℝ)^3133 := by
    have hnat : (530422217 : ℕ)^4157*12500000000000^3133 ≤ 4008129775853^3133*1250000000^4157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530422217 1250000000 4008129775853 12500000000000 4157 3133 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4157/1024 : ℝ)) 4157 3133 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183825503/5000000000 : ℝ), (2247793521/5000000000 : ℝ), (530422217/1250000000 : ℝ)] ![(266535688839/800000000000 : ℝ), (6923600133309/20000000000000 : ℝ), (4008129775853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183825503/5000000000 : ℝ)|^4157 ≤ (266535688839/800000000000 : ℝ)^3133
        have hw : |(2183825503/5000000000 : ℝ)|=(2183825503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247793521/5000000000 : ℝ)|^4157 ≤ (6923600133309/20000000000000 : ℝ)^3133
        have hw : |(2247793521/5000000000 : ℝ)|=(2247793521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530422217/1250000000 : ℝ)|^4157 ≤ (4008129775853/12500000000000 : ℝ)^3133
        have hw : |(530422217/1250000000 : ℝ)|=(530422217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1121_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5663/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3509/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (453/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (453/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (453/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (453/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (453/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (453/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (453/4000 : ℝ) ^ (8313/2048 : ℝ) ≤ (14463170260255563/100000000000000000000 : ℝ) := by
    have hpowers : (453/4000 : ℝ)^8313 ≤ (14463170260255563/100000000000000000000 : ℝ)^2048 := by
      have hnat : (453 : ℕ)^8313*100000000000000000000^2048 ≤ 14463170260255563^2048*4000^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        453 4000 14463170260255563 100000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (453/4000 : ℝ)) (X := (14463170260255563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7019/50000 : ℝ) ^ (8313/2048 : ℝ) ≤ (34581355598599017/100000000000000000000 : ℝ) := by
    have hpowers : (7019/50000 : ℝ)^8313 ≤ (34581355598599017/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7019 : ℕ)^8313*100000000000000000000^2048 ≤ 34581355598599017^2048*50000^8313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7019 50000 34581355598599017 100000000000000000000 8313 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7019/50000 : ℝ)) (X := (34581355598599017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014463170260255563/50000000000000000000 : ℝ) ≤ (2500178138726057/2500000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (50014463170260255563/50000000000000000000 : ℝ)^2048 ≤ (2500178138726057/2500000000000000 : ℝ)^8313 := by
      have hnat : (50014463170260255563 : ℕ)^2048*2500000000000000^8313 ≤ 2500178138726057^8313*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014463170260255563 50000000000000000000 2500178138726057 2500000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500178138726057/2500000000000000 : ℝ)) (X := (50014463170260255563/50000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002452226292942729/5000000000000000000 : ℝ) ≤ (10001208043202727/10000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (5002452226292942729/5000000000000000000 : ℝ)^2048 ≤ (10001208043202727/10000000000000000 : ℝ)^8313 := by
      have hnat : (5002452226292942729 : ℕ)^2048*10000000000000000^8313 ≤ 10001208043202727^8313*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002452226292942729 5000000000000000000 10001208043202727 10000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001208043202727/10000000000000000 : ℝ)) (X := (5002452226292942729/5000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034581355598599017/50000000000000000000 : ℝ) ≤ (5000851765750613/5000000000000000 : ℝ) ^ (8313/2048 : ℝ) := by
    have hpowers : (50034581355598599017/50000000000000000000 : ℝ)^2048 ≤ (5000851765750613/5000000000000000 : ℝ)^8313 := by
      have hnat : (50034581355598599017 : ℕ)^2048*5000000000000000^8313 ≤ 5000851765750613^8313*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034581355598599017 50000000000000000000 5000851765750613 5000000000000000 2048 8313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000851765750613/5000000000000000 : ℝ)) (X := (50034581355598599017/50000000000000000000 : ℝ)) (by norm_num) 8313 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14463170260255563/100000000000000000000 : ℝ) ≤ ((13560355175747084107/13565000000000000000 : ℝ)+2*(495488298499/271300000000000 : ℝ)*(453/4000 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (13560355175747084107/13565000000000000000 : ℝ)+2*(495488298499/271300000000000 : ℝ)*(453/4000 : ℝ)=(2500178138726057/2500000000000000 : ℝ) by norm_num, show 1+2*(14463170260255563/100000000000000000000 : ℝ)=(50014463170260255563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34581355598599017/100000000000000000000 : ℝ)+(14463170260255563/100000000000000000000 : ℝ) ≤ ((13560355175747084107/13565000000000000000 : ℝ)+(495488298499/271300000000000 : ℝ)*((7019/50000 : ℝ)+(453/4000 : ℝ)))^(8313/2048 : ℝ) := by
    rw [show (13560355175747084107/13565000000000000000 : ℝ)+(495488298499/271300000000000 : ℝ)*((7019/50000 : ℝ)+(453/4000 : ℝ))=(10001208043202727/10000000000000000 : ℝ) by norm_num, show 1+(34581355598599017/100000000000000000000 : ℝ)+(14463170260255563/100000000000000000000 : ℝ)=(5002452226292942729/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34581355598599017/100000000000000000000 : ℝ) ≤ ((13560355175747084107/13565000000000000000 : ℝ)+2*(495488298499/271300000000000 : ℝ)*(7019/50000 : ℝ))^(8313/2048 : ℝ) := by
    rw [show (13560355175747084107/13565000000000000000 : ℝ)+2*(495488298499/271300000000000 : ℝ)*(7019/50000 : ℝ)=(5000851765750613/5000000000000000 : ℝ) by norm_num, show 1+2*(34581355598599017/100000000000000000000 : ℝ)=(50034581355598599017/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13560355175747084107/13565000000000000000 : ℝ)*(X 1 0+X 2 0)+(495488298499/271300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (13560355175747084107/13565000000000000000 : ℝ)) (alpha := (495488298499/271300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13560355175747084107/13565000000000000000 : ℝ)*(X 0 1+X 2 1)+(495488298499/271300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (13560355175747084107/13565000000000000000 : ℝ)) (alpha := (495488298499/271300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13560355175747084107/13565000000000000000 : ℝ)*(X 0 2+X 1 2)+(495488298499/271300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8313/2048 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (13560355175747084107/13565000000000000000 : ℝ)) (alpha := (495488298499/271300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2176970087/10000000000 : ℝ)*X 0 0+(67417151/125000000 : ℝ)*X 0 1+(52654327/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133620553/250000000 : ℝ)*X 1 0+(-1120933981/5000000000 : ℝ)*X 1 1+(5265432683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672411061/5000000000 : ℝ)*X 2 0+(5265432689/10000000000 : ℝ)*X 2 1+(-2241867953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367641929/10000000000 : ℝ)*X 0 0+(132585589/312500000 : ℝ)*X 0 1+(89924459/200000000 : ℝ)*X 0 2+(4367641929/10000000000 : ℝ)*X 1 0+(132585589/312500000 : ℝ)*X 1 1+(89924459/200000000 : ℝ)*X 1 2+(4367641929/10000000000 : ℝ)*X 2 0+(132585589/312500000 : ℝ)*X 2 1+(89924459/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-68030471/312500000 : ℝ)*X 0 0+(2632876793/5000000000 : ℝ)*X 0 1+(539304999/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531245917/1000000000 : ℝ)*X 1 0+(-2114250081/10000000000 : ℝ)*X 1 1+(2696525069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664057293/1250000000 : ℝ)*X 2 0+(2696525029/5000000000 : ℝ)*X 2 1+(-422850261/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183825503/5000000000 : ℝ)*X 0 0+(2247793521/5000000000 : ℝ)*X 0 1+(530422217/1250000000 : ℝ)*X 0 2+(2183825503/5000000000 : ℝ)*X 1 0+(2247793521/5000000000 : ℝ)*X 1 1+(530422217/1250000000 : ℝ)*X 1 2+(2183825503/5000000000 : ℝ)*X 2 0+(2247793521/5000000000 : ℝ)*X 2 1+(530422217/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1121_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (707144406090466717101284343/84781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (412799799/25000000000000 : ℝ)*(base19) + (763404079/50000000000000 : ℝ)*(base23) + (8506007/12500000000000 : ℝ)*(lower2) + (50316431/25000000000000 : ℝ)*(upper3) + (3841171/3125000000000 : ℝ)*(upper5) + (1470169898646533/25000000000000 : ℝ)*(major0) + (1470169898646533/25000000000000 : ℝ)*(major1) + (1470169898646533/25000000000000 : ℝ)*(major2) + (3908123907430621/50000000000000 : ℝ)*(sp0) + (3908145305228553/50000000000000 : ℝ)*(sp1) + (488518170928009/6250000000000 : ℝ)*(sp2) + (157801696859809/4000000000000 : ℝ)*(sp3) + (2222339753/5000000000000 : ℝ)*(sp4) + (2422799369/10000000000000 : ℝ)*(sp7) + (789013329897783/20000000000000 : ℝ)*(f.failure) + (3908146130828151/50000000000000 : ℝ)*(f.sum) + (70125276265953/13565000000000000000000000000 : ℝ)*base65 + (1513520461174198969/339125000000000000000000000000000 : ℝ)*base68 + (1307396247195448969/339125000000000000000000000000000 : ℝ)*base70 + (1381211379937323969/339125000000000000000000000000000 : ℝ)*base72 + (2650178275087/3391250000000000000000000000 : ℝ)*base73 + (2680015739492198969/339125000000000000000000000000000 : ℝ)*base76 + (1025946416484676031/339125000000000000000000000000000 : ℝ)*base77 + (2798658623455198969/339125000000000000000000000000000 : ℝ)*base80 + (8540301545201/6782500000000000000000000000 : ℝ)*base82 + (5503027/1000000000000000000000 : ℝ)*base89 + (5503027/1000000000000000000000 : ℝ)*base91 + (5503027/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4169245789189534371734457861/678250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (590137547/100000000000000 : ℝ)*(base19) + (9516453/6250000000000 : ℝ)*(upper1) + (15752443/4000000000000 : ℝ)*(upper2) + (3104019/20000000000000 : ℝ)*(upper3) + (64455707/50000000000000 : ℝ)*(lower4) + (5910323946328741/100000000000000 : ℝ)*(major0) + (5910323946328741/100000000000000 : ℝ)*(major1) + (5910323946328741/100000000000000 : ℝ)*(major2) + (1047572219/6250000000000 : ℝ)*(sp0) + (28945184507/50000000000000 : ℝ)*(sp1) + (7855677299504949/100000000000000 : ℝ)*(sp4) + (7855635580153891/100000000000000 : ℝ)*(sp5) + (7855694060660453/100000000000000 : ℝ)*(sp6) + (247809601693431/6250000000000 : ℝ)*(sp7) + (247809601693431/6250000000000 : ℝ)*(f.failure) + (7855694060660453/100000000000000 : ℝ)*(f.sum) + (109794512978241/13565000000000000000000000000 : ℝ)*base66 + (8549786942357369287/1356500000000000000000000000000000 : ℝ)*base67 + (3113947298307369287/1356500000000000000000000000000000 : ℝ)*base69 + (4912149524632630713/1356500000000000000000000000000000 : ℝ)*base72 + (14092161545143/6782500000000000000000000000 : ℝ)*base74 + (19144712271557630713/1356500000000000000000000000000000 : ℝ)*base76 + (149307165468265630713/1356500000000000000000000000000000 : ℝ)*base78 + (317017142102630713/1356500000000000000000000000000000 : ℝ)*base80 + (33017845725293/1695625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (513739/312500000000000000000 : ℝ)*base89 + (513739/312500000000000000000 : ℝ)*base91 + (513739/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1121_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1121_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1121_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1121_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1121_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1121_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8313/2048 : ℝ) ≤ p) (hpb : p ≤ (4157/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74532069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1121_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1468_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:09:33.586562+00:00
-- url     : https://prove2.me/submissions/1cdb7616-693d-473d-bab9-25e1885bae16

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
theorem support_rectangle_w1468_s6_0 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-77401301/400000000 : ℝ)*x 0 + (5439019039/10000000000 : ℝ)*x 1 + (5215085149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77401301/400000000 : ℝ)^4433 ≤ (94517607569/800000000000 : ℝ)^3409 := by
    have hnat : (77401301 : ℕ)^4433*800000000000^3409 ≤ 94517607569^3409*400000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77401301 400000000 94517607569 800000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439019039/10000000000 : ℝ)^4433 ≤ (11324418326397/25000000000000 : ℝ)^3409 := by
    have hnat : (5439019039 : ℕ)^4433*25000000000000^3409 ≤ 11324418326397^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439019039 10000000000 11324418326397 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215085149/10000000000 : ℝ)^4433 ≤ (42887625738203/100000000000000 : ℝ)^3409 := by
    have hnat : (5215085149 : ℕ)^4433*100000000000000^3409 ≤ 42887625738203^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215085149 10000000000 42887625738203 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77401301/400000000 : ℝ), (5439019039/10000000000 : ℝ), (5215085149/10000000000 : ℝ)] ![(94517607569/800000000000 : ℝ), (11324418326397/25000000000000 : ℝ), (42887625738203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77401301/400000000 : ℝ)|^4433 ≤ (94517607569/800000000000 : ℝ)^3409
        have hw : |(-77401301/400000000 : ℝ)|=(77401301/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439019039/10000000000 : ℝ)|^4433 ≤ (11324418326397/25000000000000 : ℝ)^3409
        have hw : |(5439019039/10000000000 : ℝ)|=(5439019039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215085149/10000000000 : ℝ)|^4433 ≤ (42887625738203/100000000000000 : ℝ)^3409
        have hw : |(5215085149/10000000000 : ℝ)|=(5215085149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s6_1 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338479721/2500000000 : ℝ)*x 0 + (-2049827871/10000000000 : ℝ)*x 1 + (2607542647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338479721/2500000000 : ℝ)^4433 ≤ (11094554362859/25000000000000 : ℝ)^3409 := by
    have hnat : (1338479721 : ℕ)^4433*25000000000000^3409 ≤ 11094554362859^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338479721 2500000000 11094554362859 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049827871/10000000000 : ℝ)^4433 ≤ (12734155237241/100000000000000 : ℝ)^3409 := by
    have hnat : (2049827871 : ℕ)^4433*100000000000000^3409 ≤ 12734155237241^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049827871 10000000000 12734155237241 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607542647/5000000000 : ℝ)^4433 ≤ (42887627288837/100000000000000 : ℝ)^3409 := by
    have hnat : (2607542647 : ℕ)^4433*100000000000000^3409 ≤ 42887627288837^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607542647 5000000000 42887627288837 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338479721/2500000000 : ℝ), (-2049827871/10000000000 : ℝ), (2607542647/5000000000 : ℝ)] ![(11094554362859/25000000000000 : ℝ), (12734155237241/100000000000000 : ℝ), (42887627288837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338479721/2500000000 : ℝ)|^4433 ≤ (11094554362859/25000000000000 : ℝ)^3409
        have hw : |(1338479721/2500000000 : ℝ)|=(1338479721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049827871/10000000000 : ℝ)|^4433 ≤ (12734155237241/100000000000000 : ℝ)^3409
        have hw : |(-2049827871/10000000000 : ℝ)|=(2049827871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607542647/5000000000 : ℝ)|^4433 ≤ (42887627288837/100000000000000 : ℝ)^3409
        have hw : |(2607542647/5000000000 : ℝ)|=(2607542647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s6_2 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669239881/1250000000 : ℝ)*x 0 + (651885647/1250000000 : ℝ)*x 1 + (-2049827809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669239881/1250000000 : ℝ)^4433 ≤ (44378219219153/100000000000000 : ℝ)^3409 := by
    have hnat : (669239881 : ℕ)^4433*100000000000000^3409 ≤ 44378219219153^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669239881 1250000000 44378219219153 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651885647/1250000000 : ℝ)^4433 ≤ (21443813013471/50000000000000 : ℝ)^3409 := by
    have hnat : (651885647 : ℕ)^4433*50000000000000^3409 ≤ 21443813013471^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651885647 1250000000 21443813013471 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049827809/10000000000 : ℝ)^4433 ≤ (6367077368191/50000000000000 : ℝ)^3409 := by
    have hnat : (2049827809 : ℕ)^4433*50000000000000^3409 ≤ 6367077368191^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049827809 10000000000 6367077368191 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669239881/1250000000 : ℝ), (651885647/1250000000 : ℝ), (-2049827809/10000000000 : ℝ)] ![(44378219219153/100000000000000 : ℝ), (21443813013471/50000000000000 : ℝ), (6367077368191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669239881/1250000000 : ℝ)|^4433 ≤ (44378219219153/100000000000000 : ℝ)^3409
        have hw : |(669239881/1250000000 : ℝ)|=(669239881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651885647/1250000000 : ℝ)|^4433 ≤ (21443813013471/50000000000000 : ℝ)^3409
        have hw : |(651885647/1250000000 : ℝ)|=(651885647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2049827809/10000000000 : ℝ)|^4433 ≤ (6367077368191/50000000000000 : ℝ)^3409
        have hw : |(-2049827809/10000000000 : ℝ)|=(2049827809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s6_3 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171628477/400000000 : ℝ)*x 0 + (2025442247/5000000000 : ℝ)*x 1 + (2271485229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171628477/400000000 : ℝ)^4433 ≤ (16638648085081/50000000000000 : ℝ)^3409 := by
    have hnat : (171628477 : ℕ)^4433*50000000000000^3409 ≤ 16638648085081^3409*400000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171628477 400000000 16638648085081 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025442247/5000000000 : ℝ)^4433 ≤ (30879137380917/100000000000000 : ℝ)^3409 := by
    have hnat : (2025442247 : ℕ)^4433*100000000000000^3409 ≤ 30879137380917^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025442247 5000000000 30879137380917 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271485229/5000000000 : ℝ)^4433 ≤ (8960891605959/25000000000000 : ℝ)^3409 := by
    have hnat : (2271485229 : ℕ)^4433*25000000000000^3409 ≤ 8960891605959^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271485229 5000000000 8960891605959 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171628477/400000000 : ℝ), (2025442247/5000000000 : ℝ), (2271485229/5000000000 : ℝ)] ![(16638648085081/50000000000000 : ℝ), (30879137380917/100000000000000 : ℝ), (8960891605959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171628477/400000000 : ℝ)|^4433 ≤ (16638648085081/50000000000000 : ℝ)^3409
        have hw : |(171628477/400000000 : ℝ)|=(171628477/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2025442247/5000000000 : ℝ)|^4433 ≤ (30879137380917/100000000000000 : ℝ)^3409
        have hw : |(2025442247/5000000000 : ℝ)|=(2025442247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2271485229/5000000000 : ℝ)|^4433 ≤ (8960891605959/25000000000000 : ℝ)^3409
        have hw : |(2271485229/5000000000 : ℝ)|=(2271485229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s6_4 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-387012683/2000000000 : ℝ)*x 0 + (5216228173/10000000000 : ℝ)*x 1 + (5437867639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387012683/2000000000 : ℝ)^4433 ≤ (2953736551167/25000000000000 : ℝ)^3409 := by
    have hnat : (387012683 : ℕ)^4433*25000000000000^3409 ≤ 2953736551167^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387012683 2000000000 2953736551167 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216228173/10000000000 : ℝ)^4433 ≤ (42899849671609/100000000000000 : ℝ)^3409 := by
    have hnat : (5216228173 : ℕ)^4433*100000000000000^3409 ≤ 42899849671609^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216228173 10000000000 42899849671609 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437867639/10000000000 : ℝ)^4433 ≤ (11321301027319/25000000000000 : ℝ)^3409 := by
    have hnat : (5437867639 : ℕ)^4433*25000000000000^3409 ≤ 11321301027319^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437867639 10000000000 11321301027319 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-387012683/2000000000 : ℝ), (5216228173/10000000000 : ℝ), (5437867639/10000000000 : ℝ)] ![(2953736551167/25000000000000 : ℝ), (42899849671609/100000000000000 : ℝ), (11321301027319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-387012683/2000000000 : ℝ)|^4433 ≤ (2953736551167/25000000000000 : ℝ)^3409
        have hw : |(-387012683/2000000000 : ℝ)|=(387012683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216228173/10000000000 : ℝ)|^4433 ≤ (42899849671609/100000000000000 : ℝ)^3409
        have hw : |(5216228173/10000000000 : ℝ)|=(5216228173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437867639/10000000000 : ℝ)|^4433 ≤ (11321301027319/25000000000000 : ℝ)^3409
        have hw : |(5437867639/10000000000 : ℝ)|=(5437867639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s6_5 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647779403/5000000000 : ℝ)*x 0 + (-456761357/2500000000 : ℝ)*x 1 + (2718933797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647779403/5000000000 : ℝ)^4433 ≤ (10937550164801/25000000000000 : ℝ)^3409 := by
    have hnat : (2647779403 : ℕ)^4433*25000000000000^3409 ≤ 10937550164801^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647779403 5000000000 10937550164801 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456761357/2500000000 : ℝ)^4433 ≤ (2741148925411/25000000000000 : ℝ)^3409 := by
    have hnat : (456761357 : ℕ)^4433*25000000000000^3409 ≤ 2741148925411^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456761357 2500000000 2741148925411 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718933797/5000000000 : ℝ)^4433 ≤ (1132130090549/2500000000000 : ℝ)^3409 := by
    have hnat : (2718933797 : ℕ)^4433*2500000000000^3409 ≤ 1132130090549^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718933797 5000000000 1132130090549 2500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647779403/5000000000 : ℝ), (-456761357/2500000000 : ℝ), (2718933797/5000000000 : ℝ)] ![(10937550164801/25000000000000 : ℝ), (2741148925411/25000000000000 : ℝ), (1132130090549/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647779403/5000000000 : ℝ)|^4433 ≤ (10937550164801/25000000000000 : ℝ)^3409
        have hw : |(2647779403/5000000000 : ℝ)|=(2647779403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456761357/2500000000 : ℝ)|^4433 ≤ (2741148925411/25000000000000 : ℝ)^3409
        have hw : |(-456761357/2500000000 : ℝ)|=(456761357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718933797/5000000000 : ℝ)|^4433 ≤ (1132130090549/2500000000000 : ℝ)^3409
        have hw : |(2718933797/5000000000 : ℝ)|=(2718933797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s6_6 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647779389/5000000000 : ℝ)*x 0 + (339866727/625000000 : ℝ)*x 1 + (-1827045413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647779389/5000000000 : ℝ)^4433 ≤ (4375020035839/10000000000000 : ℝ)^3409 := by
    have hnat : (2647779389 : ℕ)^4433*10000000000000^3409 ≤ 4375020035839^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647779389 5000000000 4375020035839 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339866727/625000000 : ℝ)^4433 ≤ (45285204033471/100000000000000 : ℝ)^3409 := by
    have hnat : (339866727 : ℕ)^4433*100000000000000^3409 ≤ 45285204033471^3409*625000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339866727 625000000 45285204033471 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1827045413/10000000000 : ℝ)^4433 ≤ (2192919116917/20000000000000 : ℝ)^3409 := by
    have hnat : (1827045413 : ℕ)^4433*20000000000000^3409 ≤ 2192919116917^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827045413 10000000000 2192919116917 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647779389/5000000000 : ℝ), (339866727/625000000 : ℝ), (-1827045413/10000000000 : ℝ)] ![(4375020035839/10000000000000 : ℝ), (45285204033471/100000000000000 : ℝ), (2192919116917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647779389/5000000000 : ℝ)|^4433 ≤ (4375020035839/10000000000000 : ℝ)^3409
        have hw : |(2647779389/5000000000 : ℝ)|=(2647779389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339866727/625000000 : ℝ)|^4433 ≤ (45285204033471/100000000000000 : ℝ)^3409
        have hw : |(339866727/625000000 : ℝ)|=(339866727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1827045413/10000000000 : ℝ)|^4433 ≤ (2192919116917/20000000000000 : ℝ)^3409
        have hw : |(-1827045413/10000000000 : ℝ)|=(1827045413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_s6_7 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (858155983/2000000000 : ℝ)*x 0 + (908091741/2000000000 : ℝ)*x 1 + (2026707313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858155983/2000000000 : ℝ)^4433 ≤ (16638990936131/50000000000000 : ℝ)^3409 := by
    have hnat : (858155983 : ℕ)^4433*50000000000000^3409 ≤ 16638990936131^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858155983 2000000000 16638990936131 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908091741/2000000000 : ℝ)^4433 ≤ (1790889914721/5000000000000 : ℝ)^3409 := by
    have hnat : (908091741 : ℕ)^4433*5000000000000^3409 ≤ 1790889914721^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908091741 2000000000 1790889914721 5000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026707313/5000000000 : ℝ)^4433 ≤ (6180843966023/20000000000000 : ℝ)^3409 := by
    have hnat : (2026707313 : ℕ)^4433*20000000000000^3409 ≤ 6180843966023^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026707313 5000000000 6180843966023 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(858155983/2000000000 : ℝ), (908091741/2000000000 : ℝ), (2026707313/5000000000 : ℝ)] ![(16638990936131/50000000000000 : ℝ), (1790889914721/5000000000000 : ℝ), (6180843966023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(858155983/2000000000 : ℝ)|^4433 ≤ (16638990936131/50000000000000 : ℝ)^3409
        have hw : |(858155983/2000000000 : ℝ)|=(858155983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(908091741/2000000000 : ℝ)|^4433 ≤ (1790889914721/5000000000000 : ℝ)^3409
        have hw : |(908091741/2000000000 : ℝ)|=(908091741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2026707313/5000000000 : ℝ)|^4433 ≤ (6180843966023/20000000000000 : ℝ)^3409
        have hw : |(2026707313/5000000000 : ℝ)|=(2026707313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1468_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5367/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (967/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2683/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2683/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2683/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2683/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2683/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2683/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2683/25000 : ℝ) ^ (4431/1024 : ℝ) ≤ (3195812963747539/50000000000000000000 : ℝ) := by
    have hpowers : (2683/25000 : ℝ)^4431 ≤ (3195812963747539/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2683 : ℕ)^4431*50000000000000000000^1024 ≤ 3195812963747539^1024*25000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2683 25000 3195812963747539 50000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2683/25000 : ℝ)) (X := (3195812963747539/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7737/50000 : ℝ) ^ (4431/1024 : ℝ) ≤ (6227591542087379/20000000000000000000 : ℝ) := by
    have hpowers : (7737/50000 : ℝ)^4431 ≤ (6227591542087379/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7737 : ℕ)^4431*20000000000000000000^1024 ≤ 6227591542087379^1024*50000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7737 50000 6227591542087379 20000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7737/50000 : ℝ)) (X := (6227591542087379/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003195812963747539/25000000000000000000 : ℝ) ≤ (5000147702625073/5000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (25003195812963747539/25000000000000000000 : ℝ)^1024 ≤ (5000147702625073/5000000000000000 : ℝ)^4431 := by
      have hnat : (25003195812963747539 : ℕ)^1024*5000000000000000^4431 ≤ 5000147702625073^4431*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003195812963747539 25000000000000000000 5000147702625073 5000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000147702625073/5000000000000000 : ℝ)) (X := (25003195812963747539/25000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037529583637931973/100000000000000000000 : ℝ) ≤ (1250108397511981/1250000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (100037529583637931973/100000000000000000000 : ℝ)^1024 ≤ (1250108397511981/1250000000000000 : ℝ)^4431 := by
      have hnat : (100037529583637931973 : ℕ)^1024*1250000000000000^4431 ≤ 1250108397511981^4431*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037529583637931973 100000000000000000000 1250108397511981 1250000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250108397511981/1250000000000000 : ℝ)) (X := (100037529583637931973/100000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006227591542087379/10000000000000000000 : ℝ) ≤ (200028779098831/200000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (10006227591542087379/10000000000000000000 : ℝ)^1024 ≤ (200028779098831/200000000000000 : ℝ)^4431 := by
      have hnat : (10006227591542087379 : ℕ)^1024*200000000000000^4431 ≤ 200028779098831^4431*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006227591542087379 10000000000000000000 200028779098831 200000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200028779098831/200000000000000 : ℝ)) (X := (10006227591542087379/10000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3195812963747539/50000000000000000000 : ℝ) ≤ ((11852282059102011151/11855000000000000000 : ℝ)+2*(285887422851/237100000000000 : ℝ)*(2683/25000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (11852282059102011151/11855000000000000000 : ℝ)+2*(285887422851/237100000000000 : ℝ)*(2683/25000 : ℝ)=(5000147702625073/5000000000000000 : ℝ) by norm_num, show 1+2*(3195812963747539/50000000000000000000 : ℝ)=(25003195812963747539/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6227591542087379/20000000000000000000 : ℝ)+(3195812963747539/50000000000000000000 : ℝ) ≤ ((11852282059102011151/11855000000000000000 : ℝ)+(285887422851/237100000000000 : ℝ)*((7737/50000 : ℝ)+(2683/25000 : ℝ)))^(4431/1024 : ℝ) := by
    rw [show (11852282059102011151/11855000000000000000 : ℝ)+(285887422851/237100000000000 : ℝ)*((7737/50000 : ℝ)+(2683/25000 : ℝ))=(1250108397511981/1250000000000000 : ℝ) by norm_num, show 1+(6227591542087379/20000000000000000000 : ℝ)+(3195812963747539/50000000000000000000 : ℝ)=(100037529583637931973/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6227591542087379/20000000000000000000 : ℝ) ≤ ((11852282059102011151/11855000000000000000 : ℝ)+2*(285887422851/237100000000000 : ℝ)*(7737/50000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (11852282059102011151/11855000000000000000 : ℝ)+2*(285887422851/237100000000000 : ℝ)*(7737/50000 : ℝ)=(200028779098831/200000000000000 : ℝ) by norm_num, show 1+2*(6227591542087379/20000000000000000000 : ℝ)=(10006227591542087379/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11852282059102011151/11855000000000000000 : ℝ)*(X 1 0+X 2 0)+(285887422851/237100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (2683/25000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (11852282059102011151/11855000000000000000 : ℝ)) (alpha := (285887422851/237100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11852282059102011151/11855000000000000000 : ℝ)*(X 0 1+X 2 1)+(285887422851/237100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (2683/25000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (11852282059102011151/11855000000000000000 : ℝ)) (alpha := (285887422851/237100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11852282059102011151/11855000000000000000 : ℝ)*(X 0 2+X 1 2)+(285887422851/237100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (2683/25000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (11852282059102011151/11855000000000000000 : ℝ)) (alpha := (285887422851/237100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-77401301/400000000 : ℝ)*X 0 0+(5439019039/10000000000 : ℝ)*X 0 1+(5215085149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338479721/2500000000 : ℝ)*X 1 0+(-2049827871/10000000000 : ℝ)*X 1 1+(2607542647/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669239881/1250000000 : ℝ)*X 2 0+(651885647/1250000000 : ℝ)*X 2 1+(-2049827809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((171628477/400000000 : ℝ)*X 0 0+(2025442247/5000000000 : ℝ)*X 0 1+(2271485229/5000000000 : ℝ)*X 0 2+(171628477/400000000 : ℝ)*X 1 0+(2025442247/5000000000 : ℝ)*X 1 1+(2271485229/5000000000 : ℝ)*X 1 2+(171628477/400000000 : ℝ)*X 2 0+(2025442247/5000000000 : ℝ)*X 2 1+(2271485229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-387012683/2000000000 : ℝ)*X 0 0+(5216228173/10000000000 : ℝ)*X 0 1+(5437867639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647779403/5000000000 : ℝ)*X 1 0+(-456761357/2500000000 : ℝ)*X 1 1+(2718933797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647779389/5000000000 : ℝ)*X 2 0+(339866727/625000000 : ℝ)*X 2 1+(-1827045413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((858155983/2000000000 : ℝ)*X 0 0+(908091741/2000000000 : ℝ)*X 0 1+(2026707313/5000000000 : ℝ)*X 0 2+(858155983/2000000000 : ℝ)*X 1 0+(908091741/2000000000 : ℝ)*X 1 1+(2026707313/5000000000 : ℝ)*X 1 2+(858155983/2000000000 : ℝ)*X 2 0+(908091741/2000000000 : ℝ)*X 2 1+(2026707313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (361315310457271699776835209/59275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (974064383/100000000000000 : ℝ)*(base19) + (275543373/25000000000000 : ℝ)*(base23) + (4647903/100000000000000 : ℝ)*(lower2) + (11141383/12500000000000 : ℝ)*(upper3) + (20465513/12500000000000 : ℝ)*(upper5) + (324891119684151/10000000000000 : ℝ)*(major0) + (324891119684151/10000000000000 : ℝ)*(major1) + (324891119684151/10000000000000 : ℝ)*(major2) + (4465620342125233/100000000000000 : ℝ)*(sp0) + (4465639194673671/100000000000000 : ℝ)*(sp1) + (2232819533282281/50000000000000 : ℝ)*(sp2) + (127010862974253/6250000000000 : ℝ)*(sp3) + (19826612821/100000000000000 : ℝ)*(sp4) + (513385689/6250000000000 : ℝ)*(sp7) + (63505688179971/3125000000000 : ℝ)*(f.failure) + (2232820084369027/50000000000000 : ℝ)*(f.sum) + (1754725071141/1185500000000000000000000000 : ℝ)*base65 + (704009022824582199/118550000000000000000000000000000 : ℝ)*base68 + (505928402906182199/118550000000000000000000000000000 : ℝ)*base70 + (464389808295182199/118550000000000000000000000000000 : ℝ)*base72 + (4710329980859/2371000000000000000000000000 : ℝ)*base74 + (831493962056082199/118550000000000000000000000000000 : ℝ)*base76 + (349286508707782199/118550000000000000000000000000000 : ℝ)*base78 + (284415024966182199/118550000000000000000000000000000 : ℝ)*base80 + (9380784357/37046875000000000000000000 : ℝ)*base82 + (311811/312500000000000000000 : ℝ)*base89 + (311811/312500000000000000000 : ℝ)*base91 + (311811/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1567521232936067374106545737/296375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59667761/6250000000000 : ℝ)*(base19) + (983449331/100000000000000 : ℝ)*(base23) + (29967647/10000000000000 : ℝ)*(lower1) + (115559913/100000000000000 : ℝ)*(upper3) + (4353457/20000000000000 : ℝ)*(lower4) + (107744841/100000000000000 : ℝ)*(upper5) + (3282506928804771/100000000000000 : ℝ)*(major0) + (3282506928804771/100000000000000 : ℝ)*(major1) + (3282506928804771/100000000000000 : ℝ)*(major2) + (522492959/50000000000000 : ℝ)*(sp2) + (2255908826295461/50000000000000 : ℝ)*(sp4) + (2255908348953373/50000000000000 : ℝ)*(sp5) + (4511815624155673/100000000000000 : ℝ)*(sp6) + (410639205743859/20000000000000 : ℝ)*(sp7) + (410639205743859/20000000000000 : ℝ)*(f.failure) + (2255908826295461/50000000000000 : ℝ)*(f.sum) + (5726078041263/1481875000000000000000000000 : ℝ)*base66 + (5086196029375448579/1185500000000000000000000000000000 : ℝ)*base68 + (4918803542756051421/1185500000000000000000000000000000 : ℝ)*base69 + (95774239204064551421/1185500000000000000000000000000000 : ℝ)*base71 + (606460798523/370468750000000000000000000 : ℝ)*base73 + (13859351415063051421/1185500000000000000000000000000000 : ℝ)*base75 + (8380947517203551421/1185500000000000000000000000000000 : ℝ)*base77 + (9322391837795551421/1185500000000000000000000000000000 : ℝ)*base79 + (437070278081/2963750000000000000000000000 : ℝ)*base82 + (14594781/2000000000000000000000 : ℝ)*base90 + (14594781/2000000000000000000000 : ℝ)*base92 + (14594781/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1468_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5367/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (967/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1468_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1468_box_0 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1713182431/10000000000 : ℝ)*x 0 + (5407606249/10000000000 : ℝ)*x 1 + (1351901627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1713182431/10000000000 : ℝ)^4433 ≤ (5042228419529/50000000000000 : ℝ)^3409 := by
    have hnat : (1713182431 : ℕ)^4433*50000000000000^3409 ≤ 5042228419529^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713182431 10000000000 5042228419529 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407606249/10000000000 : ℝ)^4433 ≤ (44957770171169/100000000000000 : ℝ)^3409 := by
    have hnat : (5407606249 : ℕ)^4433*100000000000000^3409 ≤ 44957770171169^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407606249 10000000000 44957770171169 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351901627/2500000000 : ℝ)^4433 ≤ (44957772971247/100000000000000 : ℝ)^3409 := by
    have hnat : (1351901627 : ℕ)^4433*100000000000000^3409 ≤ 44957772971247^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351901627 2500000000 44957772971247 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1713182431/10000000000 : ℝ), (5407606249/10000000000 : ℝ), (1351901627/2500000000 : ℝ)] ![(5042228419529/50000000000000 : ℝ), (44957770171169/100000000000000 : ℝ), (44957772971247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1713182431/10000000000 : ℝ)|^4433 ≤ (5042228419529/50000000000000 : ℝ)^3409
        have hw : |(-1713182431/10000000000 : ℝ)|=(1713182431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407606249/10000000000 : ℝ)|^4433 ≤ (44957770171169/100000000000000 : ℝ)^3409
        have hw : |(5407606249/10000000000 : ℝ)|=(5407606249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351901627/2500000000 : ℝ)|^4433 ≤ (44957772971247/100000000000000 : ℝ)^3409
        have hw : |(1351901627/2500000000 : ℝ)|=(1351901627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_1 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105399141/200000000 : ℝ)*x 0 + (-237967917/1250000000 : ℝ)*x 1 + (1351901521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105399141/200000000 : ℝ)^4433 ≤ (4347535244293/10000000000000 : ℝ)^3409 := by
    have hnat : (105399141 : ℕ)^4433*10000000000000^3409 ≤ 4347535244293^3409*200000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105399141 200000000 4347535244293 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237967917/1250000000 : ℝ)^4433 ≤ (11566879154311/100000000000000 : ℝ)^3409 := by
    have hnat : (237967917 : ℕ)^4433*100000000000000^3409 ≤ 11566879154311^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237967917 1250000000 11566879154311 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351901521/2500000000 : ℝ)^4433 ≤ (8991553677467/20000000000000 : ℝ)^3409 := by
    have hnat : (1351901521 : ℕ)^4433*20000000000000^3409 ≤ 8991553677467^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351901521 2500000000 8991553677467 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105399141/200000000 : ℝ), (-237967917/1250000000 : ℝ), (1351901521/2500000000 : ℝ)] ![(4347535244293/10000000000000 : ℝ), (11566879154311/100000000000000 : ℝ), (8991553677467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105399141/200000000 : ℝ)|^4433 ≤ (4347535244293/10000000000000 : ℝ)^3409
        have hw : |(105399141/200000000 : ℝ)|=(105399141/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-237967917/1250000000 : ℝ)|^4433 ≤ (11566879154311/100000000000000 : ℝ)^3409
        have hw : |(-237967917/1250000000 : ℝ)|=(237967917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351901521/2500000000 : ℝ)|^4433 ≤ (8991553677467/20000000000000 : ℝ)^3409
        have hw : |(1351901521/2500000000 : ℝ)|=(1351901521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_2 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2634978279/5000000000 : ℝ)*x 0 + (2703803169/5000000000 : ℝ)*x 1 + (-1903743657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2634978279/5000000000 : ℝ)^4433 ≤ (434753471649/1000000000000 : ℝ)^3409 := by
    have hnat : (2634978279 : ℕ)^4433*1000000000000^3409 ≤ 434753471649^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634978279 5000000000 434753471649 1000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703803169/5000000000 : ℝ)^4433 ≤ (22478885566679/50000000000000 : ℝ)^3409 := by
    have hnat : (2703803169 : ℕ)^4433*50000000000000^3409 ≤ 22478885566679^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703803169 5000000000 22478885566679 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1903743657/10000000000 : ℝ)^4433 ≤ (722930105657/6250000000000 : ℝ)^3409 := by
    have hnat : (1903743657 : ℕ)^4433*6250000000000^3409 ≤ 722930105657^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903743657 10000000000 722930105657 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2634978279/5000000000 : ℝ), (2703803169/5000000000 : ℝ), (-1903743657/10000000000 : ℝ)] ![(434753471649/1000000000000 : ℝ), (22478885566679/50000000000000 : ℝ), (722930105657/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2634978279/5000000000 : ℝ)|^4433 ≤ (434753471649/1000000000000 : ℝ)^3409
        have hw : |(2634978279/5000000000 : ℝ)|=(2634978279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703803169/5000000000 : ℝ)|^4433 ≤ (22478885566679/50000000000000 : ℝ)^3409
        have hw : |(2703803169/5000000000 : ℝ)|=(2703803169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1903743657/10000000000 : ℝ)|^4433 ≤ (722930105657/6250000000000 : ℝ)^3409
        have hw : |(-1903743657/10000000000 : ℝ)|=(1903743657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_3 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2247970477/5000000000 : ℝ)*x 0 + (4195383293/10000000000 : ℝ)*x 1 + (4195382741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2247970477/5000000000 : ℝ)^4433 ≤ (35361801666937/100000000000000 : ℝ)^3409 := by
    have hnat : (2247970477 : ℕ)^4433*100000000000000^3409 ≤ 35361801666937^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247970477 5000000000 35361801666937 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4195383293/10000000000 : ℝ)^4433 ≤ (32319101920847/100000000000000 : ℝ)^3409 := by
    have hnat : (4195383293 : ℕ)^4433*100000000000000^3409 ≤ 32319101920847^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195383293 10000000000 32319101920847 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4195382741/10000000000 : ℝ)^4433 ≤ (40398870489/125000000000 : ℝ)^3409 := by
    have hnat : (4195382741 : ℕ)^4433*125000000000^3409 ≤ 40398870489^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195382741 10000000000 40398870489 125000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2247970477/5000000000 : ℝ), (4195383293/10000000000 : ℝ), (4195382741/10000000000 : ℝ)] ![(35361801666937/100000000000000 : ℝ), (32319101920847/100000000000000 : ℝ), (40398870489/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2247970477/5000000000 : ℝ)|^4433 ≤ (35361801666937/100000000000000 : ℝ)^3409
        have hw : |(2247970477/5000000000 : ℝ)|=(2247970477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4195383293/10000000000 : ℝ)|^4433 ≤ (32319101920847/100000000000000 : ℝ)^3409
        have hw : |(4195383293/10000000000 : ℝ)|=(4195383293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4195382741/10000000000 : ℝ)|^4433 ≤ (40398870489/125000000000 : ℝ)^3409
        have hw : |(4195382741/10000000000 : ℝ)|=(4195382741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_4 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-270294977/1250000000 : ℝ)*x 0 + (5241907131/10000000000 : ℝ)*x 1 + (2620953787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270294977/1250000000 : ℝ)^4433 ≤ (3412657771499/25000000000000 : ℝ)^3409 := by
    have hnat : (270294977 : ℕ)^4433*25000000000000^3409 ≤ 3412657771499^3409*1250000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270294977 1250000000 3412657771499 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241907131/10000000000 : ℝ)^4433 ≤ (5396835259429/12500000000000 : ℝ)^3409 := by
    have hnat : (5241907131 : ℕ)^4433*12500000000000^3409 ≤ 5396835259429^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241907131 10000000000 5396835259429 12500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620953787/5000000000 : ℝ)^4433 ≤ (1349208963131/3125000000000 : ℝ)^3409 := by
    have hnat : (2620953787 : ℕ)^4433*3125000000000^3409 ≤ 1349208963131^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620953787 5000000000 1349208963131 3125000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270294977/1250000000 : ℝ), (5241907131/10000000000 : ℝ), (2620953787/5000000000 : ℝ)] ![(3412657771499/25000000000000 : ℝ), (5396835259429/12500000000000 : ℝ), (1349208963131/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270294977/1250000000 : ℝ)|^4433 ≤ (3412657771499/25000000000000 : ℝ)^3409
        have hw : |(-270294977/1250000000 : ℝ)|=(270294977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241907131/10000000000 : ℝ)|^4433 ≤ (5396835259429/12500000000000 : ℝ)^3409
        have hw : |(5241907131/10000000000 : ℝ)|=(5241907131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620953787/5000000000 : ℝ)|^4433 ≤ (1349208963131/3125000000000 : ℝ)^3409
        have hw : |(2620953787/5000000000 : ℝ)|=(2620953787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_5 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346429987/2500000000 : ℝ)*x 0 + (-39427393/200000000 : ℝ)*x 1 + (5241907257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346429987/2500000000 : ℝ)^4433 ≤ (4472129885149/10000000000000 : ℝ)^3409 := by
    have hnat : (1346429987 : ℕ)^4433*10000000000000^3409 ≤ 4472129885149^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346429987 2500000000 4472129885149 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39427393/200000000 : ℝ)^4433 ≤ (12104017707489/100000000000000 : ℝ)^3409 := by
    have hnat : (39427393 : ℕ)^4433*100000000000000^3409 ≤ 12104017707489^3409*200000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39427393 200000000 12104017707489 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241907257/10000000000 : ℝ)^4433 ≤ (43174683424957/100000000000000 : ℝ)^3409 := by
    have hnat : (5241907257 : ℕ)^4433*100000000000000^3409 ≤ 43174683424957^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241907257 10000000000 43174683424957 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346429987/2500000000 : ℝ), (-39427393/200000000 : ℝ), (5241907257/10000000000 : ℝ)] ![(4472129885149/10000000000000 : ℝ), (12104017707489/100000000000000 : ℝ), (43174683424957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346429987/2500000000 : ℝ)|^4433 ≤ (4472129885149/10000000000000 : ℝ)^3409
        have hw : |(1346429987/2500000000 : ℝ)|=(1346429987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39427393/200000000 : ℝ)|^4433 ≤ (12104017707489/100000000000000 : ℝ)^3409
        have hw : |(-39427393/200000000 : ℝ)|=(39427393/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241907257/10000000000 : ℝ)|^4433 ≤ (43174683424957/100000000000000 : ℝ)^3409
        have hw : |(5241907257/10000000000 : ℝ)|=(5241907257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_6 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692860053/5000000000 : ℝ)*x 0 + (5241907349/10000000000 : ℝ)*x 1 + (-1971369313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692860053/5000000000 : ℝ)^4433 ≤ (22360650278783/50000000000000 : ℝ)^3409 := by
    have hnat : (2692860053 : ℕ)^4433*50000000000000^3409 ≤ 22360650278783^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692860053 5000000000 22360650278783 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241907349/10000000000 : ℝ)^4433 ≤ (1726987376413/4000000000000 : ℝ)^3409 := by
    have hnat : (5241907349 : ℕ)^4433*4000000000000^3409 ≤ 1726987376413^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241907349 10000000000 1726987376413 4000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1971369313/10000000000 : ℝ)^4433 ≤ (1513001877101/12500000000000 : ℝ)^3409 := by
    have hnat : (1971369313 : ℕ)^4433*12500000000000^3409 ≤ 1513001877101^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971369313 10000000000 1513001877101 12500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692860053/5000000000 : ℝ), (5241907349/10000000000 : ℝ), (-1971369313/10000000000 : ℝ)] ![(22360650278783/50000000000000 : ℝ), (1726987376413/4000000000000 : ℝ), (1513001877101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692860053/5000000000 : ℝ)|^4433 ≤ (22360650278783/50000000000000 : ℝ)^3409
        have hw : |(2692860053/5000000000 : ℝ)|=(2692860053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241907349/10000000000 : ℝ)|^4433 ≤ (1726987376413/4000000000000 : ℝ)^3409
        have hw : |(5241907349/10000000000 : ℝ)|=(5241907349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1971369313/10000000000 : ℝ)|^4433 ≤ (1513001877101/12500000000000 : ℝ)^3409
        have hw : |(-1971369313/10000000000 : ℝ)|=(1971369313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_7 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (204164339/500000000 : ℝ)*x 0 + (1100392353/2500000000 : ℝ)*x 1 + (4401569923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204164339/500000000 : ℝ)^4433 ≤ (6240142455339/20000000000000 : ℝ)^3409 := by
    have hnat : (204164339 : ℕ)^4433*20000000000000^3409 ≤ 6240142455339^3409*500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204164339 500000000 6240142455339 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100392353/2500000000 : ℝ)^4433 ≤ (3439964126309/10000000000000 : ℝ)^3409 := by
    have hnat : (1100392353 : ℕ)^4433*10000000000000^3409 ≤ 3439964126309^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100392353 2500000000 3439964126309 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4401569923/10000000000 : ℝ)^4433 ≤ (17199823228163/50000000000000 : ℝ)^3409 := by
    have hnat : (4401569923 : ℕ)^4433*50000000000000^3409 ≤ 17199823228163^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401569923 10000000000 17199823228163 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(204164339/500000000 : ℝ), (1100392353/2500000000 : ℝ), (4401569923/10000000000 : ℝ)] ![(6240142455339/20000000000000 : ℝ), (3439964126309/10000000000000 : ℝ), (17199823228163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(204164339/500000000 : ℝ)|^4433 ≤ (6240142455339/20000000000000 : ℝ)^3409
        have hw : |(204164339/500000000 : ℝ)|=(204164339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100392353/2500000000 : ℝ)|^4433 ≤ (3439964126309/10000000000000 : ℝ)^3409
        have hw : |(1100392353/2500000000 : ℝ)|=(1100392353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4401569923/10000000000 : ℝ)|^4433 ≤ (17199823228163/50000000000000 : ℝ)^3409
        have hw : |(4401569923/10000000000 : ℝ)|=(4401569923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_8 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-516924861/2500000000 : ℝ)*x 0 + (2563164931/5000000000 : ℝ)*x 1 + (5428184683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516924861/2500000000 : ℝ)^4433 ≤ (3219679248661/25000000000000 : ℝ)^3409 := by
    have hnat : (516924861 : ℕ)^4433*25000000000000^3409 ≤ 3219679248661^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516924861 2500000000 3219679248661 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563164931/5000000000 : ℝ)^4433 ≤ (20970454998953/50000000000000 : ℝ)^3409 := by
    have hnat : (2563164931 : ℕ)^4433*50000000000000^3409 ≤ 20970454998953^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563164931 5000000000 20970454998953 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428184683/10000000000 : ℝ)^4433 ≤ (45180373001487/100000000000000 : ℝ)^3409 := by
    have hnat : (5428184683 : ℕ)^4433*100000000000000^3409 ≤ 45180373001487^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428184683 10000000000 45180373001487 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-516924861/2500000000 : ℝ), (2563164931/5000000000 : ℝ), (5428184683/10000000000 : ℝ)] ![(3219679248661/25000000000000 : ℝ), (20970454998953/50000000000000 : ℝ), (45180373001487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-516924861/2500000000 : ℝ)|^4433 ≤ (3219679248661/25000000000000 : ℝ)^3409
        have hw : |(-516924861/2500000000 : ℝ)|=(516924861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563164931/5000000000 : ℝ)|^4433 ≤ (20970454998953/50000000000000 : ℝ)^3409
        have hw : |(2563164931/5000000000 : ℝ)|=(2563164931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428184683/10000000000 : ℝ)|^4433 ≤ (45180373001487/100000000000000 : ℝ)^3409
        have hw : |(5428184683/10000000000 : ℝ)|=(5428184683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_9 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13138931/25000000 : ℝ)*x 0 + (-1895086643/10000000000 : ℝ)*x 1 + (5428184273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13138931/25000000 : ℝ)^4433 ≤ (2707568842713/6250000000000 : ℝ)^3409 := by
    have hnat : (13138931 : ℕ)^4433*6250000000000^3409 ≤ 2707568842713^3409*25000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13138931 25000000 2707568842713 6250000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895086643/10000000000 : ℝ)^4433 ≤ (11498529939191/100000000000000 : ℝ)^3409 := by
    have hnat : (1895086643 : ℕ)^4433*100000000000000^3409 ≤ 11498529939191^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895086643 10000000000 11498529939191 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428184273/10000000000 : ℝ)^4433 ≤ (45180368563871/100000000000000 : ℝ)^3409 := by
    have hnat : (5428184273 : ℕ)^4433*100000000000000^3409 ≤ 45180368563871^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428184273 10000000000 45180368563871 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13138931/25000000 : ℝ), (-1895086643/10000000000 : ℝ), (5428184273/10000000000 : ℝ)] ![(2707568842713/6250000000000 : ℝ), (11498529939191/100000000000000 : ℝ), (45180368563871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13138931/25000000 : ℝ)|^4433 ≤ (2707568842713/6250000000000 : ℝ)^3409
        have hw : |(13138931/25000000 : ℝ)|=(13138931/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895086643/10000000000 : ℝ)|^4433 ≤ (11498529939191/100000000000000 : ℝ)^3409
        have hw : |(-1895086643/10000000000 : ℝ)|=(1895086643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428184273/10000000000 : ℝ)|^4433 ≤ (45180368563871/100000000000000 : ℝ)^3409
        have hw : |(5428184273/10000000000 : ℝ)|=(5428184273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_10 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210222873/400000000 : ℝ)*x 0 + (5428184431/10000000000 : ℝ)*x 1 + (-1895087207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210222873/400000000 : ℝ)^4433 ≤ (43321095320041/100000000000000 : ℝ)^3409 := by
    have hnat : (210222873 : ℕ)^4433*100000000000000^3409 ≤ 43321095320041^3409*400000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210222873 400000000 43321095320041 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428184431/10000000000 : ℝ)^4433 ≤ (45180370273977/100000000000000 : ℝ)^3409 := by
    have hnat : (5428184431 : ℕ)^4433*100000000000000^3409 ≤ 45180370273977^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428184431 10000000000 45180370273977 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1895087207/10000000000 : ℝ)^4433 ≤ (11498534389223/100000000000000 : ℝ)^3409 := by
    have hnat : (1895087207 : ℕ)^4433*100000000000000^3409 ≤ 11498534389223^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895087207 10000000000 11498534389223 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210222873/400000000 : ℝ), (5428184431/10000000000 : ℝ), (-1895087207/10000000000 : ℝ)] ![(43321095320041/100000000000000 : ℝ), (45180370273977/100000000000000 : ℝ), (11498534389223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210222873/400000000 : ℝ)|^4433 ≤ (43321095320041/100000000000000 : ℝ)^3409
        have hw : |(210222873/400000000 : ℝ)|=(210222873/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428184431/10000000000 : ℝ)|^4433 ≤ (45180370273977/100000000000000 : ℝ)^3409
        have hw : |(5428184431/10000000000 : ℝ)|=(5428184431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1895087207/10000000000 : ℝ)|^4433 ≤ (11498534389223/100000000000000 : ℝ)^3409
        have hw : |(-1895087207/10000000000 : ℝ)|=(1895087207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_11 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4546032113/10000000000 : ℝ)*x 0 + (4169744811/10000000000 : ℝ)*x 1 + (833949123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4546032113/10000000000 : ℝ)^4433 ≤ (35874981797747/100000000000000 : ℝ)^3409 := by
    have hnat : (4546032113 : ℕ)^4433*100000000000000^3409 ≤ 35874981797747^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546032113 10000000000 35874981797747 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169744811/10000000000 : ℝ)^4433 ≤ (6412501014851/20000000000000 : ℝ)^3409 := by
    have hnat : (4169744811 : ℕ)^4433*20000000000000^3409 ≤ 6412501014851^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169744811 10000000000 6412501014851 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833949123/2000000000 : ℝ)^4433 ≤ (3206251311349/10000000000000 : ℝ)^3409 := by
    have hnat : (833949123 : ℕ)^4433*10000000000000^3409 ≤ 3206251311349^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833949123 2000000000 3206251311349 10000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4546032113/10000000000 : ℝ), (4169744811/10000000000 : ℝ), (833949123/2000000000 : ℝ)] ![(35874981797747/100000000000000 : ℝ), (6412501014851/20000000000000 : ℝ), (3206251311349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4546032113/10000000000 : ℝ)|^4433 ≤ (35874981797747/100000000000000 : ℝ)^3409
        have hw : |(4546032113/10000000000 : ℝ)|=(4546032113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169744811/10000000000 : ℝ)|^4433 ≤ (6412501014851/20000000000000 : ℝ)^3409
        have hw : |(4169744811/10000000000 : ℝ)|=(4169744811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833949123/2000000000 : ℝ)|^4433 ≤ (3206251311349/10000000000000 : ℝ)^3409
        have hw : |(833949123/2000000000 : ℝ)|=(833949123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_12 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1808047499/10000000000 : ℝ)*x 0 + (344956491/625000000 : ℝ)*x 1 + (2613465877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1808047499/10000000000 : ℝ)^4433 ≤ (2163313815077/20000000000000 : ℝ)^3409 := by
    have hnat : (1808047499 : ℕ)^4433*20000000000000^3409 ≤ 2163313815077^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808047499 10000000000 2163313815077 20000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344956491/625000000 : ℝ)^4433 ≤ (230845370233/500000000000 : ℝ)^3409 := by
    have hnat : (344956491 : ℕ)^4433*500000000000^3409 ≤ 230845370233^3409*625000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344956491 625000000 230845370233 500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613465877/5000000000 : ℝ)^4433 ≤ (10753589216877/25000000000000 : ℝ)^3409 := by
    have hnat : (2613465877 : ℕ)^4433*25000000000000^3409 ≤ 10753589216877^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613465877 5000000000 10753589216877 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1808047499/10000000000 : ℝ), (344956491/625000000 : ℝ), (2613465877/5000000000 : ℝ)] ![(2163313815077/20000000000000 : ℝ), (230845370233/500000000000 : ℝ), (10753589216877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1808047499/10000000000 : ℝ)|^4433 ≤ (2163313815077/20000000000000 : ℝ)^3409
        have hw : |(-1808047499/10000000000 : ℝ)|=(1808047499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344956491/625000000 : ℝ)|^4433 ≤ (230845370233/500000000000 : ℝ)^3409
        have hw : |(344956491/625000000 : ℝ)|=(344956491/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613465877/5000000000 : ℝ)|^4433 ≤ (10753589216877/25000000000000 : ℝ)^3409
        have hw : |(2613465877/5000000000 : ℝ)|=(2613465877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_13 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396180631/10000000000 : ℝ)*x 0 + (-1977296039/10000000000 : ℝ)*x 1 + (209077273/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396180631/10000000000 : ℝ)^4433 ≤ (5604285716807/12500000000000 : ℝ)^3409 := by
    have hnat : (5396180631 : ℕ)^4433*12500000000000^3409 ≤ 5604285716807^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396180631 10000000000 5604285716807 12500000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1977296039/10000000000 : ℝ)^4433 ≤ (48605426479/400000000000 : ℝ)^3409 := by
    have hnat : (1977296039 : ℕ)^4433*400000000000^3409 ≤ 48605426479^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977296039 10000000000 48605426479 400000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209077273/400000000 : ℝ)^4433 ≤ (21507178813651/50000000000000 : ℝ)^3409 := by
    have hnat : (209077273 : ℕ)^4433*50000000000000^3409 ≤ 21507178813651^3409*400000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209077273 400000000 21507178813651 50000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396180631/10000000000 : ℝ), (-1977296039/10000000000 : ℝ), (209077273/400000000 : ℝ)] ![(5604285716807/12500000000000 : ℝ), (48605426479/400000000000 : ℝ), (21507178813651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396180631/10000000000 : ℝ)|^4433 ≤ (5604285716807/12500000000000 : ℝ)^3409
        have hw : |(5396180631/10000000000 : ℝ)|=(5396180631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1977296039/10000000000 : ℝ)|^4433 ≤ (48605426479/400000000000 : ℝ)^3409
        have hw : |(-1977296039/10000000000 : ℝ)|=(1977296039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209077273/400000000 : ℝ)|^4433 ≤ (21507178813651/50000000000000 : ℝ)^3409
        have hw : |(209077273/400000000 : ℝ)|=(209077273/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_14 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396180519/10000000000 : ℝ)*x 0 + (1045386357/2000000000 : ℝ)*x 1 + (-494324061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396180519/10000000000 : ℝ)^4433 ≤ (2241714226219/5000000000000 : ℝ)^3409 := by
    have hnat : (5396180519 : ℕ)^4433*5000000000000^3409 ≤ 2241714226219^3409*10000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396180519 10000000000 2241714226219 5000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045386357/2000000000 : ℝ)^4433 ≤ (43014357199249/100000000000000 : ℝ)^3409 := by
    have hnat : (1045386357 : ℕ)^4433*100000000000000^3409 ≤ 43014357199249^3409*2000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045386357 2000000000 43014357199249 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494324061/2500000000 : ℝ)^4433 ≤ (12151358257991/100000000000000 : ℝ)^3409 := by
    have hnat : (494324061 : ℕ)^4433*100000000000000^3409 ≤ 12151358257991^3409*2500000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494324061 2500000000 12151358257991 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396180519/10000000000 : ℝ), (1045386357/2000000000 : ℝ), (-494324061/2500000000 : ℝ)] ![(2241714226219/5000000000000 : ℝ), (43014357199249/100000000000000 : ℝ), (12151358257991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396180519/10000000000 : ℝ)|^4433 ≤ (2241714226219/5000000000000 : ℝ)^3409
        have hw : |(5396180519/10000000000 : ℝ)|=(5396180519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045386357/2000000000 : ℝ)|^4433 ≤ (43014357199249/100000000000000 : ℝ)^3409
        have hw : |(1045386357/2000000000 : ℝ)|=(1045386357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-494324061/2500000000 : ℝ)|^4433 ≤ (12151358257991/100000000000000 : ℝ)^3409
        have hw : |(-494324061/2500000000 : ℝ)|=(494324061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1468_box_15 (p : ℝ) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2022566497/5000000000 : ℝ)*x 0 + (2210091501/5000000000 : ℝ)*x 1 + (442018343/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022566497/5000000000 : ℝ)^4433 ≤ (30822137427181/100000000000000 : ℝ)^3409 := by
    have hnat : (2022566497 : ℕ)^4433*100000000000000^3409 ≤ 30822137427181^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022566497 5000000000 30822137427181 100000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210091501/5000000000 : ℝ)^4433 ≤ (8647232275019/25000000000000 : ℝ)^3409 := by
    have hnat : (2210091501 : ℕ)^4433*25000000000000^3409 ≤ 8647232275019^3409*5000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210091501 5000000000 8647232275019 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442018343/1000000000 : ℝ)^4433 ≤ (8647233363827/25000000000000 : ℝ)^3409 := by
    have hnat : (442018343 : ℕ)^4433*25000000000000^3409 ≤ 8647233363827^3409*1000000000^4433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442018343 1000000000 8647233363827 25000000000000 4433 3409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4433/1024 : ℝ)) 4433 3409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2022566497/5000000000 : ℝ), (2210091501/5000000000 : ℝ), (442018343/1000000000 : ℝ)] ![(30822137427181/100000000000000 : ℝ), (8647232275019/25000000000000 : ℝ), (8647233363827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2022566497/5000000000 : ℝ)|^4433 ≤ (30822137427181/100000000000000 : ℝ)^3409
        have hw : |(2022566497/5000000000 : ℝ)|=(2022566497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210091501/5000000000 : ℝ)|^4433 ≤ (8647232275019/25000000000000 : ℝ)^3409
        have hw : |(2210091501/5000000000 : ℝ)|=(2210091501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442018343/1000000000 : ℝ)|^4433 ≤ (8647233363827/25000000000000 : ℝ)^3409
        have hw : |(442018343/1000000000 : ℝ)|=(442018343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1468_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5367/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63691/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29211/50000 : ℝ) ∧ (9979/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42857/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5367/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5367/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5367/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5367/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5367/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5367/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5367/50000 : ℝ) ^ (4431/1024 : ℝ) ≤ (6396781739981649/100000000000000000000 : ℝ) := by
    have hpowers : (5367/50000 : ℝ)^4431 ≤ (6396781739981649/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5367 : ℕ)^4431*100000000000000000000^1024 ≤ 6396781739981649^1024*50000^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5367 50000 6396781739981649 100000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5367/50000 : ℝ)) (X := (6396781739981649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (967/6250 : ℝ) ^ (4431/1024 : ℝ) ≤ (31120546621243343/100000000000000000000 : ℝ) := by
    have hpowers : (967/6250 : ℝ)^4431 ≤ (31120546621243343/100000000000000000000 : ℝ)^1024 := by
      have hnat : (967 : ℕ)^4431*100000000000000000000^1024 ≤ 31120546621243343^1024*6250^4431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        967 6250 31120546621243343 100000000000000000000 4431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (967/6250 : ℝ)) (X := (31120546621243343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006396781739981649/50000000000000000000 : ℝ) ≤ (2000059128705483/2000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (50006396781739981649/50000000000000000000 : ℝ)^1024 ≤ (2000059128705483/2000000000000000 : ℝ)^4431 := by
      have hnat : (50006396781739981649 : ℕ)^1024*2000000000000000^4431 ≤ 2000059128705483^4431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006396781739981649 50000000000000000000 2000059128705483 2000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000059128705483/2000000000000000 : ℝ)) (X := (50006396781739981649/50000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126172416511288281/3125000000000000000 : ℝ) ≤ (1250108362119903/1250000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (3126172416511288281/3125000000000000000 : ℝ)^1024 ≤ (1250108362119903/1250000000000000 : ℝ)^4431 := by
      have hnat : (3126172416511288281 : ℕ)^1024*1250000000000000^4431 ≤ 1250108362119903^4431*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126172416511288281 3125000000000000000 1250108362119903 1250000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250108362119903/1250000000000000 : ℝ)) (X := (3126172416511288281/3125000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031120546621243343/50000000000000000000 : ℝ) ≤ (10001438150391033/10000000000000000 : ℝ) ^ (4431/1024 : ℝ) := by
    have hpowers : (50031120546621243343/50000000000000000000 : ℝ)^1024 ≤ (10001438150391033/10000000000000000 : ℝ)^4431 := by
      have hnat : (50031120546621243343 : ℕ)^1024*10000000000000000^4431 ≤ 10001438150391033^4431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031120546621243343 50000000000000000000 10001438150391033 10000000000000000 1024 4431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001438150391033/10000000000000000 : ℝ)) (X := (50031120546621243343/50000000000000000000 : ℝ)) (by norm_num) 4431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6396781739981649/100000000000000000000 : ℝ) ≤ ((23684568545179408329/23690000000000000000 : ℝ)+2*(571253431809/473800000000000 : ℝ)*(5367/50000 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (23684568545179408329/23690000000000000000 : ℝ)+2*(571253431809/473800000000000 : ℝ)*(5367/50000 : ℝ)=(2000059128705483/2000000000000000 : ℝ) by norm_num, show 1+2*(6396781739981649/100000000000000000000 : ℝ)=(50006396781739981649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31120546621243343/100000000000000000000 : ℝ)+(6396781739981649/100000000000000000000 : ℝ) ≤ ((23684568545179408329/23690000000000000000 : ℝ)+(571253431809/473800000000000 : ℝ)*((967/6250 : ℝ)+(5367/50000 : ℝ)))^(4431/1024 : ℝ) := by
    rw [show (23684568545179408329/23690000000000000000 : ℝ)+(571253431809/473800000000000 : ℝ)*((967/6250 : ℝ)+(5367/50000 : ℝ))=(1250108362119903/1250000000000000 : ℝ) by norm_num, show 1+(31120546621243343/100000000000000000000 : ℝ)+(6396781739981649/100000000000000000000 : ℝ)=(3126172416511288281/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31120546621243343/100000000000000000000 : ℝ) ≤ ((23684568545179408329/23690000000000000000 : ℝ)+2*(571253431809/473800000000000 : ℝ)*(967/6250 : ℝ))^(4431/1024 : ℝ) := by
    rw [show (23684568545179408329/23690000000000000000 : ℝ)+2*(571253431809/473800000000000 : ℝ)*(967/6250 : ℝ)=(10001438150391033/10000000000000000 : ℝ) by norm_num, show 1+2*(31120546621243343/100000000000000000000 : ℝ)=(50031120546621243343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23684568545179408329/23690000000000000000 : ℝ)*(X 1 0+X 2 0)+(571253431809/473800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (5367/50000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (23684568545179408329/23690000000000000000 : ℝ)) (alpha := (571253431809/473800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23684568545179408329/23690000000000000000 : ℝ)*(X 0 1+X 2 1)+(571253431809/473800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (5367/50000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (23684568545179408329/23690000000000000000 : ℝ)) (alpha := (571253431809/473800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23684568545179408329/23690000000000000000 : ℝ)*(X 0 2+X 1 2)+(571253431809/473800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4431/1024 : ℝ)) (lo := (5367/50000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (23684568545179408329/23690000000000000000 : ℝ)) (alpha := (571253431809/473800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1713182431/10000000000 : ℝ)*X 0 0+(5407606249/10000000000 : ℝ)*X 0 1+(1351901627/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((105399141/200000000 : ℝ)*X 1 0+(-237967917/1250000000 : ℝ)*X 1 1+(1351901521/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2634978279/5000000000 : ℝ)*X 2 0+(2703803169/5000000000 : ℝ)*X 2 1+(-1903743657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2247970477/5000000000 : ℝ)*X 0 0+(4195383293/10000000000 : ℝ)*X 0 1+(4195382741/10000000000 : ℝ)*X 0 2+(2247970477/5000000000 : ℝ)*X 1 0+(4195383293/10000000000 : ℝ)*X 1 1+(4195382741/10000000000 : ℝ)*X 1 2+(2247970477/5000000000 : ℝ)*X 2 0+(4195383293/10000000000 : ℝ)*X 2 1+(4195382741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-270294977/1250000000 : ℝ)*X 0 0+(5241907131/10000000000 : ℝ)*X 0 1+(2620953787/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1346429987/2500000000 : ℝ)*X 1 0+(-39427393/200000000 : ℝ)*X 1 1+(5241907257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2692860053/5000000000 : ℝ)*X 2 0+(5241907349/10000000000 : ℝ)*X 2 1+(-1971369313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((204164339/500000000 : ℝ)*X 0 0+(1100392353/2500000000 : ℝ)*X 0 1+(4401569923/10000000000 : ℝ)*X 0 2+(204164339/500000000 : ℝ)*X 1 0+(1100392353/2500000000 : ℝ)*X 1 1+(4401569923/10000000000 : ℝ)*X 1 2+(204164339/500000000 : ℝ)*X 2 0+(1100392353/2500000000 : ℝ)*X 2 1+(4401569923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-516924861/2500000000 : ℝ)*X 0 0+(2563164931/5000000000 : ℝ)*X 0 1+(5428184683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((13138931/25000000 : ℝ)*X 1 0+(-1895086643/10000000000 : ℝ)*X 1 1+(5428184273/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((210222873/400000000 : ℝ)*X 2 0+(5428184431/10000000000 : ℝ)*X 2 1+(-1895087207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4546032113/10000000000 : ℝ)*X 0 0+(4169744811/10000000000 : ℝ)*X 0 1+(833949123/2000000000 : ℝ)*X 0 2+(4546032113/10000000000 : ℝ)*X 1 0+(4169744811/10000000000 : ℝ)*X 1 1+(833949123/2000000000 : ℝ)*X 1 2+(4546032113/10000000000 : ℝ)*X 2 0+(4169744811/10000000000 : ℝ)*X 2 1+(833949123/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1808047499/10000000000 : ℝ)*X 0 0+(344956491/625000000 : ℝ)*X 0 1+(2613465877/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5396180631/10000000000 : ℝ)*X 1 0+(-1977296039/10000000000 : ℝ)*X 1 1+(209077273/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5396180519/10000000000 : ℝ)*X 2 0+(1045386357/2000000000 : ℝ)*X 2 1+(-494324061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2022566497/5000000000 : ℝ)*X 0 0+(2210091501/5000000000 : ℝ)*X 0 1+(442018343/1000000000 : ℝ)*X 0 2+(2022566497/5000000000 : ℝ)*X 1 0+(2210091501/5000000000 : ℝ)*X 1 1+(442018343/1000000000 : ℝ)*X 1 2+(2022566497/5000000000 : ℝ)*X 2 0+(2210091501/5000000000 : ℝ)*X 2 1+(442018343/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1468_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63691/100000 : ℝ) ≤ (-23574548416724045090644712418699/37015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1076771/100000000000000 : ℝ)*(lower0) + (34441353/20000000000000 : ℝ)*(lower2) + (178534869/100000000000000 : ℝ)*(lower3) + (34714671/25000000000000 : ℝ)*(lower4) + (33712135938099/1562500000000 : ℝ)*(major0) + (33712135938099/1562500000000 : ℝ)*(major1) + (33712135938099/1562500000000 : ℝ)*(major2) + (74670661621613/2500000000000 : ℝ)*(sp4) + (746692617876881/25000000000000 : ℝ)*(sp5) + (2986783704507913/100000000000000 : ℝ)*(sp6) + (674756855532351/50000000000000 : ℝ)*(sp7) + (55993356997/100000000000000 : ℝ)*(sp13) + (42760356607/100000000000000 : ℝ)*(sp14) + (2129547509/5000000000000 : ℝ)*(sp15) + (674778151007441/50000000000000 : ℝ)*(f.failure) + (74670661621613/2500000000000 : ℝ)*(f.sum) + (591519891857/740312500000000000000000000 : ℝ)*base65 + (179010424887701571/37015625000000000000000000000000 : ℝ)*base67 + (216528258034454679/37015625000000000000000000000000 : ℝ)*base70 + (13394999929201269/2313476562500000000000000000000 : ℝ)*base72 + (39049528088567/11845000000000000000000000000 : ℝ)*base73 + (7260621811136913/4626953125000000000000000000000 : ℝ)*base76 + (2508914006296411/578369140625000000000000000000 : ℝ)*base78 + (93522320287264071/37015625000000000000000000000000 : ℝ)*base79 + (52707330505393/11845000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6298081/5000000000000000000000 : ℝ)*base89 + (6298081/5000000000000000000000 : ℝ)*base91 + (6298081/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29211/50000 : ℝ) ≤ (346018061219331160759857275728083/592250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2322537/4000000000000 : ℝ)*(lower0) + (12848571/12500000000000 : ℝ)*(upper1) + (8656419/5000000000000 : ℝ)*(upper2) + (1115419695751203/50000000000000 : ℝ)*(major0) + (1115419695751203/50000000000000 : ℝ)*(major1) + (1115419695751203/50000000000000 : ℝ)*(major2) + (761705295251639/25000000000000 : ℝ)*(sp0) + (609363589005203/20000000000000 : ℝ)*(sp1) + (761700449912023/25000000000000 : ℝ)*(sp2) + (27907634509629/2000000000000 : ℝ)*(sp3) + (60490793/50000000000000 : ℝ)*(sp7) + (1054179497/25000000000000 : ℝ)*(sp9) + (20362095911/100000000000000 : ℝ)*(sp10) + (980737447/100000000000000 : ℝ)*(sp12) + (348845461615759/25000000000000 : ℝ)*(f.failure) + (3046822161744003/100000000000000 : ℝ)*(f.sum) + (11497571774083/2961250000000000000000000000 : ℝ)*base65 + (10932348913509680213/1184500000000000000000000000000000 : ℝ)*base68 + (6055791381641680213/1184500000000000000000000000000000 : ℝ)*base70 + (10730269626843680213/1184500000000000000000000000000000 : ℝ)*base72 + (10405321723717/11845000000000000000000000000 : ℝ)*base73 + (6189189177022680213/1184500000000000000000000000000000 : ℝ)*base76 + (5788426606648180213/1184500000000000000000000000000000 : ℝ)*base78 + (10697231184464180213/1184500000000000000000000000000000 : ℝ)*base80 + (10019003018703/2961250000000000000000000000 : ℝ)*base81 + (14853119/2500000000000000000000 : ℝ)*base89 + (14853119/2500000000000000000000 : ℝ)*base91 + (14853119/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (9979/12500 : ℝ) ≤ (236410657810348036395017535511851/296125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64810773/100000000000000 : ℝ)*(upper0) + (226592739/100000000000000 : ℝ)*(upper2) + (34307421/100000000000000 : ℝ)*(lower3) + (142057113/100000000000000 : ℝ)*(lower5) + (1214788130510527/50000000000000 : ℝ)*(major0) + (1214788130510527/50000000000000 : ℝ)*(major1) + (1214788130510527/50000000000000 : ℝ)*(major2) + (25098885833/100000000000000 : ℝ)*(sp1) + (8623017771/25000000000000 : ℝ)*(sp3) + (8222609227/100000000000000 : ℝ)*(sp4) + (1656420843568063/50000000000000 : ℝ)*(sp8) + (647036095871/19531250000 : ℝ)*(sp9) + (1656424954872677/50000000000000 : ℝ)*(sp10) + (759828268200049/50000000000000 : ℝ)*(sp11) + (759845514235591/50000000000000 : ℝ)*(f.failure) + (1656424954872677/50000000000000 : ℝ)*(f.sum) + (67528016574387/11845000000000000000000000000 : ℝ)*base66 + (8306086066737629383/1184500000000000000000000000000000 : ℝ)*base67 + (12157734866718129383/1184500000000000000000000000000000 : ℝ)*base69 + (10962021217063129383/1184500000000000000000000000000000 : ℝ)*base71 + (100712964379853/11845000000000000000000000000 : ℝ)*base73 + (5186012375946129383/1184500000000000000000000000000000 : ℝ)*base75 + (237166858263129383/1184500000000000000000000000000000 : ℝ)*base77 + (14610306589274870617/1184500000000000000000000000000000 : ℝ)*base80 + (53933453832923/11845000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (23602231/5000000000000000000000 : ℝ)*base89 + (23602231/5000000000000000000000 : ℝ)*base91 + (23602231/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-42857/50000 : ℝ) ≤ (-253813843111133451088898628446019/296125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43693511/100000000000000 : ℝ)*(lower0) + (63647301/100000000000000 : ℝ)*(lower1) + (3185687/100000000000000 : ℝ)*(lower3) + (2696883/3125000000000 : ℝ)*(lower4) + (1233802033755463/50000000000000 : ℝ)*(major0) + (1233802033755463/50000000000000 : ℝ)*(major1) + (1233802033755463/50000000000000 : ℝ)*(major2) + (966315371/4000000000000 : ℝ)*(sp5) + (17509747813/25000000000000 : ℝ)*(sp6) + (3140313591/25000000000000 : ℝ)*(sp7) + (1710150713982337/50000000000000 : ℝ)*(sp12) + (8550693175201/250000000000 : ℝ)*(sp13) + (1710115694486711/50000000000000 : ℝ)*(sp14) + (1543464720516317/100000000000000 : ℝ)*(sp15) + (1543477281770681/100000000000000 : ℝ)*(f.failure) + (1710150713982337/50000000000000 : ℝ)*(f.sum) + (8946195874173/11845000000000000000000000000 : ℝ)*base66 + (3655297386397198673/1184500000000000000000000000000000 : ℝ)*base68 + (3182301198648801327/1184500000000000000000000000000000 : ℝ)*base69 + (13984588173931198673/1184500000000000000000000000000000 : ℝ)*base72 + (61440968777627/11845000000000000000000000000 : ℝ)*base73 + (20314098766226698673/1184500000000000000000000000000000 : ℝ)*base76 + (1457231636166198673/1184500000000000000000000000000000 : ℝ)*base78 + (27820947950198673/1184500000000000000000000000000000 : ℝ)*base80 + (24507253645543/11845000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (36110921/10000000000000000000000 : ℝ)*base89 + (36110921/10000000000000000000000 : ℝ)*base91 + (36110921/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1468_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5367/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63691/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29211/50000 : ℝ) else (9979/12500 : ℝ) ≤ X j i ∧ X j i ≤ (42857/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1468_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1468_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63691/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29211/50000 : ℝ) else (9979/12500 : ℝ) ≤ X j i ∧ X j i ≤ (42857/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1468_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1468_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4431/1024 : ℝ) ≤ p) (hpb : p ≤ (4433/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159873041/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63691/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29211/50000 : ℝ) else (9979/12500 : ℝ) ≤ X j i ∧ X j i ≤ (42857/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1468_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

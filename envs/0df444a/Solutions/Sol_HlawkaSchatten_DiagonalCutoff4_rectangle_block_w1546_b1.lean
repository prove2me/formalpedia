-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1546_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:19.324026+00:00
-- url     : https://prove2.me/submissions/939d4b36-6875-48e6-986b-38b5a9a165ac

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
theorem support_rectangle_w1546_s3_0 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-227325011/1250000000 : ℝ)*x 0 + (271552903/500000000 : ℝ)*x 1 + (2608592063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227325011/1250000000 : ℝ)^4589 ≤ (11145673696329/100000000000000 : ℝ)^3565 := by
    have hnat : (227325011 : ℕ)^4589*100000000000000^3565 ≤ 11145673696329^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227325011 1250000000 11145673696329 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271552903/500000000 : ℝ)^4589 ≤ (22787854947069/50000000000000 : ℝ)^3565 := by
    have hnat : (271552903 : ℕ)^4589*50000000000000^3565 ≤ 22787854947069^3565*500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271552903 500000000 22787854947069 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608592063/5000000000 : ℝ)^4589 ≤ (43278616407701/100000000000000 : ℝ)^3565 := by
    have hnat : (2608592063 : ℕ)^4589*100000000000000^3565 ≤ 43278616407701^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608592063 5000000000 43278616407701 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-227325011/1250000000 : ℝ), (271552903/500000000 : ℝ), (2608592063/5000000000 : ℝ)] ![(11145673696329/100000000000000 : ℝ), (22787854947069/50000000000000 : ℝ), (43278616407701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-227325011/1250000000 : ℝ)|^4589 ≤ (11145673696329/100000000000000 : ℝ)^3565
        have hw : |(-227325011/1250000000 : ℝ)|=(227325011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271552903/500000000 : ℝ)|^4589 ≤ (22787854947069/50000000000000 : ℝ)^3565
        have hw : |(271552903/500000000 : ℝ)|=(271552903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608592063/5000000000 : ℝ)|^4589 ≤ (43278616407701/100000000000000 : ℝ)^3565
        have hw : |(2608592063/5000000000 : ℝ)|=(2608592063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s3_1 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070044239/2000000000 : ℝ)*x 0 + (-1928113801/10000000000 : ℝ)*x 1 + (5217184173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070044239/2000000000 : ℝ)^4589 ≤ (894087531943/2000000000000 : ℝ)^3565 := by
    have hnat : (1070044239 : ℕ)^4589*2000000000000^3565 ≤ 894087531943^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070044239 2000000000 894087531943 2000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1928113801/10000000000 : ℝ)^4589 ≤ (1502125808613/12500000000000 : ℝ)^3565 := by
    have hnat : (1928113801 : ℕ)^4589*12500000000000^3565 ≤ 1502125808613^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928113801 10000000000 1502125808613 12500000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217184173/10000000000 : ℝ)^4589 ≤ (21639308454787/50000000000000 : ℝ)^3565 := by
    have hnat : (5217184173 : ℕ)^4589*50000000000000^3565 ≤ 21639308454787^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217184173 10000000000 21639308454787 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070044239/2000000000 : ℝ), (-1928113801/10000000000 : ℝ), (5217184173/10000000000 : ℝ)] ![(894087531943/2000000000000 : ℝ), (1502125808613/12500000000000 : ℝ), (21639308454787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070044239/2000000000 : ℝ)|^4589 ≤ (894087531943/2000000000000 : ℝ)^3565
        have hw : |(1070044239/2000000000 : ℝ)|=(1070044239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1928113801/10000000000 : ℝ)|^4589 ≤ (1502125808613/12500000000000 : ℝ)^3565
        have hw : |(-1928113801/10000000000 : ℝ)|=(1928113801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217184173/10000000000 : ℝ)|^4589 ≤ (21639308454787/50000000000000 : ℝ)^3565
        have hw : |(5217184173/10000000000 : ℝ)|=(5217184173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s3_2 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267511067/500000000 : ℝ)*x 0 + (1304296021/2500000000 : ℝ)*x 1 + (-77124549/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267511067/500000000 : ℝ)^4589 ≤ (558804726959/1250000000000 : ℝ)^3565 := by
    have hnat : (267511067 : ℕ)^4589*1250000000000^3565 ≤ 558804726959^3565*500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267511067 500000000 558804726959 1250000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304296021/2500000000 : ℝ)^4589 ≤ (43278615959219/100000000000000 : ℝ)^3565 := by
    have hnat : (1304296021 : ℕ)^4589*100000000000000^3565 ≤ 43278615959219^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304296021 2500000000 43278615959219 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77124549/400000000 : ℝ)^4589 ≤ (12017005859177/100000000000000 : ℝ)^3565 := by
    have hnat : (77124549 : ℕ)^4589*100000000000000^3565 ≤ 12017005859177^3565*400000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77124549 400000000 12017005859177 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267511067/500000000 : ℝ), (1304296021/2500000000 : ℝ), (-77124549/400000000 : ℝ)] ![(558804726959/1250000000000 : ℝ), (43278615959219/100000000000000 : ℝ), (12017005859177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267511067/500000000 : ℝ)|^4589 ≤ (558804726959/1250000000000 : ℝ)^3565
        have hw : |(267511067/500000000 : ℝ)|=(267511067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304296021/2500000000 : ℝ)|^4589 ≤ (43278615959219/100000000000000 : ℝ)^3565
        have hw : |(1304296021/2500000000 : ℝ)|=(1304296021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77124549/400000000 : ℝ)|^4589 ≤ (12017005859177/100000000000000 : ℝ)^3565
        have hw : |(-77124549/400000000 : ℝ)|=(77124549/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s3_3 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4253987801/10000000000 : ℝ)*x 0 + (62682211/156250000 : ℝ)*x 1 + (1127070101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253987801/10000000000 : ℝ)^4589 ≤ (33279192197661/100000000000000 : ℝ)^3565 := by
    have hnat : (4253987801 : ℕ)^4589*100000000000000^3565 ≤ 33279192197661^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253987801 10000000000 33279192197661 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62682211/156250000 : ℝ)^4589 ≤ (30859176109817/100000000000000 : ℝ)^3565 := by
    have hnat : (62682211 : ℕ)^4589*100000000000000^3565 ≤ 30859176109817^3565*156250000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62682211 156250000 30859176109817 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127070101/2500000000 : ℝ)^4589 ≤ (17930815838809/50000000000000 : ℝ)^3565 := by
    have hnat : (1127070101 : ℕ)^4589*50000000000000^3565 ≤ 17930815838809^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127070101 2500000000 17930815838809 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253987801/10000000000 : ℝ), (62682211/156250000 : ℝ), (1127070101/2500000000 : ℝ)] ![(33279192197661/100000000000000 : ℝ), (30859176109817/100000000000000 : ℝ), (17930815838809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253987801/10000000000 : ℝ)|^4589 ≤ (33279192197661/100000000000000 : ℝ)^3565
        have hw : |(4253987801/10000000000 : ℝ)|=(4253987801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62682211/156250000 : ℝ)|^4589 ≤ (30859176109817/100000000000000 : ℝ)^3565
        have hw : |(62682211/156250000 : ℝ)|=(62682211/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127070101/2500000000 : ℝ)|^4589 ≤ (17930815838809/50000000000000 : ℝ)^3565
        have hw : |(1127070101/2500000000 : ℝ)|=(1127070101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s3_4 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1818629167/10000000000 : ℝ)*x 0 + (2609157433/5000000000 : ℝ)*x 1 + (2714959493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1818629167/10000000000 : ℝ)^4589 ≤ (1114590310409/10000000000000 : ℝ)^3565 := by
    have hnat : (1818629167 : ℕ)^4589*10000000000000^3565 ≤ 1114590310409^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818629167 10000000000 1114590310409 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609157433/5000000000 : ℝ)^4589 ≤ (4329069098679/10000000000000 : ℝ)^3565 := by
    have hnat : (2609157433 : ℕ)^4589*10000000000000^3565 ≤ 4329069098679^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609157433 5000000000 4329069098679 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714959493/5000000000 : ℝ)^4589 ≤ (45563405892609/100000000000000 : ℝ)^3565 := by
    have hnat : (2714959493 : ℕ)^4589*100000000000000^3565 ≤ 45563405892609^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714959493 5000000000 45563405892609 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1818629167/10000000000 : ℝ), (2609157433/5000000000 : ℝ), (2714959493/5000000000 : ℝ)] ![(1114590310409/10000000000000 : ℝ), (4329069098679/10000000000000 : ℝ), (45563405892609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1818629167/10000000000 : ℝ)|^4589 ≤ (1114590310409/10000000000000 : ℝ)^3565
        have hw : |(-1818629167/10000000000 : ℝ)|=(1818629167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609157433/5000000000 : ℝ)|^4589 ≤ (4329069098679/10000000000000 : ℝ)^3565
        have hw : |(2609157433/5000000000 : ℝ)|=(2609157433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714959493/5000000000 : ℝ)|^4589 ≤ (45563405892609/100000000000000 : ℝ)^3565
        have hw : |(2714959493/5000000000 : ℝ)|=(2714959493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s3_5 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293805481/10000000000 : ℝ)*x 0 + (-107211191/625000000 : ℝ)*x 1 + (5429919181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293805481/10000000000 : ℝ)^4589 ≤ (8819701983393/20000000000000 : ℝ)^3565 := by
    have hnat : (5293805481 : ℕ)^4589*20000000000000^3565 ≤ 8819701983393^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293805481 10000000000 8819701983393 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107211191/625000000 : ℝ)^4589 ≤ (1033808207633/10000000000000 : ℝ)^3565 := by
    have hnat : (107211191 : ℕ)^4589*10000000000000^3565 ≤ 1033808207633^3565*625000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107211191 625000000 1033808207633 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429919181/10000000000 : ℝ)^4589 ≤ (45563407998889/100000000000000 : ℝ)^3565 := by
    have hnat : (5429919181 : ℕ)^4589*100000000000000^3565 ≤ 45563407998889^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429919181 10000000000 45563407998889 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293805481/10000000000 : ℝ), (-107211191/625000000 : ℝ), (5429919181/10000000000 : ℝ)] ![(8819701983393/20000000000000 : ℝ), (1033808207633/10000000000000 : ℝ), (45563407998889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293805481/10000000000 : ℝ)|^4589 ≤ (8819701983393/20000000000000 : ℝ)^3565
        have hw : |(5293805481/10000000000 : ℝ)|=(5293805481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107211191/625000000 : ℝ)|^4589 ≤ (1033808207633/10000000000000 : ℝ)^3565
        have hw : |(-107211191/625000000 : ℝ)|=(107211191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429919181/10000000000 : ℝ)|^4589 ≤ (45563407998889/100000000000000 : ℝ)^3565
        have hw : |(5429919181/10000000000 : ℝ)|=(5429919181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s3_6 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293806007/10000000000 : ℝ)*x 0 + (1085983781/2000000000 : ℝ)*x 1 + (-1715378711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293806007/10000000000 : ℝ)^4589 ≤ (44098515557239/100000000000000 : ℝ)^3565 := by
    have hnat : (5293806007 : ℕ)^4589*100000000000000^3565 ≤ 44098515557239^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293806007 10000000000 44098515557239 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085983781/2000000000 : ℝ)^4589 ≤ (45563405017693/100000000000000 : ℝ)^3565 := by
    have hnat : (1085983781 : ℕ)^4589*100000000000000^3565 ≤ 45563405017693^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085983781 2000000000 45563405017693 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1715378711/10000000000 : ℝ)^4589 ≤ (1033807939989/10000000000000 : ℝ)^3565 := by
    have hnat : (1715378711 : ℕ)^4589*10000000000000^3565 ≤ 1033807939989^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1715378711 10000000000 1033807939989 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293806007/10000000000 : ℝ), (1085983781/2000000000 : ℝ), (-1715378711/10000000000 : ℝ)] ![(44098515557239/100000000000000 : ℝ), (45563405017693/100000000000000 : ℝ), (1033807939989/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293806007/10000000000 : ℝ)|^4589 ≤ (44098515557239/100000000000000 : ℝ)^3565
        have hw : |(5293806007/10000000000 : ℝ)|=(5293806007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085983781/2000000000 : ℝ)|^4589 ≤ (45563405017693/100000000000000 : ℝ)^3565
        have hw : |(1085983781/2000000000 : ℝ)|=(1085983781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1715378711/10000000000 : ℝ)|^4589 ≤ (1033807939989/10000000000000 : ℝ)^3565
        have hw : |(-1715378711/10000000000 : ℝ)|=(1715378711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s3_7 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254055693/10000000000 : ℝ)*x 0 + (901131111/2000000000 : ℝ)*x 1 + (802861263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254055693/10000000000 : ℝ)^4589 ≤ (16639937940233/50000000000000 : ℝ)^3565 := by
    have hnat : (4254055693 : ℕ)^4589*50000000000000^3565 ≤ 16639937940233^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254055693 10000000000 16639937940233 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901131111/2000000000 : ℝ)^4589 ≤ (1791737842609/5000000000000 : ℝ)^3565 := by
    have hnat : (901131111 : ℕ)^4589*5000000000000^3565 ≤ 1791737842609^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901131111 2000000000 1791737842609 5000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (802861263/2000000000 : ℝ)^4589 ≤ (15442683622577/50000000000000 : ℝ)^3565 := by
    have hnat : (802861263 : ℕ)^4589*50000000000000^3565 ≤ 15442683622577^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802861263 2000000000 15442683622577 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254055693/10000000000 : ℝ), (901131111/2000000000 : ℝ), (802861263/2000000000 : ℝ)] ![(16639937940233/50000000000000 : ℝ), (1791737842609/5000000000000 : ℝ), (15442683622577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254055693/10000000000 : ℝ)|^4589 ≤ (16639937940233/50000000000000 : ℝ)^3565
        have hw : |(4254055693/10000000000 : ℝ)|=(4254055693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901131111/2000000000 : ℝ)|^4589 ≤ (1791737842609/5000000000000 : ℝ)^3565
        have hw : |(901131111/2000000000 : ℝ)|=(901131111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(802861263/2000000000 : ℝ)|^4589 ≤ (15442683622577/50000000000000 : ℝ)^3565
        have hw : |(802861263/2000000000 : ℝ)|=(802861263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1546_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (397/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5499/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15531/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (397/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10677/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (397/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10677/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (397/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10677/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (397/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10677/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (397/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10677/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (397/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10677/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10677/100000 : ℝ) ^ (4587/1024 : ℝ) ≤ (2222879790079187/50000000000000000000 : ℝ) := by
    have hpowers : (10677/100000 : ℝ)^4587 ≤ (2222879790079187/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10677 : ℕ)^4587*50000000000000000000^1024 ≤ 2222879790079187^1024*100000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10677 100000 2222879790079187 50000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10677/100000 : ℝ)) (X := (2222879790079187/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (397/2500 : ℝ) ^ (4587/1024 : ℝ) ≤ (26315768033673287/100000000000000000000 : ℝ) := by
    have hpowers : (397/2500 : ℝ)^4587 ≤ (26315768033673287/100000000000000000000 : ℝ)^1024 := by
      have hnat : (397 : ℕ)^4587*100000000000000000000^1024 ≤ 26315768033673287^1024*2500^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        397 2500 26315768033673287 100000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (397/2500 : ℝ)) (X := (26315768033673287/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002222879790079187/25000000000000000000 : ℝ) ≤ (39063275340059/39062500000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (25002222879790079187/25000000000000000000 : ℝ)^1024 ≤ (39063275340059/39062500000000 : ℝ)^4587 := by
      have hnat : (25002222879790079187 : ℕ)^1024*39062500000000^4587 ≤ 39063275340059^4587*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002222879790079187 25000000000000000000 39063275340059 39062500000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39063275340059/39062500000000 : ℝ)) (X := (25002222879790079187/25000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030761527613831661/100000000000000000000 : ℝ) ≤ (10000686637053137/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (100030761527613831661/100000000000000000000 : ℝ)^1024 ≤ (10000686637053137/10000000000000000 : ℝ)^4587 := by
      have hnat : (100030761527613831661 : ℕ)^1024*10000000000000000^4587 ≤ 10000686637053137^4587*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030761527613831661 100000000000000000000 10000686637053137 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000686637053137/10000000000000000 : ℝ)) (X := (100030761527613831661/100000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026315768033673287/50000000000000000000 : ℝ) ≤ (1000117478705117/1000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (50026315768033673287/50000000000000000000 : ℝ)^1024 ≤ (1000117478705117/1000000000000000 : ℝ)^4587 := by
      have hnat : (50026315768033673287 : ℕ)^1024*1000000000000000^4587 ≤ 1000117478705117^4587*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026315768033673287 50000000000000000000 1000117478705117 1000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000117478705117/1000000000000000 : ℝ)) (X := (50026315768033673287/50000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2222879790079187/50000000000000000000 : ℝ) ≤ ((5202060877308970943/5203000000000000000 : ℝ)+2*(488149998033/520300000000000 : ℝ)*(10677/100000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (5202060877308970943/5203000000000000000 : ℝ)+2*(488149998033/520300000000000 : ℝ)*(10677/100000 : ℝ)=(39063275340059/39062500000000 : ℝ) by norm_num, show 1+2*(2222879790079187/50000000000000000000 : ℝ)=(25002222879790079187/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26315768033673287/100000000000000000000 : ℝ)+(2222879790079187/50000000000000000000 : ℝ) ≤ ((5202060877308970943/5203000000000000000 : ℝ)+(488149998033/520300000000000 : ℝ)*((397/2500 : ℝ)+(10677/100000 : ℝ)))^(4587/1024 : ℝ) := by
    rw [show (5202060877308970943/5203000000000000000 : ℝ)+(488149998033/520300000000000 : ℝ)*((397/2500 : ℝ)+(10677/100000 : ℝ))=(10000686637053137/10000000000000000 : ℝ) by norm_num, show 1+(26315768033673287/100000000000000000000 : ℝ)+(2222879790079187/50000000000000000000 : ℝ)=(100030761527613831661/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26315768033673287/100000000000000000000 : ℝ) ≤ ((5202060877308970943/5203000000000000000 : ℝ)+2*(488149998033/520300000000000 : ℝ)*(397/2500 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (5202060877308970943/5203000000000000000 : ℝ)+2*(488149998033/520300000000000 : ℝ)*(397/2500 : ℝ)=(1000117478705117/1000000000000000 : ℝ) by norm_num, show 1+2*(26315768033673287/100000000000000000000 : ℝ)=(50026315768033673287/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5202060877308970943/5203000000000000000 : ℝ)*(X 1 0+X 2 0)+(488149998033/520300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (10677/100000 : ℝ)) (hi := (397/2500 : ℝ)) (c := (5202060877308970943/5203000000000000000 : ℝ)) (alpha := (488149998033/520300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5202060877308970943/5203000000000000000 : ℝ)*(X 0 1+X 2 1)+(488149998033/520300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (10677/100000 : ℝ)) (hi := (397/2500 : ℝ)) (c := (5202060877308970943/5203000000000000000 : ℝ)) (alpha := (488149998033/520300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5202060877308970943/5203000000000000000 : ℝ)*(X 0 2+X 1 2)+(488149998033/520300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (10677/100000 : ℝ)) (hi := (397/2500 : ℝ)) (c := (5202060877308970943/5203000000000000000 : ℝ)) (alpha := (488149998033/520300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-227325011/1250000000 : ℝ)*X 0 0+(271552903/500000000 : ℝ)*X 0 1+(2608592063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070044239/2000000000 : ℝ)*X 1 0+(-1928113801/10000000000 : ℝ)*X 1 1+(5217184173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267511067/500000000 : ℝ)*X 2 0+(1304296021/2500000000 : ℝ)*X 2 1+(-77124549/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4253987801/10000000000 : ℝ)*X 0 0+(62682211/156250000 : ℝ)*X 0 1+(1127070101/2500000000 : ℝ)*X 0 2+(4253987801/10000000000 : ℝ)*X 1 0+(62682211/156250000 : ℝ)*X 1 1+(1127070101/2500000000 : ℝ)*X 1 2+(4253987801/10000000000 : ℝ)*X 2 0+(62682211/156250000 : ℝ)*X 2 1+(1127070101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1818629167/10000000000 : ℝ)*X 0 0+(2609157433/5000000000 : ℝ)*X 0 1+(2714959493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293805481/10000000000 : ℝ)*X 1 0+(-107211191/625000000 : ℝ)*X 1 1+(5429919181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293806007/10000000000 : ℝ)*X 2 0+(1085983781/2000000000 : ℝ)*X 2 1+(-1715378711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4254055693/10000000000 : ℝ)*X 0 0+(901131111/2000000000 : ℝ)*X 0 1+(802861263/2000000000 : ℝ)*X 0 2+(4254055693/10000000000 : ℝ)*X 1 0+(901131111/2000000000 : ℝ)*X 1 1+(802861263/2000000000 : ℝ)*X 1 2+(4254055693/10000000000 : ℝ)*X 2 0+(901131111/2000000000 : ℝ)*X 2 1+(802861263/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1493102941236011614997691/189200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1267786321/100000000000000 : ℝ)*(base19) + (330592301/25000000000000 : ℝ)*(base23) + (19297247/50000000000000 : ℝ)*(lower2) + (146188987/100000000000000 : ℝ)*(upper3) + (93703457/50000000000000 : ℝ)*(upper5) + (1672332269696813/50000000000000 : ℝ)*(major0) + (1672332269696813/50000000000000 : ℝ)*(major1) + (3344664539393627/100000000000000 : ℝ)*(major2) + (4675671363359811/100000000000000 : ℝ)*(sp0) + (73057699370787/1562500000000 : ℝ)*(sp1) + (935138541029497/20000000000000 : ℝ)*(sp2) + (2013625534940477/100000000000000 : ℝ)*(sp3) + (11332078439/50000000000000 : ℝ)*(sp4) + (9253274593/100000000000000 : ℝ)*(sp7) + (201363478821507/10000000000000 : ℝ)*(f.failure) + (4675694027516689/100000000000000 : ℝ)*(f.sum) + (183386135341611/52030000000000000000000000000 : ℝ)*base66 + (2620013541724490341/260150000000000000000000000000000 : ℝ)*base68 + (671718335499860261/520300000000000000000000000000000 : ℝ)*base69 + (1240097881862740341/260150000000000000000000000000000 : ℝ)*base72 + (38492872869301/52030000000000000000000000000 : ℝ)*base74 + (5787922009168860261/520300000000000000000000000000000 : ℝ)*base75 + (2474499805273905341/260150000000000000000000000000000 : ℝ)*base78 + (5634849180094455341/260150000000000000000000000000000 : ℝ)*base80 + (478661388617/406484375000000000000000000 : ℝ)*base81 + (2155991/250000000000000000000 : ℝ)*base89 + (2155991/250000000000000000000 : ℝ)*base91 + (344009/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (574152003953960056175881827/65037500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (625650613/100000000000000 : ℝ)*(base19) + (1493443263/100000000000000 : ℝ)*(base23) + (36198149/20000000000000 : ℝ)*(upper3) + (119492019/100000000000000 : ℝ)*(lower4) + (3424487/10000000000000 : ℝ)*(upper5) + (845127194109679/25000000000000 : ℝ)*(major0) + (845127194109679/25000000000000 : ℝ)*(major1) + (845127194109679/25000000000000 : ℝ)*(major2) + (2316142001/25000000000000 : ℝ)*(sp1) + (12726159877/50000000000000 : ℝ)*(sp2) + (4725802667153073/100000000000000 : ℝ)*(sp4) + (590724097116807/12500000000000 : ℝ)*(sp5) + (590721965173757/12500000000000 : ℝ)*(sp6) + (254401823932149/12500000000000 : ℝ)*(sp7) + (254401823932149/12500000000000 : ℝ)*(f.failure) + (4725802667153073/100000000000000 : ℝ)*(f.sum) + (128891655847653/26015000000000000000000000000 : ℝ)*base65 + (1103263362181777297/130075000000000000000000000000000 : ℝ)*base67 + (411000741780777297/130075000000000000000000000000000 : ℝ)*base69 + (1427071105407227297/130075000000000000000000000000000 : ℝ)*base71 + (3543734115833/1625937500000000000000000000 : ℝ)*base73 + (2035083729987027297/130075000000000000000000000000000 : ℝ)*base75 + (1930849156329527297/130075000000000000000000000000000 : ℝ)*base77 + (1276585594381927297/130075000000000000000000000000000 : ℝ)*base79 + (5148617504291/13007500000000000000000000000 : ℝ)*base82 + (2727263/312500000000000000000 : ℝ)*base90 + (2727263/312500000000000000000 : ℝ)*base92 + (2727263/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1546_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (397/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15531/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1546_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1546_s4_0 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1818897577/10000000000 : ℝ)*x 0 + (5429083931/10000000000 : ℝ)*x 1 + (5218961183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1818897577/10000000000 : ℝ)^4589 ≤ (5574010336451/50000000000000 : ℝ)^3565 := by
    have hnat : (1818897577 : ℕ)^4589*50000000000000^3565 ≤ 5574010336451^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818897577 10000000000 5574010336451 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429083931/10000000000 : ℝ)^4589 ≤ (22777193150831/50000000000000 : ℝ)^3565 := by
    have hnat : (5429083931 : ℕ)^4589*50000000000000^3565 ≤ 22777193150831^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429083931 10000000000 22777193150831 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218961183/10000000000 : ℝ)^4589 ≤ (8659518600887/20000000000000 : ℝ)^3565 := by
    have hnat : (5218961183 : ℕ)^4589*20000000000000^3565 ≤ 8659518600887^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218961183 10000000000 8659518600887 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1818897577/10000000000 : ℝ), (5429083931/10000000000 : ℝ), (5218961183/10000000000 : ℝ)] ![(5574010336451/50000000000000 : ℝ), (22777193150831/50000000000000 : ℝ), (8659518600887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1818897577/10000000000 : ℝ)|^4589 ≤ (5574010336451/50000000000000 : ℝ)^3565
        have hw : |(-1818897577/10000000000 : ℝ)|=(1818897577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429083931/10000000000 : ℝ)|^4589 ≤ (22777193150831/50000000000000 : ℝ)^3565
        have hw : |(5429083931/10000000000 : ℝ)|=(5429083931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218961183/10000000000 : ℝ)|^4589 ≤ (8659518600887/20000000000000 : ℝ)^3565
        have hw : |(5218961183/10000000000 : ℝ)|=(5218961183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s4_1 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674850461/5000000000 : ℝ)*x 0 + (-192644581/1000000000 : ℝ)*x 1 + (5218961173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674850461/5000000000 : ℝ)^4589 ≤ (44698780798851/100000000000000 : ℝ)^3565 := by
    have hnat : (2674850461 : ℕ)^4589*100000000000000^3565 ≤ 44698780798851^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674850461 5000000000 44698780798851 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192644581/1000000000 : ℝ)^4589 ≤ (2400725258213/20000000000000 : ℝ)^3565 := by
    have hnat : (192644581 : ℕ)^4589*20000000000000^3565 ≤ 2400725258213^3565*1000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192644581 1000000000 2400725258213 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218961173/10000000000 : ℝ)^4589 ≤ (43297592897643/100000000000000 : ℝ)^3565 := by
    have hnat : (5218961173 : ℕ)^4589*100000000000000^3565 ≤ 43297592897643^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218961173 10000000000 43297592897643 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674850461/5000000000 : ℝ), (-192644581/1000000000 : ℝ), (5218961173/10000000000 : ℝ)] ![(44698780798851/100000000000000 : ℝ), (2400725258213/20000000000000 : ℝ), (43297592897643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674850461/5000000000 : ℝ)|^4589 ≤ (44698780798851/100000000000000 : ℝ)^3565
        have hw : |(2674850461/5000000000 : ℝ)|=(2674850461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192644581/1000000000 : ℝ)|^4589 ≤ (2400725258213/20000000000000 : ℝ)^3565
        have hw : |(-192644581/1000000000 : ℝ)|=(192644581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218961173/10000000000 : ℝ)|^4589 ≤ (43297592897643/100000000000000 : ℝ)^3565
        have hw : |(5218961173/10000000000 : ℝ)|=(5218961173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s4_2 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069940169/2000000000 : ℝ)*x 0 + (5218961073/10000000000 : ℝ)*x 1 + (-963223023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069940169/2000000000 : ℝ)^4589 ≤ (44698779970689/100000000000000 : ℝ)^3565 := by
    have hnat : (1069940169 : ℕ)^4589*100000000000000^3565 ≤ 44698779970689^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069940169 2000000000 44698779970689 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218961073/10000000000 : ℝ)^4589 ≤ (1731903673189/4000000000000 : ℝ)^3565 := by
    have hnat : (5218961073 : ℕ)^4589*4000000000000^3565 ≤ 1731903673189^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218961073 10000000000 1731903673189 4000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963223023/5000000000 : ℝ)^4589 ≤ (6001814091979/50000000000000 : ℝ)^3565 := by
    have hnat : (963223023 : ℕ)^4589*50000000000000^3565 ≤ 6001814091979^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963223023 5000000000 6001814091979 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069940169/2000000000 : ℝ), (5218961073/10000000000 : ℝ), (-963223023/5000000000 : ℝ)] ![(44698779970689/100000000000000 : ℝ), (1731903673189/4000000000000 : ℝ), (6001814091979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069940169/2000000000 : ℝ)|^4589 ≤ (44698779970689/100000000000000 : ℝ)^3565
        have hw : |(1069940169/2000000000 : ℝ)|=(1069940169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218961073/10000000000 : ℝ)|^4589 ≤ (1731903673189/4000000000000 : ℝ)^3565
        have hw : |(5218961073/10000000000 : ℝ)|=(5218961073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-963223023/5000000000 : ℝ)|^4589 ≤ (6001814091979/50000000000000 : ℝ)^3565
        have hw : |(-963223023/5000000000 : ℝ)|=(963223023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s4_3 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1063543643/2500000000 : ℝ)*x 0 + (4015995507/10000000000 : ℝ)*x 1 + (225195217/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063543643/2500000000 : ℝ)^4589 ≤ (33281073017693/100000000000000 : ℝ)^3565 := by
    have hnat : (1063543643 : ℕ)^4589*100000000000000^3565 ≤ 33281073017693^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063543643 2500000000 33281073017693 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4015995507/10000000000 : ℝ)^4589 ≤ (30902097634317/100000000000000 : ℝ)^3565 := by
    have hnat : (4015995507 : ℕ)^4589*100000000000000^3565 ≤ 30902097634317^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015995507 10000000000 30902097634317 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225195217/500000000 : ℝ)^4589 ≤ (17908414665987/50000000000000 : ℝ)^3565 := by
    have hnat : (225195217 : ℕ)^4589*50000000000000^3565 ≤ 17908414665987^3565*500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225195217 500000000 17908414665987 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063543643/2500000000 : ℝ), (4015995507/10000000000 : ℝ), (225195217/500000000 : ℝ)] ![(33281073017693/100000000000000 : ℝ), (30902097634317/100000000000000 : ℝ), (17908414665987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063543643/2500000000 : ℝ)|^4589 ≤ (33281073017693/100000000000000 : ℝ)^3565
        have hw : |(1063543643/2500000000 : ℝ)|=(1063543643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4015995507/10000000000 : ℝ)|^4589 ≤ (30902097634317/100000000000000 : ℝ)^3565
        have hw : |(4015995507/10000000000 : ℝ)|=(4015995507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225195217/500000000 : ℝ)|^4589 ≤ (17908414665987/50000000000000 : ℝ)^3565
        have hw : |(225195217/500000000 : ℝ)|=(225195217/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s4_4 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1818925137/10000000000 : ℝ)*x 0 + (5220052549/10000000000 : ℝ)*x 1 + (217119387/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1818925137/10000000000 : ℝ)^4589 ≤ (2787059526819/25000000000000 : ℝ)^3565 := by
    have hnat : (1818925137 : ℕ)^4589*25000000000000^3565 ≤ 2787059526819^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818925137 10000000000 2787059526819 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220052549/10000000000 : ℝ)^4589 ≤ (21654624128281/50000000000000 : ℝ)^3565 := by
    have hnat : (5220052549 : ℕ)^4589*50000000000000^3565 ≤ 21654624128281^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220052549 10000000000 21654624128281 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217119387/400000000 : ℝ)^4589 ≤ (22771256816017/50000000000000 : ℝ)^3565 := by
    have hnat : (217119387 : ℕ)^4589*50000000000000^3565 ≤ 22771256816017^3565*400000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217119387 400000000 22771256816017 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1818925137/10000000000 : ℝ), (5220052549/10000000000 : ℝ), (217119387/400000000 : ℝ)] ![(2787059526819/25000000000000 : ℝ), (21654624128281/50000000000000 : ℝ), (22771256816017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1818925137/10000000000 : ℝ)|^4589 ≤ (2787059526819/25000000000000 : ℝ)^3565
        have hw : |(-1818925137/10000000000 : ℝ)|=(1818925137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220052549/10000000000 : ℝ)|^4589 ≤ (21654624128281/50000000000000 : ℝ)^3565
        have hw : |(5220052549/10000000000 : ℝ)|=(5220052549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217119387/400000000 : ℝ)|^4589 ≤ (22771256816017/50000000000000 : ℝ)^3565
        have hw : |(217119387/400000000 : ℝ)|=(217119387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s4_5 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647137557/5000000000 : ℝ)*x 0 + (-1717422801/10000000000 : ℝ)*x 1 + (5427984747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647137557/5000000000 : ℝ)^4589 ≤ (4410354583437/10000000000000 : ℝ)^3565 := by
    have hnat : (2647137557 : ℕ)^4589*10000000000000^3565 ≤ 4410354583437^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647137557 5000000000 4410354583437 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1717422801/10000000000 : ℝ)^4589 ≤ (2070787949359/20000000000000 : ℝ)^3565 := by
    have hnat : (1717422801 : ℕ)^4589*20000000000000^3565 ≤ 2070787949359^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717422801 10000000000 2070787949359 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427984747/10000000000 : ℝ)^4589 ≤ (22771257204829/50000000000000 : ℝ)^3565 := by
    have hnat : (5427984747 : ℕ)^4589*50000000000000^3565 ≤ 22771257204829^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427984747 10000000000 22771257204829 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647137557/5000000000 : ℝ), (-1717422801/10000000000 : ℝ), (5427984747/10000000000 : ℝ)] ![(4410354583437/10000000000000 : ℝ), (2070787949359/20000000000000 : ℝ), (22771257204829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647137557/5000000000 : ℝ)|^4589 ≤ (4410354583437/10000000000000 : ℝ)^3565
        have hw : |(2647137557/5000000000 : ℝ)|=(2647137557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1717422801/10000000000 : ℝ)|^4589 ≤ (2070787949359/20000000000000 : ℝ)^3565
        have hw : |(-1717422801/10000000000 : ℝ)|=(1717422801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427984747/10000000000 : ℝ)|^4589 ≤ (22771257204829/50000000000000 : ℝ)^3565
        have hw : |(5427984747/10000000000 : ℝ)|=(5427984747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s4_6 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294275003/10000000000 : ℝ)*x 0 + (2713992389/5000000000 : ℝ)*x 1 + (-1717422911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294275003/10000000000 : ℝ)^4589 ≤ (11025886161023/25000000000000 : ℝ)^3565 := by
    have hnat : (5294275003 : ℕ)^4589*25000000000000^3565 ≤ 11025886161023^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294275003 10000000000 11025886161023 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713992389/5000000000 : ℝ)^4589 ≤ (11385628686117/25000000000000 : ℝ)^3565 := by
    have hnat : (2713992389 : ℕ)^4589*25000000000000^3565 ≤ 11385628686117^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713992389 5000000000 11385628686117 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1717422911/10000000000 : ℝ)^4589 ≤ (2588485150111/25000000000000 : ℝ)^3565 := by
    have hnat : (1717422911 : ℕ)^4589*25000000000000^3565 ≤ 2588485150111^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717422911 10000000000 2588485150111 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294275003/10000000000 : ℝ), (2713992389/5000000000 : ℝ), (-1717422911/10000000000 : ℝ)] ![(11025886161023/25000000000000 : ℝ), (11385628686117/25000000000000 : ℝ), (2588485150111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294275003/10000000000 : ℝ)|^4589 ≤ (11025886161023/25000000000000 : ℝ)^3565
        have hw : |(5294275003/10000000000 : ℝ)|=(5294275003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713992389/5000000000 : ℝ)|^4589 ≤ (11385628686117/25000000000000 : ℝ)^3565
        have hw : |(2713992389/5000000000 : ℝ)|=(2713992389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1717422911/10000000000 : ℝ)|^4589 ≤ (2588485150111/25000000000000 : ℝ)^3565
        have hw : |(-1717422911/10000000000 : ℝ)|=(1717422911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s4_7 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254239201/10000000000 : ℝ)*x 0 + (1125342491/2500000000 : ℝ)*x 1 + (1004637147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254239201/10000000000 : ℝ)^4589 ≤ (16640861924863/50000000000000 : ℝ)^3565 := by
    have hnat : (4254239201 : ℕ)^4589*50000000000000^3565 ≤ 16640861924863^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254239201 10000000000 16640861924863 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125342491/2500000000 : ℝ)^4589 ≤ (17895443994763/50000000000000 : ℝ)^3565 := by
    have hnat : (1125342491 : ℕ)^4589*50000000000000^3565 ≤ 17895443994763^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125342491 2500000000 17895443994763 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004637147/2500000000 : ℝ)^4589 ≤ (15463694069719/50000000000000 : ℝ)^3565 := by
    have hnat : (1004637147 : ℕ)^4589*50000000000000^3565 ≤ 15463694069719^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004637147 2500000000 15463694069719 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254239201/10000000000 : ℝ), (1125342491/2500000000 : ℝ), (1004637147/2500000000 : ℝ)] ![(16640861924863/50000000000000 : ℝ), (17895443994763/50000000000000 : ℝ), (15463694069719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254239201/10000000000 : ℝ)|^4589 ≤ (16640861924863/50000000000000 : ℝ)^3565
        have hw : |(4254239201/10000000000 : ℝ)|=(4254239201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125342491/2500000000 : ℝ)|^4589 ≤ (17895443994763/50000000000000 : ℝ)^3565
        have hw : |(1125342491/2500000000 : ℝ)|=(1125342491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004637147/2500000000 : ℝ)|^4589 ≤ (15463694069719/50000000000000 : ℝ)^3565
        have hw : |(1004637147/2500000000 : ℝ)|=(1004637147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1546_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15531/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2759/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15531/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5499/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15531/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5499/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15531/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5499/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15531/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5499/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15531/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5499/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15531/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5499/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5499/50000 : ℝ) ^ (4587/1024 : ℝ) ≤ (1015318438764543/20000000000000000000 : ℝ) := by
    have hpowers : (5499/50000 : ℝ)^4587 ≤ (1015318438764543/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5499 : ℕ)^4587*20000000000000000000^1024 ≤ 1015318438764543^1024*50000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5499 50000 1015318438764543 20000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5499/50000 : ℝ)) (X := (1015318438764543/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15531/100000 : ℝ) ^ (4587/1024 : ℝ) ≤ (23822323575190541/100000000000000000000 : ℝ) := by
    have hpowers : (15531/100000 : ℝ)^4587 ≤ (23822323575190541/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15531 : ℕ)^4587*100000000000000000000^1024 ≤ 23822323575190541^1024*100000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15531 100000 23822323575190541 100000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15531/100000 : ℝ)) (X := (23822323575190541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001015318438764543/10000000000000000000 : ℝ) ≤ (1000022665033483/1000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (10001015318438764543/10000000000000000000 : ℝ)^1024 ≤ (1000022665033483/1000000000000000 : ℝ)^4587 := by
      have hnat : (10001015318438764543 : ℕ)^1024*1000000000000000^4587 ≤ 1000022665033483^4587*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001015318438764543 10000000000000000000 1000022665033483 1000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000022665033483/1000000000000000 : ℝ)) (X := (10001015318438764543/10000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503612364471126657/12500000000000000000 : ℝ) ≤ (10000645065814777/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (12503612364471126657/12500000000000000000 : ℝ)^1024 ≤ (10000645065814777/10000000000000000 : ℝ)^4587 := by
      have hnat : (12503612364471126657 : ℕ)^1024*10000000000000000^4587 ≤ 10000645065814777^4587*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503612364471126657 12500000000000000000 10000645065814777 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000645065814777/10000000000000000 : ℝ)) (X := (12503612364471126657/12500000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023822323575190541/50000000000000000000 : ℝ) ≤ (2500265870323681/2500000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (50023822323575190541/50000000000000000000 : ℝ)^1024 ≤ (2500265870323681/2500000000000000 : ℝ)^4587 := by
      have hnat : (50023822323575190541 : ℕ)^1024*2500000000000000^4587 ≤ 2500265870323681^4587*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023822323575190541 50000000000000000000 2500265870323681 2500000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500265870323681/2500000000000000 : ℝ)) (X := (50023822323575190541/50000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1015318438764543/20000000000000000000 : ℝ) ≤ ((7553637323178478363/7555000000000000000 : ℝ)+2*(139471826649/151100000000000 : ℝ)*(5499/50000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (7553637323178478363/7555000000000000000 : ℝ)+2*(139471826649/151100000000000 : ℝ)*(5499/50000 : ℝ)=(1000022665033483/1000000000000000 : ℝ) by norm_num, show 1+2*(1015318438764543/20000000000000000000 : ℝ)=(10001015318438764543/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23822323575190541/100000000000000000000 : ℝ)+(1015318438764543/20000000000000000000 : ℝ) ≤ ((7553637323178478363/7555000000000000000 : ℝ)+(139471826649/151100000000000 : ℝ)*((15531/100000 : ℝ)+(5499/50000 : ℝ)))^(4587/1024 : ℝ) := by
    rw [show (7553637323178478363/7555000000000000000 : ℝ)+(139471826649/151100000000000 : ℝ)*((15531/100000 : ℝ)+(5499/50000 : ℝ))=(10000645065814777/10000000000000000 : ℝ) by norm_num, show 1+(23822323575190541/100000000000000000000 : ℝ)+(1015318438764543/20000000000000000000 : ℝ)=(12503612364471126657/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23822323575190541/100000000000000000000 : ℝ) ≤ ((7553637323178478363/7555000000000000000 : ℝ)+2*(139471826649/151100000000000 : ℝ)*(15531/100000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (7553637323178478363/7555000000000000000 : ℝ)+2*(139471826649/151100000000000 : ℝ)*(15531/100000 : ℝ)=(2500265870323681/2500000000000000 : ℝ) by norm_num, show 1+2*(23822323575190541/100000000000000000000 : ℝ)=(50023822323575190541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7553637323178478363/7555000000000000000 : ℝ)*(X 1 0+X 2 0)+(139471826649/151100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (5499/50000 : ℝ)) (hi := (15531/100000 : ℝ)) (c := (7553637323178478363/7555000000000000000 : ℝ)) (alpha := (139471826649/151100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7553637323178478363/7555000000000000000 : ℝ)*(X 0 1+X 2 1)+(139471826649/151100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (5499/50000 : ℝ)) (hi := (15531/100000 : ℝ)) (c := (7553637323178478363/7555000000000000000 : ℝ)) (alpha := (139471826649/151100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7553637323178478363/7555000000000000000 : ℝ)*(X 0 2+X 1 2)+(139471826649/151100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (5499/50000 : ℝ)) (hi := (15531/100000 : ℝ)) (c := (7553637323178478363/7555000000000000000 : ℝ)) (alpha := (139471826649/151100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1818897577/10000000000 : ℝ)*X 0 0+(5429083931/10000000000 : ℝ)*X 0 1+(5218961183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674850461/5000000000 : ℝ)*X 1 0+(-192644581/1000000000 : ℝ)*X 1 1+(5218961173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069940169/2000000000 : ℝ)*X 2 0+(5218961073/10000000000 : ℝ)*X 2 1+(-963223023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1063543643/2500000000 : ℝ)*X 0 0+(4015995507/10000000000 : ℝ)*X 0 1+(225195217/500000000 : ℝ)*X 0 2+(1063543643/2500000000 : ℝ)*X 1 0+(4015995507/10000000000 : ℝ)*X 1 1+(225195217/500000000 : ℝ)*X 1 2+(1063543643/2500000000 : ℝ)*X 2 0+(4015995507/10000000000 : ℝ)*X 2 1+(225195217/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1818925137/10000000000 : ℝ)*X 0 0+(5220052549/10000000000 : ℝ)*X 0 1+(217119387/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647137557/5000000000 : ℝ)*X 1 0+(-1717422801/10000000000 : ℝ)*X 1 1+(5427984747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294275003/10000000000 : ℝ)*X 2 0+(2713992389/5000000000 : ℝ)*X 2 1+(-1717422911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4254239201/10000000000 : ℝ)*X 0 0+(1125342491/2500000000 : ℝ)*X 0 1+(1004637147/2500000000 : ℝ)*X 0 2+(4254239201/10000000000 : ℝ)*X 1 0+(1125342491/2500000000 : ℝ)*X 1 1+(1004637147/2500000000 : ℝ)*X 1 2+(4254239201/10000000000 : ℝ)*X 2 0+(1125342491/2500000000 : ℝ)*X 2 1+(1004637147/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71038543783238479008181401/9443750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1767584007/100000000000000 : ℝ)*(base19) + (1689362533/100000000000000 : ℝ)*(base23) + (76006731/25000000000000 : ℝ)*(upper3) + (2600231/50000000000000 : ℝ)*(upper4) + (53559057/100000000000000 : ℝ)*(upper5) + (85109647992091/2500000000000 : ℝ)*(major0) + (85109647992091/2500000000000 : ℝ)*(major1) + (85109647992091/2500000000000 : ℝ)*(major2) + (237957812593831/5000000000000 : ℝ)*(sp0) + (190367205672939/4000000000000 : ℝ)*(sp1) + (4759180220044949/100000000000000 : ℝ)*(sp2) + (512393778386133/25000000000000 : ℝ)*(sp3) + (25657530863/100000000000000 : ℝ)*(sp4) + (291313451/2000000000000 : ℝ)*(sp7) + (1024794839608541/50000000000000 : ℝ)*(f.failure) + (2379590954703741/50000000000000 : ℝ)*(f.sum) + (6130054521259/1511000000000000000000000000 : ℝ)*base65 + (167463931732314533/18887500000000000000000000000000 : ℝ)*base67 + (88529222388610467/18887500000000000000000000000000 : ℝ)*base70 + (44219256906027033/18887500000000000000000000000000 : ℝ)*base71 + (1453095262779/755500000000000000000000000 : ℝ)*base73 + (202915136852235467/18887500000000000000000000000000 : ℝ)*base76 + (145559421280964533/18887500000000000000000000000000 : ℝ)*base77 + (272188371295189533/18887500000000000000000000000000 : ℝ)*base79 + (1925063326293/755500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1644233/1250000000000000000000 : ℝ)*base89 + (1644233/1250000000000000000000 : ℝ)*base91 + (1644233/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (283115677909622534085791217/23609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1176921459/100000000000000 : ℝ)*(base19) + (339017909/25000000000000 : ℝ)*(base23) + (805887/500000000000 : ℝ)*(upper3) + (76347541/50000000000000 : ℝ)*(lower4) + (269581511/100000000000000 : ℝ)*(upper5) + (215013086880839/6250000000000 : ℝ)*(major0) + (215013086880839/6250000000000 : ℝ)*(major1) + (215013086880839/6250000000000 : ℝ)*(major2) + (19688667683/100000000000000 : ℝ)*(sp1) + (755321093/4000000000000 : ℝ)*(sp2) + (4809261400431043/100000000000000 : ℝ)*(sp4) + (4809240534841901/100000000000000 : ℝ)*(sp5) + (2404620580666041/50000000000000 : ℝ)*(sp6) + (2071156980033687/100000000000000 : ℝ)*(sp7) + (2071156980033687/100000000000000 : ℝ)*(f.failure) + (4809261400431043/100000000000000 : ℝ)*(f.sum) + (8276418473849/1888750000000000000000000000 : ℝ)*base65 + (66645588501319693/47218750000000000000000000000000 : ℝ)*base68 + (595174222694007193/47218750000000000000000000000000 : ℝ)*base70 + (99537796555805307/47218750000000000000000000000000 : ℝ)*base71 + (37060730440141/7555000000000000000000000000 : ℝ)*base73 + (432887637178100943/47218750000000000000000000000000 : ℝ)*base76 + (162038988795475943/47218750000000000000000000000000 : ℝ)*base78 + (404660486909257193/47218750000000000000000000000000 : ℝ)*base80 + (1064241966909/472187500000000000000000000 : ℝ)*base82 + (149669/2500000000000000000000 : ℝ)*base90 + (149669/2500000000000000000000 : ℝ)*base92 + (149669/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1546_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15531/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5499/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1546_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1546_s5_0 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1818929643/10000000000 : ℝ)*x 0 + (5428868313/10000000000 : ℝ)*x 1 + (326197223/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1818929643/10000000000 : ℝ)^4589 ≤ (11148273657413/100000000000000 : ℝ)^3565 := by
    have hnat : (1818929643 : ℕ)^4589*100000000000000^3565 ≤ 11148273657413^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818929643 10000000000 11148273657413 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428868313/10000000000 : ℝ)^4589 ≤ (45552057434569/100000000000000 : ℝ)^3565 := by
    have hnat : (5428868313 : ℕ)^4589*100000000000000^3565 ≤ 45552057434569^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428868313 10000000000 45552057434569 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326197223/625000000 : ℝ)^4589 ≤ (10824917222349/25000000000000 : ℝ)^3565 := by
    have hnat : (326197223 : ℕ)^4589*25000000000000^3565 ≤ 10824917222349^3565*625000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326197223 625000000 10824917222349 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1818929643/10000000000 : ℝ), (5428868313/10000000000 : ℝ), (326197223/625000000 : ℝ)] ![(11148273657413/100000000000000 : ℝ), (45552057434569/100000000000000 : ℝ), (10824917222349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1818929643/10000000000 : ℝ)|^4589 ≤ (11148273657413/100000000000000 : ℝ)^3565
        have hw : |(-1818929643/10000000000 : ℝ)|=(1818929643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428868313/10000000000 : ℝ)|^4589 ≤ (45552057434569/100000000000000 : ℝ)^3565
        have hw : |(5428868313/10000000000 : ℝ)|=(5428868313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326197223/625000000 : ℝ)|^4589 ≤ (10824917222349/25000000000000 : ℝ)^3565
        have hw : |(326197223/625000000 : ℝ)|=(326197223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s5_1 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26748219/50000000 : ℝ)*x 0 + (-1926263399/10000000000 : ℝ)*x 1 + (5219155701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26748219/50000000 : ℝ)^4589 ≤ (22349083216239/50000000000000 : ℝ)^3565 := by
    have hnat : (26748219 : ℕ)^4589*50000000000000^3565 ≤ 22349083216239^3565*50000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26748219 50000000 22349083216239 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1926263399/10000000000 : ℝ)^4589 ≤ (6001081620293/50000000000000 : ℝ)^3565 := by
    have hnat : (1926263399 : ℕ)^4589*50000000000000^3565 ≤ 6001081620293^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926263399 10000000000 6001081620293 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219155701/10000000000 : ℝ)^4589 ≤ (43299670309743/100000000000000 : ℝ)^3565 := by
    have hnat : (5219155701 : ℕ)^4589*100000000000000^3565 ≤ 43299670309743^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219155701 10000000000 43299670309743 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26748219/50000000 : ℝ), (-1926263399/10000000000 : ℝ), (5219155701/10000000000 : ℝ)] ![(22349083216239/50000000000000 : ℝ), (6001081620293/50000000000000 : ℝ), (43299670309743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26748219/50000000 : ℝ)|^4589 ≤ (22349083216239/50000000000000 : ℝ)^3565
        have hw : |(26748219/50000000 : ℝ)|=(26748219/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1926263399/10000000000 : ℝ)|^4589 ≤ (6001081620293/50000000000000 : ℝ)^3565
        have hw : |(-1926263399/10000000000 : ℝ)|=(1926263399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219155701/10000000000 : ℝ)|^4589 ≤ (43299670309743/100000000000000 : ℝ)^3565
        have hw : |(5219155701/10000000000 : ℝ)|=(5219155701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s5_2 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133741097/250000000 : ℝ)*x 0 + (1304788903/2500000000 : ℝ)*x 1 + (-1926263411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133741097/250000000 : ℝ)^4589 ≤ (5587270911613/12500000000000 : ℝ)^3565 := by
    have hnat : (133741097 : ℕ)^4589*12500000000000^3565 ≤ 5587270911613^3565*250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133741097 250000000 5587270911613 12500000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304788903/2500000000 : ℝ)^4589 ≤ (8659933871857/20000000000000 : ℝ)^3565 := by
    have hnat : (1304788903 : ℕ)^4589*20000000000000^3565 ≤ 8659933871857^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304788903 2500000000 8659933871857 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926263411/10000000000 : ℝ)^4589 ≤ (93766901069/781250000000 : ℝ)^3565 := by
    have hnat : (1926263411 : ℕ)^4589*781250000000^3565 ≤ 93766901069^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926263411 10000000000 93766901069 781250000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133741097/250000000 : ℝ), (1304788903/2500000000 : ℝ), (-1926263411/10000000000 : ℝ)] ![(5587270911613/12500000000000 : ℝ), (8659933871857/20000000000000 : ℝ), (93766901069/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133741097/250000000 : ℝ)|^4589 ≤ (5587270911613/12500000000000 : ℝ)^3565
        have hw : |(133741097/250000000 : ℝ)|=(133741097/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304788903/2500000000 : ℝ)|^4589 ≤ (8659933871857/20000000000000 : ℝ)^3565
        have hw : |(1304788903/2500000000 : ℝ)|=(1304788903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1926263411/10000000000 : ℝ)|^4589 ≤ (93766901069/781250000000 : ℝ)^3565
        have hw : |(-1926263411/10000000000 : ℝ)|=(1926263411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s5_3 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531774353/1250000000 : ℝ)*x 0 + (2008234821/5000000000 : ℝ)*x 1 + (1125856407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531774353/1250000000 : ℝ)^4589 ≤ (33281276960669/100000000000000 : ℝ)^3565 := by
    have hnat : (531774353 : ℕ)^4589*100000000000000^3565 ≤ 33281276960669^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531774353 1250000000 33281276960669 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008234821/5000000000 : ℝ)^4589 ≤ (7726698501997/25000000000000 : ℝ)^3565 := by
    have hnat : (2008234821 : ℕ)^4589*25000000000000^3565 ≤ 7726698501997^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008234821 5000000000 7726698501997 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125856407/2500000000 : ℝ)^4589 ≤ (7162385802967/20000000000000 : ℝ)^3565 := by
    have hnat : (1125856407 : ℕ)^4589*20000000000000^3565 ≤ 7162385802967^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125856407 2500000000 7162385802967 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531774353/1250000000 : ℝ), (2008234821/5000000000 : ℝ), (1125856407/2500000000 : ℝ)] ![(33281276960669/100000000000000 : ℝ), (7726698501997/25000000000000 : ℝ), (7162385802967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531774353/1250000000 : ℝ)|^4589 ≤ (33281276960669/100000000000000 : ℝ)^3565
        have hw : |(531774353/1250000000 : ℝ)|=(531774353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008234821/5000000000 : ℝ)|^4589 ≤ (7726698501997/25000000000000 : ℝ)^3565
        have hw : |(2008234821/5000000000 : ℝ)|=(2008234821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125856407/2500000000 : ℝ)|^4589 ≤ (7162385802967/20000000000000 : ℝ)^3565
        have hw : |(1125856407/2500000000 : ℝ)|=(1125856407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s5_4 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-72758293/400000000 : ℝ)*x 0 + (5220242793/10000000000 : ℝ)*x 1 + (5427773037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72758293/400000000 : ℝ)^4589 ≤ (11148492055413/100000000000000 : ℝ)^3565 := by
    have hnat : (72758293 : ℕ)^4589*100000000000000^3565 ≤ 11148492055413^3565*400000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72758293 400000000 11148492055413 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220242793/10000000000 : ℝ)^4589 ≤ (21655640020281/50000000000000 : ℝ)^3565 := by
    have hnat : (5220242793 : ℕ)^4589*50000000000000^3565 ≤ 21655640020281^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220242793 10000000000 21655640020281 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427773037/10000000000 : ℝ)^4589 ≤ (45540227885213/100000000000000 : ℝ)^3565 := by
    have hnat : (5427773037 : ℕ)^4589*100000000000000^3565 ≤ 45540227885213^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427773037 10000000000 45540227885213 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72758293/400000000 : ℝ), (5220242793/10000000000 : ℝ), (5427773037/10000000000 : ℝ)] ![(11148492055413/100000000000000 : ℝ), (21655640020281/50000000000000 : ℝ), (45540227885213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72758293/400000000 : ℝ)|^4589 ≤ (11148492055413/100000000000000 : ℝ)^3565
        have hw : |(-72758293/400000000 : ℝ)|=(72758293/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220242793/10000000000 : ℝ)|^4589 ≤ (21655640020281/50000000000000 : ℝ)^3565
        have hw : |(5220242793/10000000000 : ℝ)|=(5220242793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427773037/10000000000 : ℝ)|^4589 ≤ (45540227885213/100000000000000 : ℝ)^3565
        have hw : |(5427773037/10000000000 : ℝ)|=(5427773037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s5_5 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165447711/312500000 : ℝ)*x 0 + (-429411521/2500000000 : ℝ)*x 1 + (1085554607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165447711/312500000 : ℝ)^4589 ≤ (22052049780587/50000000000000 : ℝ)^3565 := by
    have hnat : (165447711 : ℕ)^4589*50000000000000^3565 ≤ 22052049780587^3565*312500000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165447711 312500000 22052049780587 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429411521/2500000000 : ℝ)^4589 ≤ (5177836277907/50000000000000 : ℝ)^3565 := by
    have hnat : (429411521 : ℕ)^4589*50000000000000^3565 ≤ 5177836277907^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429411521 2500000000 5177836277907 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085554607/2000000000 : ℝ)^4589 ≤ (45540227863613/100000000000000 : ℝ)^3565 := by
    have hnat : (1085554607 : ℕ)^4589*100000000000000^3565 ≤ 45540227863613^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085554607 2000000000 45540227863613 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165447711/312500000 : ℝ), (-429411521/2500000000 : ℝ), (1085554607/2000000000 : ℝ)] ![(22052049780587/50000000000000 : ℝ), (5177836277907/50000000000000 : ℝ), (45540227863613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165447711/312500000 : ℝ)|^4589 ≤ (22052049780587/50000000000000 : ℝ)^3565
        have hw : |(165447711/312500000 : ℝ)|=(165447711/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429411521/2500000000 : ℝ)|^4589 ≤ (5177836277907/50000000000000 : ℝ)^3565
        have hw : |(-429411521/2500000000 : ℝ)|=(429411521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085554607/2000000000 : ℝ)|^4589 ≤ (45540227863613/100000000000000 : ℝ)^3565
        have hw : |(1085554607/2000000000 : ℝ)|=(1085554607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s5_6 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294326749/10000000000 : ℝ)*x 0 + (2713886519/5000000000 : ℝ)*x 1 + (-429411521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294326749/10000000000 : ℝ)^4589 ≤ (11026024882251/25000000000000 : ℝ)^3565 := by
    have hnat : (5294326749 : ℕ)^4589*25000000000000^3565 ≤ 11026024882251^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294326749 10000000000 11026024882251 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713886519/5000000000 : ℝ)^4589 ≤ (45540227896013/100000000000000 : ℝ)^3565 := by
    have hnat : (2713886519 : ℕ)^4589*100000000000000^3565 ≤ 45540227896013^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713886519 5000000000 45540227896013 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429411521/2500000000 : ℝ)^4589 ≤ (5177836277907/50000000000000 : ℝ)^3565 := by
    have hnat : (429411521 : ℕ)^4589*50000000000000^3565 ≤ 5177836277907^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429411521 2500000000 5177836277907 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294326749/10000000000 : ℝ), (2713886519/5000000000 : ℝ), (-429411521/2500000000 : ℝ)] ![(11026024882251/25000000000000 : ℝ), (45540227896013/100000000000000 : ℝ), (5177836277907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294326749/10000000000 : ℝ)|^4589 ≤ (11026024882251/25000000000000 : ℝ)^3565
        have hw : |(5294326749/10000000000 : ℝ)|=(5294326749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713886519/5000000000 : ℝ)|^4589 ≤ (45540227896013/100000000000000 : ℝ)^3565
        have hw : |(2713886519/5000000000 : ℝ)|=(2713886519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429411521/2500000000 : ℝ)|^4589 ≤ (5177836277907/50000000000000 : ℝ)^3565
        have hw : |(-429411521/2500000000 : ℝ)|=(429411521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s5_7 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127129507/5000000000 : ℝ)*x 0 + (140653167/312500000 : ℝ)*x 1 + (4019012577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127129507/5000000000 : ℝ)^4589 ≤ (33281923372723/100000000000000 : ℝ)^3565 := by
    have hnat : (2127129507 : ℕ)^4589*100000000000000^3565 ≤ 33281923372723^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127129507 5000000000 33281923372723 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140653167/312500000 : ℝ)^4589 ≤ (35786091752753/100000000000000 : ℝ)^3565 := by
    have hnat : (140653167 : ℕ)^4589*100000000000000^3565 ≤ 35786091752753^3565*312500000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140653167 312500000 35786091752753 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4019012577/10000000000 : ℝ)^4589 ≤ (15465992426439/50000000000000 : ℝ)^3565 := by
    have hnat : (4019012577 : ℕ)^4589*50000000000000^3565 ≤ 15465992426439^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019012577 10000000000 15465992426439 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127129507/5000000000 : ℝ), (140653167/312500000 : ℝ), (4019012577/10000000000 : ℝ)] ![(33281923372723/100000000000000 : ℝ), (35786091752753/100000000000000 : ℝ), (15465992426439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127129507/5000000000 : ℝ)|^4589 ≤ (33281923372723/100000000000000 : ℝ)^3565
        have hw : |(2127129507/5000000000 : ℝ)|=(2127129507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140653167/312500000 : ℝ)|^4589 ≤ (35786091752753/100000000000000 : ℝ)^3565
        have hw : |(140653167/312500000 : ℝ)|=(140653167/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4019012577/10000000000 : ℝ)|^4589 ≤ (15465992426439/50000000000000 : ℝ)^3565
        have hw : |(4019012577/10000000000 : ℝ)|=(4019012577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1546_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (69/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2759/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2759/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2759/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2759/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2759/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2759/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2759/25000 : ℝ) ^ (4587/1024 : ℝ) ≤ (5155638420908153/100000000000000000000 : ℝ) := by
    have hpowers : (2759/25000 : ℝ)^4587 ≤ (5155638420908153/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2759 : ℕ)^4587*100000000000000000000^1024 ≤ 5155638420908153^1024*25000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2759 25000 5155638420908153 100000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2759/25000 : ℝ)) (X := (5155638420908153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4587/1024 : ℝ) ≤ (23541907750414267/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4587 ≤ (23541907750414267/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4587*100000000000000000000^1024 ≤ 23541907750414267^1024*10000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 23541907750414267 100000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (23541907750414267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005155638420908153/50000000000000000000 : ℝ) ≤ (5000115089651909/5000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (50005155638420908153/50000000000000000000 : ℝ)^1024 ≤ (5000115089651909/5000000000000000 : ℝ)^4587 := by
      have hnat : (50005155638420908153 : ℕ)^1024*5000000000000000^4587 ≤ 5000115089651909^4587*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005155638420908153 50000000000000000000 5000115089651909 5000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000115089651909/5000000000000000 : ℝ)) (X := (50005155638420908153/50000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001434877308566121/5000000000000000000 : ℝ) ≤ (10000640571453457/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (5001434877308566121/5000000000000000000 : ℝ)^1024 ≤ (10000640571453457/10000000000000000 : ℝ)^4587 := by
      have hnat : (5001434877308566121 : ℕ)^1024*10000000000000000^4587 ≤ 10000640571453457^4587*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001434877308566121 5000000000000000000 10000640571453457 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000640571453457/10000000000000000 : ℝ)) (X := (5001434877308566121/5000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023541907750414267/50000000000000000000 : ℝ) ≤ (1250131370450387/1250000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (50023541907750414267/50000000000000000000 : ℝ)^1024 ≤ (1250131370450387/1250000000000000 : ℝ)^4587 := by
      have hnat : (50023541907750414267 : ℕ)^1024*1250000000000000^4587 ≤ 1250131370450387^4587*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023541907750414267 50000000000000000000 1250131370450387 1250000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250131370450387/1250000000000000 : ℝ)) (X := (50023541907750414267/50000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5155638420908153/100000000000000000000 : ℝ) ≤ ((11132991760773093341/11135000000000000000 : ℝ)+2*(410392149639/445400000000000 : ℝ)*(2759/25000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (11132991760773093341/11135000000000000000 : ℝ)+2*(410392149639/445400000000000 : ℝ)*(2759/25000 : ℝ)=(5000115089651909/5000000000000000 : ℝ) by norm_num, show 1+2*(5155638420908153/100000000000000000000 : ℝ)=(50005155638420908153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23541907750414267/100000000000000000000 : ℝ)+(5155638420908153/100000000000000000000 : ℝ) ≤ ((11132991760773093341/11135000000000000000 : ℝ)+(410392149639/445400000000000 : ℝ)*((1549/10000 : ℝ)+(2759/25000 : ℝ)))^(4587/1024 : ℝ) := by
    rw [show (11132991760773093341/11135000000000000000 : ℝ)+(410392149639/445400000000000 : ℝ)*((1549/10000 : ℝ)+(2759/25000 : ℝ))=(10000640571453457/10000000000000000 : ℝ) by norm_num, show 1+(23541907750414267/100000000000000000000 : ℝ)+(5155638420908153/100000000000000000000 : ℝ)=(5001434877308566121/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23541907750414267/100000000000000000000 : ℝ) ≤ ((11132991760773093341/11135000000000000000 : ℝ)+2*(410392149639/445400000000000 : ℝ)*(1549/10000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (11132991760773093341/11135000000000000000 : ℝ)+2*(410392149639/445400000000000 : ℝ)*(1549/10000 : ℝ)=(1250131370450387/1250000000000000 : ℝ) by norm_num, show 1+2*(23541907750414267/100000000000000000000 : ℝ)=(50023541907750414267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11132991760773093341/11135000000000000000 : ℝ)*(X 1 0+X 2 0)+(410392149639/445400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11132991760773093341/11135000000000000000 : ℝ)) (alpha := (410392149639/445400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11132991760773093341/11135000000000000000 : ℝ)*(X 0 1+X 2 1)+(410392149639/445400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11132991760773093341/11135000000000000000 : ℝ)) (alpha := (410392149639/445400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11132991760773093341/11135000000000000000 : ℝ)*(X 0 2+X 1 2)+(410392149639/445400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11132991760773093341/11135000000000000000 : ℝ)) (alpha := (410392149639/445400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1818929643/10000000000 : ℝ)*X 0 0+(5428868313/10000000000 : ℝ)*X 0 1+(326197223/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((26748219/50000000 : ℝ)*X 1 0+(-1926263399/10000000000 : ℝ)*X 1 1+(5219155701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133741097/250000000 : ℝ)*X 2 0+(1304788903/2500000000 : ℝ)*X 2 1+(-1926263411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((531774353/1250000000 : ℝ)*X 0 0+(2008234821/5000000000 : ℝ)*X 0 1+(1125856407/2500000000 : ℝ)*X 0 2+(531774353/1250000000 : ℝ)*X 1 0+(2008234821/5000000000 : ℝ)*X 1 1+(1125856407/2500000000 : ℝ)*X 1 2+(531774353/1250000000 : ℝ)*X 2 0+(2008234821/5000000000 : ℝ)*X 2 1+(1125856407/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-72758293/400000000 : ℝ)*X 0 0+(5220242793/10000000000 : ℝ)*X 0 1+(5427773037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165447711/312500000 : ℝ)*X 1 0+(-429411521/2500000000 : ℝ)*X 1 1+(1085554607/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294326749/10000000000 : ℝ)*X 2 0+(2713886519/5000000000 : ℝ)*X 2 1+(-429411521/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127129507/5000000000 : ℝ)*X 0 0+(140653167/312500000 : ℝ)*X 0 1+(4019012577/10000000000 : ℝ)*X 0 2+(2127129507/5000000000 : ℝ)*X 1 0+(140653167/312500000 : ℝ)*X 1 1+(4019012577/10000000000 : ℝ)*X 1 2+(2127129507/5000000000 : ℝ)*X 2 0+(140653167/312500000 : ℝ)*X 2 1+(4019012577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2827579502066704609211686581/278375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1791629843/100000000000000 : ℝ)*(base19) + (1713496253/100000000000000 : ℝ)*(base23) + (79946609/100000000000000 : ℝ)*(lower2) + (1610911/625000000000 : ℝ)*(upper3) + (37296491/25000000000000 : ℝ)*(upper5) + (426380715095363/12500000000000 : ℝ)*(major0) + (426380715095363/12500000000000 : ℝ)*(major1) + (1705522860381453/50000000000000 : ℝ)*(major2) + (2384230093885287/50000000000000 : ℝ)*(sp0) + (953698027934401/20000000000000 : ℝ)*(sp1) + (2384245108902797/50000000000000 : ℝ)*(sp2) + (2053585457013621/100000000000000 : ℝ)*(sp3) + (15871765637/50000000000000 : ℝ)*(sp4) + (685731437/5000000000000 : ℝ)*(sp7) + (1026799585821181/50000000000000 : ℝ)*(f.failure) + (596061491412731/12500000000000 : ℝ)*(f.sum) + (2526904690869/4454000000000000000000000000 : ℝ)*base66 + (357501052085571533/139187500000000000000000000000000 : ℝ)*base67 + (7224189394848404473/556750000000000000000000000000000 : ℝ)*base69 + (1322287311121053467/139187500000000000000000000000000 : ℝ)*base72 + (17364559918121/4454000000000000000000000000 : ℝ)*base73 + (9348894747087154473/556750000000000000000000000000000 : ℝ)*base75 + (56563485335811601/8187500000000000000000000000000 : ℝ)*base78 + (8768761091313399/8187500000000000000000000000000 : ℝ)*base79 + (23210742054619/5567500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (20936553/1250000000000000000000 : ℝ)*base89 + (20936553/1250000000000000000000 : ℝ)*base91 + (4063447/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (362023441479112820121982449/69593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (829117163/100000000000000 : ℝ)*(base19) + (448399439/50000000000000 : ℝ)*(base23) + (269874993/100000000000000 : ℝ)*(lower1) + (338289/312500000000 : ℝ)*(upper3) + (7954233/25000000000000 : ℝ)*(lower4) + (107437263/100000000000000 : ℝ)*(upper5) + (861715408004563/25000000000000 : ℝ)*(major0) + (861715408004563/25000000000000 : ℝ)*(major1) + (861715408004563/25000000000000 : ℝ)*(major2) + (493656507/50000000000000 : ℝ)*(sp2) + (2409280584560837/50000000000000 : ℝ)*(sp4) + (481856034000451/10000000000000 : ℝ)*(sp5) + (2409279642504891/50000000000000 : ℝ)*(sp6) + (518790480379091/25000000000000 : ℝ)*(sp7) + (518790480379091/25000000000000 : ℝ)*(f.failure) + (2409280584560837/50000000000000 : ℝ)*(f.sum) + (1267163799269/695937500000000000000000000 : ℝ)*base65 + (314674261940230001/16375000000000000000000000000000 : ℝ)*base68 + (22230275703730001/16375000000000000000000000000000 : ℝ)*base70 + (2458157961597480001/16375000000000000000000000000000 : ℝ)*base72 + (5990573314377/5567500000000000000000000000 : ℝ)*base73 + (108002000237269999/16375000000000000000000000000000 : ℝ)*base75 + (58648343954730001/16375000000000000000000000000000 : ℝ)*base78 + (106482459572980001/16375000000000000000000000000000 : ℝ)*base80 + (9400051776351/2783750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (478617/625000000000000000000 : ℝ)*base90 + (478617/625000000000000000000 : ℝ)*base92 + (478617/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1546_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1546_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1546_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (397/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1546_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1546_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1546_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (397/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1546_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

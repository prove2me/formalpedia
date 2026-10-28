-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:35.904689+00:00
-- url     : https://prove2.me/submissions/4059356d-203d-4506-a88b-98a0b8a484ff

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
theorem support_rectangle_w1094_s3_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185685597/10000000000 : ℝ)*x 0 + (5434332577/10000000000 : ℝ)*x 1 + (2613673409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185685597/10000000000 : ℝ)^8287 ≤ (207310962717/1562500000000 : ℝ)^6239 := by
    have hnat : (2185685597 : ℕ)^8287*1562500000000^6239 ≤ 207310962717^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185685597 10000000000 207310962717 1562500000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434332577/10000000000 : ℝ)^8287 ≤ (8896842560573/20000000000000 : ℝ)^6239 := by
    have hnat : (5434332577 : ℕ)^8287*20000000000000^6239 ≤ 8896842560573^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434332577 10000000000 8896842560573 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613673409/5000000000 : ℝ)^8287 ≤ (1689915422539/4000000000000 : ℝ)^6239 := by
    have hnat : (2613673409 : ℕ)^8287*4000000000000^6239 ≤ 1689915422539^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613673409 5000000000 1689915422539 4000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185685597/10000000000 : ℝ), (5434332577/10000000000 : ℝ), (2613673409/5000000000 : ℝ)] ![(207310962717/1562500000000 : ℝ), (8896842560573/20000000000000 : ℝ), (1689915422539/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185685597/10000000000 : ℝ)|^8287 ≤ (207310962717/1562500000000 : ℝ)^6239
        have hw : |(-2185685597/10000000000 : ℝ)|=(2185685597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434332577/10000000000 : ℝ)|^8287 ≤ (8896842560573/20000000000000 : ℝ)^6239
        have hw : |(5434332577/10000000000 : ℝ)|=(5434332577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613673409/5000000000 : ℝ)|^8287 ≤ (1689915422539/4000000000000 : ℝ)^6239
        have hw : |(2613673409/5000000000 : ℝ)|=(2613673409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s3_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267748787/500000000 : ℝ)*x 0 + (-2291606191/10000000000 : ℝ)*x 1 + (5227346691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267748787/500000000 : ℝ)^8287 ≤ (10905863823179/25000000000000 : ℝ)^6239 := by
    have hnat : (267748787 : ℕ)^8287*25000000000000^6239 ≤ 10905863823179^6239*500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267748787 500000000 10905863823179 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2291606191/10000000000 : ℝ)^8287 ≤ (14128660487371/100000000000000 : ℝ)^6239 := by
    have hnat : (2291606191 : ℕ)^8287*100000000000000^6239 ≤ 14128660487371^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291606191 10000000000 14128660487371 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227346691/10000000000 : ℝ)^8287 ≤ (21123942100059/50000000000000 : ℝ)^6239 := by
    have hnat : (5227346691 : ℕ)^8287*50000000000000^6239 ≤ 21123942100059^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227346691 10000000000 21123942100059 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267748787/500000000 : ℝ), (-2291606191/10000000000 : ℝ), (5227346691/10000000000 : ℝ)] ![(10905863823179/25000000000000 : ℝ), (14128660487371/100000000000000 : ℝ), (21123942100059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267748787/500000000 : ℝ)|^8287 ≤ (10905863823179/25000000000000 : ℝ)^6239
        have hw : |(267748787/500000000 : ℝ)|=(267748787/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2291606191/10000000000 : ℝ)|^8287 ≤ (14128660487371/100000000000000 : ℝ)^6239
        have hw : |(-2291606191/10000000000 : ℝ)|=(2291606191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227346691/10000000000 : ℝ)|^8287 ≤ (21123942100059/50000000000000 : ℝ)^6239
        have hw : |(5227346691/10000000000 : ℝ)|=(5227346691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s3_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677487807/5000000000 : ℝ)*x 0 + (5227347139/10000000000 : ℝ)*x 1 + (-2291605771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677487807/5000000000 : ℝ)^8287 ≤ (2181172696467/5000000000000 : ℝ)^6239 := by
    have hnat : (2677487807 : ℕ)^8287*5000000000000^6239 ≤ 2181172696467^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677487807 5000000000 2181172696467 5000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227347139/10000000000 : ℝ)^8287 ≤ (21123944504721/50000000000000 : ℝ)^6239 := by
    have hnat : (5227347139 : ℕ)^8287*50000000000000^6239 ≤ 21123944504721^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227347139 10000000000 21123944504721 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2291605771/10000000000 : ℝ)^8287 ≤ (14128657047893/100000000000000 : ℝ)^6239 := by
    have hnat : (2291605771 : ℕ)^8287*100000000000000^6239 ≤ 14128657047893^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291605771 10000000000 14128657047893 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677487807/5000000000 : ℝ), (5227347139/10000000000 : ℝ), (-2291605771/10000000000 : ℝ)] ![(2181172696467/5000000000000 : ℝ), (21123944504721/50000000000000 : ℝ), (14128657047893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677487807/5000000000 : ℝ)|^8287 ≤ (2181172696467/5000000000000 : ℝ)^6239
        have hw : |(2677487807/5000000000 : ℝ)|=(2677487807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227347139/10000000000 : ℝ)|^8287 ≤ (21123944504721/50000000000000 : ℝ)^6239
        have hw : |(5227347139/10000000000 : ℝ)|=(5227347139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2291605771/10000000000 : ℝ)|^8287 ≤ (14128657047893/100000000000000 : ℝ)^6239
        have hw : |(-2291605771/10000000000 : ℝ)|=(2291605771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s3_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873778449/2000000000 : ℝ)*x 0 + (260607299/625000000 : ℝ)*x 1 + (4577635381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873778449/2000000000 : ℝ)^8287 ≤ (33290509526149/100000000000000 : ℝ)^6239 := by
    have hnat : (873778449 : ℕ)^8287*100000000000000^6239 ≤ 33290509526149^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873778449 2000000000 33290509526149 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260607299/625000000 : ℝ)^8287 ≤ (625797167471/2000000000000 : ℝ)^6239 := by
    have hnat : (260607299 : ℕ)^8287*2000000000000^6239 ≤ 625797167471^6239*625000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260607299 625000000 625797167471 2000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4577635381/10000000000 : ℝ)^8287 ≤ (17709816040961/50000000000000 : ℝ)^6239 := by
    have hnat : (4577635381 : ℕ)^8287*50000000000000^6239 ≤ 17709816040961^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4577635381 10000000000 17709816040961 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873778449/2000000000 : ℝ), (260607299/625000000 : ℝ), (4577635381/10000000000 : ℝ)] ![(33290509526149/100000000000000 : ℝ), (625797167471/2000000000000 : ℝ), (17709816040961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873778449/2000000000 : ℝ)|^8287 ≤ (33290509526149/100000000000000 : ℝ)^6239
        have hw : |(873778449/2000000000 : ℝ)|=(873778449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260607299/625000000 : ℝ)|^8287 ≤ (625797167471/2000000000000 : ℝ)^6239
        have hw : |(260607299/625000000 : ℝ)|=(260607299/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4577635381/10000000000 : ℝ)|^8287 ≤ (17709816040961/50000000000000 : ℝ)^6239
        have hw : |(4577635381/10000000000 : ℝ)|=(4577635381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s3_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092853169/5000000000 : ℝ)*x 0 + (1307044517/2500000000 : ℝ)*x 1 + (5433496433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092853169/5000000000 : ℝ)^8287 ≤ (6634034424463/50000000000000 : ℝ)^6239 := by
    have hnat : (1092853169 : ℕ)^8287*50000000000000^6239 ≤ 6634034424463^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092853169 5000000000 6634034424463 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307044517/2500000000 : ℝ)^8287 ≤ (21128404673319/50000000000000 : ℝ)^6239 := by
    have hnat : (1307044517 : ℕ)^8287*50000000000000^6239 ≤ 21128404673319^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307044517 2500000000 21128404673319 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433496433/10000000000 : ℝ)^8287 ≤ (44475121792367/100000000000000 : ℝ)^6239 := by
    have hnat : (5433496433 : ℕ)^8287*100000000000000^6239 ≤ 44475121792367^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433496433 10000000000 44475121792367 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092853169/5000000000 : ℝ), (1307044517/2500000000 : ℝ), (5433496433/10000000000 : ℝ)] ![(6634034424463/50000000000000 : ℝ), (21128404673319/50000000000000 : ℝ), (44475121792367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092853169/5000000000 : ℝ)|^8287 ≤ (6634034424463/50000000000000 : ℝ)^6239
        have hw : |(-1092853169/5000000000 : ℝ)|=(1092853169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307044517/2500000000 : ℝ)|^8287 ≤ (21128404673319/50000000000000 : ℝ)^6239
        have hw : |(1307044517/2500000000 : ℝ)|=(1307044517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433496433/10000000000 : ℝ)|^8287 ≤ (44475121792367/100000000000000 : ℝ)^6239
        have hw : |(5433496433/10000000000 : ℝ)|=(5433496433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s3_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302724053/10000000000 : ℝ)*x 0 + (-2085456329/10000000000 : ℝ)*x 1 + (54334967/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302724053/10000000000 : ℝ)^8287 ≤ (1722359060831/4000000000000 : ℝ)^6239 := by
    have hnat : (5302724053 : ℕ)^8287*4000000000000^6239 ≤ 1722359060831^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302724053 10000000000 1722359060831 4000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085456329/10000000000 : ℝ)^8287 ≤ (2493179753743/20000000000000 : ℝ)^6239 := by
    have hnat : (2085456329 : ℕ)^8287*20000000000000^6239 ≤ 2493179753743^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085456329 10000000000 2493179753743 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54334967/100000000 : ℝ)^8287 ≤ (44475124695263/100000000000000 : ℝ)^6239 := by
    have hnat : (54334967 : ℕ)^8287*100000000000000^6239 ≤ 44475124695263^6239*100000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54334967 100000000 44475124695263 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302724053/10000000000 : ℝ), (-2085456329/10000000000 : ℝ), (54334967/100000000 : ℝ)] ![(1722359060831/4000000000000 : ℝ), (2493179753743/20000000000000 : ℝ), (44475124695263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302724053/10000000000 : ℝ)|^8287 ≤ (1722359060831/4000000000000 : ℝ)^6239
        have hw : |(5302724053/10000000000 : ℝ)|=(5302724053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2085456329/10000000000 : ℝ)|^8287 ≤ (2493179753743/20000000000000 : ℝ)^6239
        have hw : |(-2085456329/10000000000 : ℝ)|=(2085456329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54334967/100000000 : ℝ)|^8287 ≤ (44475124695263/100000000000000 : ℝ)^6239
        have hw : |(54334967/100000000 : ℝ)|=(54334967/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s3_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2651362091/5000000000 : ℝ)*x 0 + (5433496457/10000000000 : ℝ)*x 1 + (-260682061/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651362091/5000000000 : ℝ)^8287 ≤ (21529488956063/50000000000000 : ℝ)^6239 := by
    have hnat : (2651362091 : ℕ)^8287*50000000000000^6239 ≤ 21529488956063^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651362091 5000000000 21529488956063 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433496457/10000000000 : ℝ)^8287 ≤ (22237561026651/50000000000000 : ℝ)^6239 := by
    have hnat : (5433496457 : ℕ)^8287*50000000000000^6239 ≤ 22237561026651^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433496457 10000000000 22237561026651 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260682061/1250000000 : ℝ)^8287 ≤ (1246590003113/10000000000000 : ℝ)^6239 := by
    have hnat : (260682061 : ℕ)^8287*10000000000000^6239 ≤ 1246590003113^6239*1250000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260682061 1250000000 1246590003113 10000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651362091/5000000000 : ℝ), (5433496457/10000000000 : ℝ), (-260682061/1250000000 : ℝ)] ![(21529488956063/50000000000000 : ℝ), (22237561026651/50000000000000 : ℝ), (1246590003113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651362091/5000000000 : ℝ)|^8287 ≤ (21529488956063/50000000000000 : ℝ)^6239
        have hw : |(2651362091/5000000000 : ℝ)|=(2651362091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433496457/10000000000 : ℝ)|^8287 ≤ (22237561026651/50000000000000 : ℝ)^6239
        have hw : |(5433496457/10000000000 : ℝ)|=(5433496457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260682061/1250000000 : ℝ)|^8287 ≤ (1246590003113/10000000000000 : ℝ)^6239
        have hw : |(-260682061/1250000000 : ℝ)|=(260682061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s3_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184466343/5000000000 : ℝ)*x 0 + (183039919/400000000 : ℝ)*x 1 + (2085681931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184466343/5000000000 : ℝ)^8287 ≤ (16645459418853/50000000000000 : ℝ)^6239 := by
    have hnat : (2184466343 : ℕ)^8287*50000000000000^6239 ≤ 16645459418853^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184466343 5000000000 16645459418853 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183039919/400000000 : ℝ)^8287 ≤ (17701402359147/50000000000000 : ℝ)^6239 := by
    have hnat : (183039919 : ℕ)^8287*50000000000000^6239 ≤ 17701402359147^6239*400000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183039919 400000000 17701402359147 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085681931/5000000000 : ℝ)^8287 ≤ (31306276428777/100000000000000 : ℝ)^6239 := by
    have hnat : (2085681931 : ℕ)^8287*100000000000000^6239 ≤ 31306276428777^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085681931 5000000000 31306276428777 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184466343/5000000000 : ℝ), (183039919/400000000 : ℝ), (2085681931/5000000000 : ℝ)] ![(16645459418853/50000000000000 : ℝ), (17701402359147/50000000000000 : ℝ), (31306276428777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184466343/5000000000 : ℝ)|^8287 ≤ (16645459418853/50000000000000 : ℝ)^6239
        have hw : |(2184466343/5000000000 : ℝ)|=(2184466343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183039919/400000000 : ℝ)|^8287 ≤ (17701402359147/50000000000000 : ℝ)^6239
        have hw : |(183039919/400000000 : ℝ)|=(183039919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085681931/5000000000 : ℝ)|^8287 ≤ (31306276428777/100000000000000 : ℝ)^6239
        have hw : |(2085681931/5000000000 : ℝ)|=(2085681931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (333/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10487/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14867/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (333/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8847/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (333/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8847/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (333/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8847/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (333/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8847/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (333/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8847/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (333/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8847/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8847/100000 : ℝ) ^ (4143/1024 : ℝ) ≤ (5480796691760231/100000000000000000000 : ℝ) := by
    have hpowers : (8847/100000 : ℝ)^4143 ≤ (5480796691760231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8847 : ℕ)^4143*100000000000000000000^1024 ≤ 5480796691760231^1024*100000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8847 100000 5480796691760231 100000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8847/100000 : ℝ)) (X := (5480796691760231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (333/2000 : ℝ) ^ (4143/1024 : ℝ) ≤ (2211928595245253/3125000000000000000 : ℝ) := by
    have hpowers : (333/2000 : ℝ)^4143 ≤ (2211928595245253/3125000000000000000 : ℝ)^1024 := by
      have hnat : (333 : ℕ)^4143*3125000000000000000^1024 ≤ 2211928595245253^1024*2000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        333 2000 2211928595245253 3125000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (333/2000 : ℝ)) (X := (2211928595245253/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005480796691760231/50000000000000000000 : ℝ) ≤ (10000270919828833/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (50005480796691760231/50000000000000000000 : ℝ)^1024 ≤ (10000270919828833/10000000000000000 : ℝ)^4143 := by
      have hnat : (50005480796691760231 : ℕ)^1024*10000000000000000^4143 ≤ 10000270919828833^4143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005480796691760231 50000000000000000000 10000270919828833 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000270919828833/10000000000000000 : ℝ)) (X := (50005480796691760231/50000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100076262511739608327/100000000000000000000 : ℝ) ≤ (10001884393053939/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (100076262511739608327/100000000000000000000 : ℝ)^1024 ≤ (10001884393053939/10000000000000000 : ℝ)^4143 := by
      have hnat : (100076262511739608327 : ℕ)^1024*10000000000000000^4143 ≤ 10001884393053939^4143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100076262511739608327 100000000000000000000 10001884393053939 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001884393053939/10000000000000000 : ℝ)) (X := (100076262511739608327/100000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1564711928595245253/1562500000000000000 : ℝ) ≤ (2000699573255809/2000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (1564711928595245253/1562500000000000000 : ℝ)^1024 ≤ (2000699573255809/2000000000000000 : ℝ)^4143 := by
      have hnat : (1564711928595245253 : ℕ)^1024*2000000000000000^4143 ≤ 2000699573255809^4143*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1564711928595245253 1562500000000000000 2000699573255809 2000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000699573255809/2000000000000000 : ℝ)) (X := (1564711928595245253/1562500000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5480796691760231/100000000000000000000 : ℝ) ≤ ((1733412559826207963/1734000000000000000 : ℝ)+2*(806736612553/390150000000000 : ℝ)*(8847/100000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (1733412559826207963/1734000000000000000 : ℝ)+2*(806736612553/390150000000000 : ℝ)*(8847/100000 : ℝ)=(10000270919828833/10000000000000000 : ℝ) by norm_num, show 1+2*(5480796691760231/100000000000000000000 : ℝ)=(50005480796691760231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2211928595245253/3125000000000000000 : ℝ)+(5480796691760231/100000000000000000000 : ℝ) ≤ ((1733412559826207963/1734000000000000000 : ℝ)+(806736612553/390150000000000 : ℝ)*((333/2000 : ℝ)+(8847/100000 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (1733412559826207963/1734000000000000000 : ℝ)+(806736612553/390150000000000 : ℝ)*((333/2000 : ℝ)+(8847/100000 : ℝ))=(10001884393053939/10000000000000000 : ℝ) by norm_num, show 1+(2211928595245253/3125000000000000000 : ℝ)+(5480796691760231/100000000000000000000 : ℝ)=(100076262511739608327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2211928595245253/3125000000000000000 : ℝ) ≤ ((1733412559826207963/1734000000000000000 : ℝ)+2*(806736612553/390150000000000 : ℝ)*(333/2000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (1733412559826207963/1734000000000000000 : ℝ)+2*(806736612553/390150000000000 : ℝ)*(333/2000 : ℝ)=(2000699573255809/2000000000000000 : ℝ) by norm_num, show 1+2*(2211928595245253/3125000000000000000 : ℝ)=(1564711928595245253/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1733412559826207963/1734000000000000000 : ℝ)*(X 1 0+X 2 0)+(806736612553/390150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (8847/100000 : ℝ)) (hi := (333/2000 : ℝ)) (c := (1733412559826207963/1734000000000000000 : ℝ)) (alpha := (806736612553/390150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1733412559826207963/1734000000000000000 : ℝ)*(X 0 1+X 2 1)+(806736612553/390150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (8847/100000 : ℝ)) (hi := (333/2000 : ℝ)) (c := (1733412559826207963/1734000000000000000 : ℝ)) (alpha := (806736612553/390150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1733412559826207963/1734000000000000000 : ℝ)*(X 0 2+X 1 2)+(806736612553/390150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (8847/100000 : ℝ)) (hi := (333/2000 : ℝ)) (c := (1733412559826207963/1734000000000000000 : ℝ)) (alpha := (806736612553/390150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2185685597/10000000000 : ℝ)*X 0 0+(5434332577/10000000000 : ℝ)*X 0 1+(2613673409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267748787/500000000 : ℝ)*X 1 0+(-2291606191/10000000000 : ℝ)*X 1 1+(5227346691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677487807/5000000000 : ℝ)*X 2 0+(5227347139/10000000000 : ℝ)*X 2 1+(-2291605771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873778449/2000000000 : ℝ)*X 0 0+(260607299/625000000 : ℝ)*X 0 1+(4577635381/10000000000 : ℝ)*X 0 2+(873778449/2000000000 : ℝ)*X 1 0+(260607299/625000000 : ℝ)*X 1 1+(4577635381/10000000000 : ℝ)*X 1 2+(873778449/2000000000 : ℝ)*X 2 0+(260607299/625000000 : ℝ)*X 2 1+(4577635381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1092853169/5000000000 : ℝ)*X 0 0+(1307044517/2500000000 : ℝ)*X 0 1+(5433496433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302724053/10000000000 : ℝ)*X 1 0+(-2085456329/10000000000 : ℝ)*X 1 1+(54334967/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651362091/5000000000 : ℝ)*X 2 0+(5433496457/10000000000 : ℝ)*X 2 1+(-260682061/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184466343/5000000000 : ℝ)*X 0 0+(183039919/400000000 : ℝ)*X 0 1+(2085681931/5000000000 : ℝ)*X 0 2+(2184466343/5000000000 : ℝ)*X 1 0+(183039919/400000000 : ℝ)*X 1 1+(2085681931/5000000000 : ℝ)*X 1 2+(2184466343/5000000000 : ℝ)*X 2 0+(183039919/400000000 : ℝ)*X 2 1+(2085681931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (459005263620491638473296381/65025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14973071/800000000000 : ℝ)*(base19) + (676587089/50000000000000 : ℝ)*(base23) + (216759349/100000000000000 : ℝ)*(lower2) + (238359/250000000000 : ℝ)*(upper3) + (182063941/100000000000000 : ℝ)*(upper5) + (1820703487004143/50000000000000 : ℝ)*(major0) + (1820703487004143/50000000000000 : ℝ)*(major1) + (1820703487004143/50000000000000 : ℝ)*(major2) + (2415640002419971/50000000000000 : ℝ)*(sp0) + (2415656931410851/50000000000000 : ℝ)*(sp1) + (4831314381281399/100000000000000 : ℝ)*(sp2) + (612870928740439/25000000000000 : ℝ)*(sp3) + (7145923127/20000000000000 : ℝ)*(sp4) + (2852660483/20000000000000 : ℝ)*(sp7) + (612874494566043/25000000000000 : ℝ)*(f.failure) + (4831315734455577/100000000000000 : ℝ)*(f.sum) + (63996971630363/19507500000000000000000000000 : ℝ)*base65 + (6853345950424423619/780300000000000000000000000000000 : ℝ)*base68 + (5007814906214623619/780300000000000000000000000000000 : ℝ)*base70 + (5549638147788523619/780300000000000000000000000000000 : ℝ)*base72 + (185796369116611/39015000000000000000000000000 : ℝ)*base73 + (5964582537665923619/780300000000000000000000000000000 : ℝ)*base76 + (3646716250820323619/780300000000000000000000000000000 : ℝ)*base78 + (357965241791476381/780300000000000000000000000000000 : ℝ)*base79 + (8533323046739/39015000000000000000000000000 : ℝ)*base82 + (44077591/2500000000000000000000 : ℝ)*base89 + (44077591/2500000000000000000000 : ℝ)*base91 + (44077591/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2498381810918365159753449041/260100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (440773539/25000000000000 : ℝ)*(base19) + (1085556711/50000000000000 : ℝ)*(base23) + (16870351/6250000000000 : ℝ)*(upper3) + (129277021/100000000000000 : ℝ)*(lower4) + (117304727/100000000000000 : ℝ)*(upper5) + (3670924624145959/100000000000000 : ℝ)*(major0) + (3670924624145959/100000000000000 : ℝ)*(major1) + (3670924624145959/100000000000000 : ℝ)*(major2) + (6453879867/20000000000000 : ℝ)*(sp1) + (36911570777/100000000000000 : ℝ)*(sp2) + (4870478834437353/100000000000000 : ℝ)*(sp4) + (2435222400971931/50000000000000 : ℝ)*(sp5) + (2435219875876577/50000000000000 : ℝ)*(sp6) + (1235685046836171/50000000000000 : ℝ)*(sp7) + (1235685046836171/50000000000000 : ℝ)*(f.failure) + (4870478834437353/100000000000000 : ℝ)*(f.sum) + (2513694607199/2438437500000000000000000000 : ℝ)*base65 + (11080872317421323653/1560600000000000000000000000000000 : ℝ)*base67 + (13173972135861923653/1560600000000000000000000000000000 : ℝ)*base69 + (11895295235934923653/1560600000000000000000000000000000 : ℝ)*base71 + (7991509894351/39015000000000000000000000000 : ℝ)*base74 + (2180100653280323653/1560600000000000000000000000000000 : ℝ)*base75 + (11270498850822923653/1560600000000000000000000000000000 : ℝ)*base77 + (15965615274275123653/1560600000000000000000000000000000 : ℝ)*base79 + (155943054617879/39015000000000000000000000000 : ℝ)*base81 + (49063673/5000000000000000000000 : ℝ)*base90 + (49063673/5000000000000000000000 : ℝ)*base92 + (49063673/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1094_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (333/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14867/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1094_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1094_s4_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094548629/5000000000 : ℝ)*x 0 + (337769121/625000000 : ℝ)*x 1 + (1051028741/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094548629/5000000000 : ℝ)^8287 ≤ (6647708448483/50000000000000 : ℝ)^6239 := by
    have hnat : (1094548629 : ℕ)^8287*50000000000000^6239 ≤ 6647708448483^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094548629 5000000000 6647708448483 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337769121/625000000 : ℝ)^8287 ≤ (8831607017809/20000000000000 : ℝ)^6239 := by
    have hnat : (337769121 : ℕ)^8287*20000000000000^6239 ≤ 8831607017809^6239*625000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337769121 625000000 8831607017809 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051028741/2000000000 : ℝ)^8287 ≤ (42546547998591/100000000000000 : ℝ)^6239 := by
    have hnat : (1051028741 : ℕ)^8287*100000000000000^6239 ≤ 42546547998591^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051028741 2000000000 42546547998591 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094548629/5000000000 : ℝ), (337769121/625000000 : ℝ), (1051028741/2000000000 : ℝ)] ![(6647708448483/50000000000000 : ℝ), (8831607017809/20000000000000 : ℝ), (42546547998591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094548629/5000000000 : ℝ)|^8287 ≤ (6647708448483/50000000000000 : ℝ)^6239
        have hw : |(-1094548629/5000000000 : ℝ)|=(1094548629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337769121/625000000 : ℝ)|^8287 ≤ (8831607017809/20000000000000 : ℝ)^6239
        have hw : |(337769121/625000000 : ℝ)|=(337769121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051028741/2000000000 : ℝ)|^8287 ≤ (42546547998591/100000000000000 : ℝ)^6239
        have hw : |(1051028741/2000000000 : ℝ)|=(1051028741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s4_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069503097/2000000000 : ℝ)*x 0 + (-2264939159/10000000000 : ℝ)*x 1 + (5255144207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069503097/2000000000 : ℝ)^8287 ≤ (21771375258607/50000000000000 : ℝ)^6239 := by
    have hnat : (1069503097 : ℕ)^8287*50000000000000^6239 ≤ 21771375258607^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069503097 2000000000 21771375258607 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264939159/10000000000 : ℝ)^8287 ≤ (13910696074463/100000000000000 : ℝ)^6239 := by
    have hnat : (2264939159 : ℕ)^8287*100000000000000^6239 ≤ 13910696074463^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264939159 10000000000 13910696074463 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255144207/10000000000 : ℝ)^8287 ≤ (42546553397/100000000000 : ℝ)^6239 := by
    have hnat : (5255144207 : ℕ)^8287*100000000000^6239 ≤ 42546553397^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255144207 10000000000 42546553397 100000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069503097/2000000000 : ℝ), (-2264939159/10000000000 : ℝ), (5255144207/10000000000 : ℝ)] ![(21771375258607/50000000000000 : ℝ), (13910696074463/100000000000000 : ℝ), (42546553397/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069503097/2000000000 : ℝ)|^8287 ≤ (21771375258607/50000000000000 : ℝ)^6239
        have hw : |(1069503097/2000000000 : ℝ)|=(1069503097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2264939159/10000000000 : ℝ)|^8287 ≤ (13910696074463/100000000000000 : ℝ)^6239
        have hw : |(-2264939159/10000000000 : ℝ)|=(2264939159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255144207/10000000000 : ℝ)|^8287 ≤ (42546553397/100000000000 : ℝ)^6239
        have hw : |(5255144207/10000000000 : ℝ)|=(5255144207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s4_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673757817/5000000000 : ℝ)*x 0 + (5255144053/10000000000 : ℝ)*x 1 + (-566234791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673757817/5000000000 : ℝ)^8287 ≤ (21771376064361/50000000000000 : ℝ)^6239 := by
    have hnat : (2673757817 : ℕ)^8287*50000000000000^6239 ≤ 21771376064361^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673757817 5000000000 21771376064361 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255144053/10000000000 : ℝ)^8287 ≤ (8509310348183/20000000000000 : ℝ)^6239 := by
    have hnat : (5255144053 : ℕ)^8287*20000000000000^6239 ≤ 8509310348183^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255144053 10000000000 8509310348183 20000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566234791/2500000000 : ℝ)^8287 ≤ (3477674028813/25000000000000 : ℝ)^6239 := by
    have hnat : (566234791 : ℕ)^8287*25000000000000^6239 ≤ 3477674028813^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566234791 2500000000 3477674028813 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673757817/5000000000 : ℝ), (5255144053/10000000000 : ℝ), (-566234791/2500000000 : ℝ)] ![(21771376064361/50000000000000 : ℝ), (8509310348183/20000000000000 : ℝ), (3477674028813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673757817/5000000000 : ℝ)|^8287 ≤ (21771376064361/50000000000000 : ℝ)^6239
        have hw : |(2673757817/5000000000 : ℝ)|=(2673757817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255144053/10000000000 : ℝ)|^8287 ≤ (8509310348183/20000000000000 : ℝ)^6239
        have hw : |(5255144053/10000000000 : ℝ)|=(5255144053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-566234791/2500000000 : ℝ)|^8287 ≤ (3477674028813/25000000000000 : ℝ)^6239
        have hw : |(-566234791/2500000000 : ℝ)|=(566234791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s4_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546365629/1250000000 : ℝ)*x 0 + (1056607323/2500000000 : ℝ)*x 1 + (35315561/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546365629/1250000000 : ℝ)^8287 ≤ (33311085315157/100000000000000 : ℝ)^6239 := by
    have hnat : (546365629 : ℕ)^8287*100000000000000^6239 ≤ 33311085315157^6239*1250000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546365629 1250000000 33311085315157 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056607323/2500000000 : ℝ)^8287 ≤ (497756084851/1562500000000 : ℝ)^6239 := by
    have hnat : (1056607323 : ℕ)^8287*1562500000000^6239 ≤ 497756084851^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056607323 2500000000 497756084851 1562500000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35315561/78125000 : ℝ)^8287 ≤ (696650504797/2000000000000 : ℝ)^6239 := by
    have hnat : (35315561 : ℕ)^8287*2000000000000^6239 ≤ 696650504797^6239*78125000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35315561 78125000 696650504797 2000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546365629/1250000000 : ℝ), (1056607323/2500000000 : ℝ), (35315561/78125000 : ℝ)] ![(33311085315157/100000000000000 : ℝ), (497756084851/1562500000000 : ℝ), (696650504797/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546365629/1250000000 : ℝ)|^8287 ≤ (33311085315157/100000000000000 : ℝ)^6239
        have hw : |(546365629/1250000000 : ℝ)|=(546365629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056607323/2500000000 : ℝ)|^8287 ≤ (497756084851/1562500000000 : ℝ)^6239
        have hw : |(1056607323/2500000000 : ℝ)|=(1056607323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35315561/78125000 : ℝ)|^8287 ≤ (696650504797/2000000000000 : ℝ)^6239
        have hw : |(35315561/78125000 : ℝ)|=(35315561/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s4_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-547276121/2500000000 : ℝ)*x 0 + (2627788277/5000000000 : ℝ)*x 1 + (5403871663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547276121/2500000000 : ℝ)^8287 ≤ (6647737595053/50000000000000 : ℝ)^6239 := by
    have hnat : (547276121 : ℕ)^8287*50000000000000^6239 ≤ 6647737595053^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547276121 2500000000 6647737595053 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627788277/5000000000 : ℝ)^8287 ≤ (42551202834497/100000000000000 : ℝ)^6239 := by
    have hnat : (2627788277 : ℕ)^8287*100000000000000^6239 ≤ 42551202834497^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627788277 5000000000 42551202834497 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403871663/10000000000 : ℝ)^8287 ≤ (22076660980341/50000000000000 : ℝ)^6239 := by
    have hnat : (5403871663 : ℕ)^8287*50000000000000^6239 ≤ 22076660980341^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403871663 10000000000 22076660980341 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547276121/2500000000 : ℝ), (2627788277/5000000000 : ℝ), (5403871663/10000000000 : ℝ)] ![(6647737595053/50000000000000 : ℝ), (42551202834497/100000000000000 : ℝ), (22076660980341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547276121/2500000000 : ℝ)|^8287 ≤ (6647737595053/50000000000000 : ℝ)^6239
        have hw : |(-547276121/2500000000 : ℝ)|=(547276121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627788277/5000000000 : ℝ)|^8287 ≤ (42551202834497/100000000000000 : ℝ)^6239
        have hw : |(2627788277/5000000000 : ℝ)|=(2627788277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403871663/10000000000 : ℝ)|^8287 ≤ (22076660980341/50000000000000 : ℝ)^6239
        have hw : |(5403871663/10000000000 : ℝ)|=(5403871663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s4_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654931953/5000000000 : ℝ)*x 0 + (-2116211299/10000000000 : ℝ)*x 1 + (675483991/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654931953/5000000000 : ℝ)^8287 ≤ (84250003153/195312500000 : ℝ)^6239 := by
    have hnat : (2654931953 : ℕ)^8287*195312500000^6239 ≤ 84250003153^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654931953 5000000000 84250003153 195312500000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116211299/10000000000 : ℝ)^8287 ≤ (12710673532777/100000000000000 : ℝ)^6239 := by
    have hnat : (2116211299 : ℕ)^8287*100000000000000^6239 ≤ 12710673532777^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116211299 10000000000 12710673532777 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675483991/1250000000 : ℝ)^8287 ≤ (44153324836667/100000000000000 : ℝ)^6239 := by
    have hnat : (675483991 : ℕ)^8287*100000000000000^6239 ≤ 44153324836667^6239*1250000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675483991 1250000000 44153324836667 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654931953/5000000000 : ℝ), (-2116211299/10000000000 : ℝ), (675483991/1250000000 : ℝ)] ![(84250003153/195312500000 : ℝ), (12710673532777/100000000000000 : ℝ), (44153324836667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654931953/5000000000 : ℝ)|^8287 ≤ (84250003153/195312500000 : ℝ)^6239
        have hw : |(2654931953/5000000000 : ℝ)|=(2654931953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2116211299/10000000000 : ℝ)|^8287 ≤ (12710673532777/100000000000000 : ℝ)^6239
        have hw : |(-2116211299/10000000000 : ℝ)|=(2116211299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675483991/1250000000 : ℝ)|^8287 ≤ (44153324836667/100000000000000 : ℝ)^6239
        have hw : |(675483991/1250000000 : ℝ)|=(675483991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s4_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309863727/10000000000 : ℝ)*x 0 + (5403871953/10000000000 : ℝ)*x 1 + (-529052877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309863727/10000000000 : ℝ)^8287 ≤ (43135999682849/100000000000000 : ℝ)^6239 := by
    have hnat : (5309863727 : ℕ)^8287*100000000000000^6239 ≤ 43135999682849^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309863727 10000000000 43135999682849 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403871953/10000000000 : ℝ)^8287 ≤ (22076662553993/50000000000000 : ℝ)^6239 := by
    have hnat : (5403871953 : ℕ)^8287*50000000000000^6239 ≤ 22076662553993^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403871953 10000000000 22076662553993 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529052877/2500000000 : ℝ)^8287 ≤ (12710675200171/100000000000000 : ℝ)^6239 := by
    have hnat : (529052877 : ℕ)^8287*100000000000000^6239 ≤ 12710675200171^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529052877 2500000000 12710675200171 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309863727/10000000000 : ℝ), (5403871953/10000000000 : ℝ), (-529052877/2500000000 : ℝ)] ![(43135999682849/100000000000000 : ℝ), (22076662553993/50000000000000 : ℝ), (12710675200171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309863727/10000000000 : ℝ)|^8287 ≤ (43135999682849/100000000000000 : ℝ)^6239
        have hw : |(5309863727/10000000000 : ℝ)|=(5309863727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403871953/10000000000 : ℝ)|^8287 ≤ (22076662553993/50000000000000 : ℝ)^6239
        have hw : |(5403871953/10000000000 : ℝ)|=(5403871953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529052877/2500000000 : ℝ)|^8287 ≤ (12710675200171/100000000000000 : ℝ)^6239
        have hw : |(-529052877/2500000000 : ℝ)|=(529052877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s4_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185469933/5000000000 : ℝ)*x 0 + (1129884871/2500000000 : ℝ)*x 1 + (264205349/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185469933/5000000000 : ℝ)^8287 ≤ (33311235475861/100000000000000 : ℝ)^6239 := by
    have hnat : (2185469933 : ℕ)^8287*100000000000000^6239 ≤ 33311235475861^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185469933 5000000000 33311235475861 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129884871/2500000000 : ℝ)^8287 ≤ (8705950476411/25000000000000 : ℝ)^6239 := by
    have hnat : (1129884871 : ℕ)^8287*25000000000000^6239 ≤ 8705950476411^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129884871 2500000000 8705950476411 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264205349/625000000 : ℝ)^8287 ≤ (15932481302099/50000000000000 : ℝ)^6239 := by
    have hnat : (264205349 : ℕ)^8287*50000000000000^6239 ≤ 15932481302099^6239*625000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264205349 625000000 15932481302099 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185469933/5000000000 : ℝ), (1129884871/2500000000 : ℝ), (264205349/625000000 : ℝ)] ![(33311235475861/100000000000000 : ℝ), (8705950476411/25000000000000 : ℝ), (15932481302099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185469933/5000000000 : ℝ)|^8287 ≤ (33311235475861/100000000000000 : ℝ)^6239
        have hw : |(2185469933/5000000000 : ℝ)|=(2185469933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129884871/2500000000 : ℝ)|^8287 ≤ (8705950476411/25000000000000 : ℝ)^6239
        have hw : |(1129884871/2500000000 : ℝ)|=(1129884871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264205349/625000000 : ℝ)|^8287 ≤ (15932481302099/50000000000000 : ℝ)^6239
        have hw : |(264205349/625000000 : ℝ)|=(264205349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14867/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11081/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14867/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14867/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14867/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14867/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14867/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14867/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10487/100000 : ℝ) ^ (4143/1024 : ℝ) ≤ (5452861912158901/50000000000000000000 : ℝ) := by
    have hpowers : (10487/100000 : ℝ)^4143 ≤ (5452861912158901/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10487 : ℕ)^4143*50000000000000000000^1024 ≤ 5452861912158901^1024*100000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10487 100000 5452861912158901 50000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10487/100000 : ℝ)) (X := (5452861912158901/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14867/100000 : ℝ) ^ (4143/1024 : ℝ) ≤ (2238049639265037/5000000000000000000 : ℝ) := by
    have hpowers : (14867/100000 : ℝ)^4143 ≤ (2238049639265037/5000000000000000000 : ℝ)^1024 := by
      have hnat : (14867 : ℕ)^4143*5000000000000000000^1024 ≤ 2238049639265037^1024*100000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14867 100000 2238049639265037 5000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14867/100000 : ℝ)) (X := (2238049639265037/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005452861912158901/25000000000000000000 : ℝ) ≤ (2500134763992753/2500000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (25005452861912158901/25000000000000000000 : ℝ)^1024 ≤ (2500134763992753/2500000000000000 : ℝ)^4143 := by
      have hnat : (25005452861912158901 : ℕ)^1024*2500000000000000^4143 ≤ 2500134763992753^4143*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005452861912158901 25000000000000000000 2500134763992753 2500000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134763992753/2500000000000000 : ℝ)) (X := (25005452861912158901/25000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027833358304809271/50000000000000000000 : ℝ) ≤ (10001375592019469/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (50027833358304809271/50000000000000000000 : ℝ)^1024 ≤ (10001375592019469/10000000000000000 : ℝ)^4143 := by
      have hnat : (50027833358304809271 : ℕ)^1024*10000000000000000^4143 ≤ 10001375592019469^4143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027833358304809271 50000000000000000000 10001375592019469 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001375592019469/10000000000000000 : ℝ)) (X := (50027833358304809271/50000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502238049639265037/2500000000000000000 : ℝ) ≤ (5001106064033963/5000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (2502238049639265037/2500000000000000000 : ℝ)^1024 ≤ (5001106064033963/5000000000000000 : ℝ)^4143 := by
      have hnat : (2502238049639265037 : ℕ)^1024*5000000000000000^4143 ≤ 5001106064033963^4143*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502238049639265037 2500000000000000000 5001106064033963 5000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001106064033963/5000000000000000 : ℝ)) (X := (2502238049639265037/2500000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5452861912158901/50000000000000000000 : ℝ) ≤ ((21892407779036347721/21900000000000000000 : ℝ)+2*(836536048457/438000000000000 : ℝ)*(10487/100000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (21892407779036347721/21900000000000000000 : ℝ)+2*(836536048457/438000000000000 : ℝ)*(10487/100000 : ℝ)=(2500134763992753/2500000000000000 : ℝ) by norm_num, show 1+2*(5452861912158901/50000000000000000000 : ℝ)=(25005452861912158901/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2238049639265037/5000000000000000000 : ℝ)+(5452861912158901/50000000000000000000 : ℝ) ≤ ((21892407779036347721/21900000000000000000 : ℝ)+(836536048457/438000000000000 : ℝ)*((14867/100000 : ℝ)+(10487/100000 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (21892407779036347721/21900000000000000000 : ℝ)+(836536048457/438000000000000 : ℝ)*((14867/100000 : ℝ)+(10487/100000 : ℝ))=(10001375592019469/10000000000000000 : ℝ) by norm_num, show 1+(2238049639265037/5000000000000000000 : ℝ)+(5452861912158901/50000000000000000000 : ℝ)=(50027833358304809271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2238049639265037/5000000000000000000 : ℝ) ≤ ((21892407779036347721/21900000000000000000 : ℝ)+2*(836536048457/438000000000000 : ℝ)*(14867/100000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (21892407779036347721/21900000000000000000 : ℝ)+2*(836536048457/438000000000000 : ℝ)*(14867/100000 : ℝ)=(5001106064033963/5000000000000000 : ℝ) by norm_num, show 1+2*(2238049639265037/5000000000000000000 : ℝ)=(2502238049639265037/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21892407779036347721/21900000000000000000 : ℝ)*(X 1 0+X 2 0)+(836536048457/438000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (10487/100000 : ℝ)) (hi := (14867/100000 : ℝ)) (c := (21892407779036347721/21900000000000000000 : ℝ)) (alpha := (836536048457/438000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21892407779036347721/21900000000000000000 : ℝ)*(X 0 1+X 2 1)+(836536048457/438000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (10487/100000 : ℝ)) (hi := (14867/100000 : ℝ)) (c := (21892407779036347721/21900000000000000000 : ℝ)) (alpha := (836536048457/438000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21892407779036347721/21900000000000000000 : ℝ)*(X 0 2+X 1 2)+(836536048457/438000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (10487/100000 : ℝ)) (hi := (14867/100000 : ℝ)) (c := (21892407779036347721/21900000000000000000 : ℝ)) (alpha := (836536048457/438000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1094548629/5000000000 : ℝ)*X 0 0+(337769121/625000000 : ℝ)*X 0 1+(1051028741/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069503097/2000000000 : ℝ)*X 1 0+(-2264939159/10000000000 : ℝ)*X 1 1+(5255144207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673757817/5000000000 : ℝ)*X 2 0+(5255144053/10000000000 : ℝ)*X 2 1+(-566234791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546365629/1250000000 : ℝ)*X 0 0+(1056607323/2500000000 : ℝ)*X 0 1+(35315561/78125000 : ℝ)*X 0 2+(546365629/1250000000 : ℝ)*X 1 0+(1056607323/2500000000 : ℝ)*X 1 1+(35315561/78125000 : ℝ)*X 1 2+(546365629/1250000000 : ℝ)*X 2 0+(1056607323/2500000000 : ℝ)*X 2 1+(35315561/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-547276121/2500000000 : ℝ)*X 0 0+(2627788277/5000000000 : ℝ)*X 0 1+(5403871663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654931953/5000000000 : ℝ)*X 1 0+(-2116211299/10000000000 : ℝ)*X 1 1+(675483991/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309863727/10000000000 : ℝ)*X 2 0+(5403871953/10000000000 : ℝ)*X 2 1+(-529052877/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185469933/5000000000 : ℝ)*X 0 0+(1129884871/2500000000 : ℝ)*X 0 1+(264205349/625000000 : ℝ)*X 0 2+(2185469933/5000000000 : ℝ)*X 1 0+(1129884871/2500000000 : ℝ)*X 1 1+(264205349/625000000 : ℝ)*X 1 2+(2185469933/5000000000 : ℝ)*X 2 0+(1129884871/2500000000 : ℝ)*X 2 1+(264205349/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (566134924699943455329/7300000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1203956593/100000000000000 : ℝ)*(base19) + (44242299/4000000000000 : ℝ)*(base23) + (314239137/100000000000000 : ℝ)*(upper3) + (9515259/6250000000000 : ℝ)*(upper4) + (16875571/12500000000000 : ℝ)*(upper5) + (5053010397992097/100000000000000 : ℝ)*(major0) + (5053010397992097/100000000000000 : ℝ)*(major1) + (5053010397992097/100000000000000 : ℝ)*(major2) + (838018953522339/12500000000000 : ℝ)*(sp0) + (6704190334090151/100000000000000 : ℝ)*(sp1) + (6704190431989269/100000000000000 : ℝ)*(sp2) + (340180908533551/10000000000000 : ℝ)*(sp3) + (77948961/195312500000 : ℝ)*(sp4) + (20170016839/100000000000000 : ℝ)*(sp7) + (68036585107047/2000000000000 : ℝ)*(f.failure) + (838023942255843/12500000000000 : ℝ)*(f.sum) + (12839386101557/7300000000000000000000000000 : ℝ)*base66 + (8996228683573863021/730000000000000000000000000000000 : ℝ)*base68 + (15356388760946136979/730000000000000000000000000000000 : ℝ)*base69 + (2301684823863863021/730000000000000000000000000000000 : ℝ)*base72 + (32547519323657/7300000000000000000000000000 : ℝ)*base74 + (415318101816136979/730000000000000000000000000000000 : ℝ)*base75 + (9495667559106136979/730000000000000000000000000000000 : ℝ)*base77 + (7245258784383863021/730000000000000000000000000000000 : ℝ)*base80 + (19935006119443/7300000000000000000000000000 : ℝ)*base81 + (2246739/200000000000000000000 : ℝ)*base89 + (2246739/200000000000000000000 : ℝ)*base91 + (2246739/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1118237386959763779648626149/182500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1039046981/100000000000000 : ℝ)*(base19) + (229922723/25000000000000 : ℝ)*(base23) + (11015471/20000000000000 : ℝ)*(upper3) + (94010777/100000000000000 : ℝ)*(lower4) + (18007291/12500000000000 : ℝ)*(upper5) + (5082494132820469/100000000000000 : ℝ)*(major0) + (5082494132820469/100000000000000 : ℝ)*(major1) + (5082494132820469/100000000000000 : ℝ)*(major2) + (20210746289/50000000000000 : ℝ)*(sp1) + (6135747143/20000000000000 : ℝ)*(sp2) + (134866190467597/2000000000000 : ℝ)*(sp4) + (6743268062840291/100000000000000 : ℝ)*(sp5) + (6743277924953243/100000000000000 : ℝ)*(sp6) + (3421678538016811/100000000000000 : ℝ)*(sp7) + (3421678538016811/100000000000000 : ℝ)*(f.failure) + (134866190467597/2000000000000 : ℝ)*(f.sum) + (86607771086933/21900000000000000000000000000 : ℝ)*base65 + (5684687262964349617/730000000000000000000000000000000 : ℝ)*base68 + (6345075010464349617/730000000000000000000000000000000 : ℝ)*base70 + (679969666095650383/730000000000000000000000000000000 : ℝ)*base71 + (90250402458367/21900000000000000000000000000 : ℝ)*base74 + (6821221995584349617/730000000000000000000000000000000 : ℝ)*base76 + (635766270254349617/730000000000000000000000000000000 : ℝ)*base78 + (5997864251984349617/730000000000000000000000000000000 : ℝ)*base80 + (49935126218333/21900000000000000000000000000 : ℝ)*base81 + (78940007/10000000000000000000000 : ℝ)*base89 + (78940007/10000000000000000000000 : ℝ)*base91 + (78940007/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1094_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14867/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1094_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1094_s5_0 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189849663/10000000000 : ℝ)*x 0 + (5396205729/10000000000 : ℝ)*x 1 + (2631375199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189849663/10000000000 : ℝ)^8287 ≤ (1662685873887/12500000000000 : ℝ)^6239 := by
    have hnat : (2189849663 : ℕ)^8287*12500000000000^6239 ≤ 1662685873887^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189849663 10000000000 1662685873887 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396205729/10000000000 : ℝ)^8287 ≤ (22035072348919/50000000000000 : ℝ)^6239 := by
    have hnat : (5396205729 : ℕ)^8287*50000000000000^6239 ≤ 22035072348919^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396205729 10000000000 22035072348919 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631375199/5000000000 : ℝ)^8287 ≤ (333034127389/781250000000 : ℝ)^6239 := by
    have hnat : (2631375199 : ℕ)^8287*781250000000^6239 ≤ 333034127389^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631375199 5000000000 333034127389 781250000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189849663/10000000000 : ℝ), (5396205729/10000000000 : ℝ), (2631375199/5000000000 : ℝ)] ![(1662685873887/12500000000000 : ℝ), (22035072348919/50000000000000 : ℝ), (333034127389/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189849663/10000000000 : ℝ)|^8287 ≤ (1662685873887/12500000000000 : ℝ)^6239
        have hw : |(-2189849663/10000000000 : ℝ)|=(2189849663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396205729/10000000000 : ℝ)|^8287 ≤ (22035072348919/50000000000000 : ℝ)^6239
        have hw : |(5396205729/10000000000 : ℝ)|=(5396205729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631375199/5000000000 : ℝ)|^8287 ≤ (333034127389/781250000000 : ℝ)^6239
        have hw : |(2631375199/5000000000 : ℝ)|=(2631375199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s5_1 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672746363/5000000000 : ℝ)*x 0 + (-2257586643/10000000000 : ℝ)*x 1 + (5262751277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672746363/5000000000 : ℝ)^8287 ≤ (21760437373873/50000000000000 : ℝ)^6239 := by
    have hnat : (2672746363 : ℕ)^8287*50000000000000^6239 ≤ 21760437373873^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672746363 5000000000 21760437373873 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257586643/10000000000 : ℝ)^8287 ≤ (6925373738237/50000000000000 : ℝ)^6239 := by
    have hnat : (2257586643 : ℕ)^8287*50000000000000^6239 ≤ 6925373738237^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257586643 10000000000 6925373738237 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262751277/10000000000 : ℝ)^8287 ≤ (341027022103/800000000000 : ℝ)^6239 := by
    have hnat : (5262751277 : ℕ)^8287*800000000000^6239 ≤ 341027022103^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262751277 10000000000 341027022103 800000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672746363/5000000000 : ℝ), (-2257586643/10000000000 : ℝ), (5262751277/10000000000 : ℝ)] ![(21760437373873/50000000000000 : ℝ), (6925373738237/50000000000000 : ℝ), (341027022103/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672746363/5000000000 : ℝ)|^8287 ≤ (21760437373873/50000000000000 : ℝ)^6239
        have hw : |(2672746363/5000000000 : ℝ)|=(2672746363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2257586643/10000000000 : ℝ)|^8287 ≤ (6925373738237/50000000000000 : ℝ)^6239
        have hw : |(-2257586643/10000000000 : ℝ)|=(2257586643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262751277/10000000000 : ℝ)|^8287 ≤ (341027022103/800000000000 : ℝ)^6239
        have hw : |(5262751277/10000000000 : ℝ)|=(5262751277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s5_2 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167046657/312500000 : ℝ)*x 0 + (2631375371/5000000000 : ℝ)*x 1 + (-1128793477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167046657/312500000 : ℝ)^8287 ≤ (21760438985181/50000000000000 : ℝ)^6239 := by
    have hnat : (167046657 : ℕ)^8287*50000000000000^6239 ≤ 21760438985181^6239*312500000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167046657 312500000 21760438985181 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631375371/5000000000 : ℝ)^8287 ≤ (21314186003429/50000000000000 : ℝ)^6239 := by
    have hnat : (2631375371 : ℕ)^8287*50000000000000^6239 ≤ 21314186003429^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631375371 5000000000 21314186003429 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128793477/5000000000 : ℝ)^8287 ≤ (13850750010853/100000000000000 : ℝ)^6239 := by
    have hnat : (1128793477 : ℕ)^8287*100000000000000^6239 ≤ 13850750010853^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128793477 5000000000 13850750010853 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167046657/312500000 : ℝ), (2631375371/5000000000 : ℝ), (-1128793477/5000000000 : ℝ)] ![(21760438985181/50000000000000 : ℝ), (21314186003429/50000000000000 : ℝ), (13850750010853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167046657/312500000 : ℝ)|^8287 ≤ (21760438985181/50000000000000 : ℝ)^6239
        have hw : |(167046657/312500000 : ℝ)|=(167046657/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631375371/5000000000 : ℝ)|^8287 ≤ (21314186003429/50000000000000 : ℝ)^6239
        have hw : |(2631375371/5000000000 : ℝ)|=(2631375371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1128793477/5000000000 : ℝ)|^8287 ≤ (13850750010853/100000000000000 : ℝ)^6239
        have hw : |(-1128793477/5000000000 : ℝ)|=(1128793477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s5_3 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874272661/2000000000 : ℝ)*x 0 + (2120924731/5000000000 : ℝ)*x 1 + (4504857007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874272661/2000000000 : ℝ)^8287 ≤ (3331552190869/10000000000000 : ℝ)^6239 := by
    have hnat : (874272661 : ℕ)^8287*10000000000000^6239 ≤ 3331552190869^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874272661 2000000000 3331552190869 10000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120924731/5000000000 : ℝ)^8287 ≤ (32010863019083/100000000000000 : ℝ)^6239 := by
    have hnat : (2120924731 : ℕ)^8287*100000000000000^6239 ≤ 32010863019083^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120924731 5000000000 32010863019083 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504857007/10000000000 : ℝ)^8287 ≤ (2167100941489/6250000000000 : ℝ)^6239 := by
    have hnat : (4504857007 : ℕ)^8287*6250000000000^6239 ≤ 2167100941489^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504857007 10000000000 2167100941489 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874272661/2000000000 : ℝ), (2120924731/5000000000 : ℝ), (4504857007/10000000000 : ℝ)] ![(3331552190869/10000000000000 : ℝ), (32010863019083/100000000000000 : ℝ), (2167100941489/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874272661/2000000000 : ℝ)|^8287 ≤ (3331552190869/10000000000000 : ℝ)^6239
        have hw : |(874272661/2000000000 : ℝ)|=(874272661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120924731/5000000000 : ℝ)|^8287 ≤ (32010863019083/100000000000000 : ℝ)^6239
        have hw : |(2120924731/5000000000 : ℝ)|=(2120924731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504857007/10000000000 : ℝ)|^8287 ≤ (2167100941489/6250000000000 : ℝ)^6239
        have hw : |(4504857007/10000000000 : ℝ)|=(4504857007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s5_4 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-21898549/100000000 : ℝ)*x 0 + (2631548573/5000000000 : ℝ)*x 1 + (5395857917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21898549/100000000 : ℝ)^8287 ≤ (6650764621729/50000000000000 : ℝ)^6239 := by
    have hnat : (21898549 : ℕ)^8287*50000000000000^6239 ≤ 6650764621729^6239*100000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21898549 100000000 6650764621729 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631548573/5000000000 : ℝ)^8287 ≤ (42632098976791/100000000000000 : ℝ)^6239 := by
    have hnat : (2631548573 : ℕ)^8287*100000000000000^6239 ≤ 42632098976791^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631548573 5000000000 42632098976791 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395857917/10000000000 : ℝ)^8287 ≤ (44066371771743/100000000000000 : ℝ)^6239 := by
    have hnat : (5395857917 : ℕ)^8287*100000000000000^6239 ≤ 44066371771743^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395857917 10000000000 44066371771743 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21898549/100000000 : ℝ), (2631548573/5000000000 : ℝ), (5395857917/10000000000 : ℝ)] ![(6650764621729/50000000000000 : ℝ), (42632098976791/100000000000000 : ℝ), (44066371771743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21898549/100000000 : ℝ)|^8287 ≤ (6650764621729/50000000000000 : ℝ)^6239
        have hw : |(-21898549/100000000 : ℝ)|=(21898549/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631548573/5000000000 : ℝ)|^8287 ≤ (42632098976791/100000000000000 : ℝ)^6239
        have hw : |(2631548573/5000000000 : ℝ)|=(2631548573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395857917/10000000000 : ℝ)|^8287 ≤ (44066371771743/100000000000000 : ℝ)^6239
        have hw : |(5395857917/10000000000 : ℝ)|=(5395857917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s5_5 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311804933/10000000000 : ℝ)*x 0 + (-424895967/2000000000 : ℝ)*x 1 + (2697928911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311804933/10000000000 : ℝ)^8287 ≤ (43156947391559/100000000000000 : ℝ)^6239 := by
    have hnat : (5311804933 : ℕ)^8287*100000000000000^6239 ≤ 43156947391559^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311804933 10000000000 43156947391559 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424895967/2000000000 : ℝ)^8287 ≤ (1597085231731/12500000000000 : ℝ)^6239 := by
    have hnat : (424895967 : ℕ)^8287*12500000000000^6239 ≤ 1597085231731^6239*2000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424895967 2000000000 1597085231731 12500000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697928911/5000000000 : ℝ)^8287 ≤ (2754148171327/6250000000000 : ℝ)^6239 := by
    have hnat : (2697928911 : ℕ)^8287*6250000000000^6239 ≤ 2754148171327^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697928911 5000000000 2754148171327 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311804933/10000000000 : ℝ), (-424895967/2000000000 : ℝ), (2697928911/5000000000 : ℝ)] ![(43156947391559/100000000000000 : ℝ), (1597085231731/12500000000000 : ℝ), (2754148171327/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311804933/10000000000 : ℝ)|^8287 ≤ (43156947391559/100000000000000 : ℝ)^6239
        have hw : |(5311804933/10000000000 : ℝ)|=(5311804933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424895967/2000000000 : ℝ)|^8287 ≤ (1597085231731/12500000000000 : ℝ)^6239
        have hw : |(-424895967/2000000000 : ℝ)|=(424895967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697928911/5000000000 : ℝ)|^8287 ≤ (2754148171327/6250000000000 : ℝ)^6239
        have hw : |(2697928911/5000000000 : ℝ)|=(2697928911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s5_6 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311804913/10000000000 : ℝ)*x 0 + (1348964471/2500000000 : ℝ)*x 1 + (-2124479777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311804913/10000000000 : ℝ)^8287 ≤ (1726277887029/4000000000000 : ℝ)^6239 := by
    have hnat : (5311804913 : ℕ)^8287*4000000000000^6239 ≤ 1726277887029^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311804913 10000000000 1726277887029 4000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348964471/2500000000 : ℝ)^8287 ≤ (2754148213361/6250000000000 : ℝ)^6239 := by
    have hnat : (1348964471 : ℕ)^8287*6250000000000^6239 ≤ 2754148213361^6239*2500000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348964471 2500000000 2754148213361 6250000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124479777/10000000000 : ℝ)^8287 ≤ (6388340695267/50000000000000 : ℝ)^6239 := by
    have hnat : (2124479777 : ℕ)^8287*50000000000000^6239 ≤ 6388340695267^6239*10000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124479777 10000000000 6388340695267 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311804913/10000000000 : ℝ), (1348964471/2500000000 : ℝ), (-2124479777/10000000000 : ℝ)] ![(1726277887029/4000000000000 : ℝ), (2754148213361/6250000000000 : ℝ), (6388340695267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311804913/10000000000 : ℝ)|^8287 ≤ (1726277887029/4000000000000 : ℝ)^6239
        have hw : |(5311804913/10000000000 : ℝ)|=(5311804913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348964471/2500000000 : ℝ)|^8287 ≤ (2754148213361/6250000000000 : ℝ)^6239
        have hw : |(1348964471/2500000000 : ℝ)|=(1348964471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124479777/10000000000 : ℝ)|^8287 ≤ (6388340695267/50000000000000 : ℝ)^6239
        have hw : |(-2124479777/10000000000 : ℝ)|=(2124479777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1094_s5_7 (p : ℝ) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185686871/5000000000 : ℝ)*x 0 + (90083493/200000000 : ℝ)*x 1 + (84850697/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185686871/5000000000 : ℝ)^8287 ≤ (8328906890793/25000000000000 : ℝ)^6239 := by
    have hnat : (2185686871 : ℕ)^8287*25000000000000^6239 ≤ 8328906890793^6239*5000000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185686871 5000000000 8328906890793 25000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90083493/200000000 : ℝ)^8287 ≤ (17333319573287/50000000000000 : ℝ)^6239 := by
    have hnat : (90083493 : ℕ)^8287*50000000000000^6239 ≤ 17333319573287^6239*200000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90083493 200000000 17333319573287 50000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84850697/200000000 : ℝ)^8287 ≤ (32017733268397/100000000000000 : ℝ)^6239 := by
    have hnat : (84850697 : ℕ)^8287*100000000000000^6239 ≤ 32017733268397^6239*200000000^8287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84850697 200000000 32017733268397 100000000000000 8287 6239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8287/2048 : ℝ)) 8287 6239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185686871/5000000000 : ℝ), (90083493/200000000 : ℝ), (84850697/200000000 : ℝ)] ![(8328906890793/25000000000000 : ℝ), (17333319573287/50000000000000 : ℝ), (32017733268397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185686871/5000000000 : ℝ)|^8287 ≤ (8328906890793/25000000000000 : ℝ)^6239
        have hw : |(2185686871/5000000000 : ℝ)|=(2185686871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90083493/200000000 : ℝ)|^8287 ≤ (17333319573287/50000000000000 : ℝ)^6239
        have hw : |(90083493/200000000 : ℝ)|=(90083493/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84850697/200000000 : ℝ)|^8287 ≤ (32017733268397/100000000000000 : ℝ)^6239
        have hw : |(84850697/200000000 : ℝ)|=(84850697/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1094_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11081/100000 : ℝ) ^ (4143/1024 : ℝ) ≤ (13628984147312613/100000000000000000000 : ℝ) := by
    have hpowers : (11081/100000 : ℝ)^4143 ≤ (13628984147312613/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11081 : ℕ)^4143*100000000000000000000^1024 ≤ 13628984147312613^1024*100000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11081 100000 13628984147312613 100000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11081/100000 : ℝ)) (X := (13628984147312613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (4143/1024 : ℝ) ≤ (3758927863450717/10000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^4143 ≤ (3758927863450717/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14239 : ℕ)^4143*10000000000000000000^1024 ≤ 3758927863450717^1024*100000^4143 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 3758927863450717 10000000000000000000 4143 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (3758927863450717/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013628984147312613/50000000000000000000 : ℝ) ≤ (10000673649435021/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (50013628984147312613/50000000000000000000 : ℝ)^1024 ≤ (10000673649435021/10000000000000000 : ℝ)^4143 := by
      have hnat : (50013628984147312613 : ℕ)^1024*10000000000000000^4143 ≤ 10000673649435021^4143*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013628984147312613 50000000000000000000 10000673649435021 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000673649435021/10000000000000000 : ℝ)) (X := (50013628984147312613/50000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051218262781819783/100000000000000000000 : ℝ) ≤ (10001265686519639/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (100051218262781819783/100000000000000000000 : ℝ)^1024 ≤ (10001265686519639/10000000000000000 : ℝ)^4143 := by
      have hnat : (100051218262781819783 : ℕ)^1024*10000000000000000^4143 ≤ 10001265686519639^4143*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051218262781819783 100000000000000000000 10001265686519639 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001265686519639/10000000000000000 : ℝ)) (X := (100051218262781819783/100000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003758927863450717/5000000000000000000 : ℝ) ≤ (10001857723604257/10000000000000000 : ℝ) ^ (4143/1024 : ℝ) := by
    have hpowers : (5003758927863450717/5000000000000000000 : ℝ)^1024 ≤ (10001857723604257/10000000000000000 : ℝ)^4143 := by
      have hnat : (5003758927863450717 : ℕ)^1024*10000000000000000^4143 ≤ 10001857723604257^4143*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003758927863450717 5000000000000000000 10001857723604257 10000000000000000 1024 4143 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001857723604257/10000000000000000 : ℝ)) (X := (5003758927863450717/5000000000000000000 : ℝ)) (by norm_num) 4143 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13628984147312613/100000000000000000000 : ℝ) ≤ ((15784503329523246101/15790000000000000000 : ℝ)+2*(296018542309/157900000000000 : ℝ)*(11081/100000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (15784503329523246101/15790000000000000000 : ℝ)+2*(296018542309/157900000000000 : ℝ)*(11081/100000 : ℝ)=(10000673649435021/10000000000000000 : ℝ) by norm_num, show 1+2*(13628984147312613/100000000000000000000 : ℝ)=(50013628984147312613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3758927863450717/10000000000000000000 : ℝ)+(13628984147312613/100000000000000000000 : ℝ) ≤ ((15784503329523246101/15790000000000000000 : ℝ)+(296018542309/157900000000000 : ℝ)*((14239/100000 : ℝ)+(11081/100000 : ℝ)))^(4143/1024 : ℝ) := by
    rw [show (15784503329523246101/15790000000000000000 : ℝ)+(296018542309/157900000000000 : ℝ)*((14239/100000 : ℝ)+(11081/100000 : ℝ))=(10001265686519639/10000000000000000 : ℝ) by norm_num, show 1+(3758927863450717/10000000000000000000 : ℝ)+(13628984147312613/100000000000000000000 : ℝ)=(100051218262781819783/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3758927863450717/10000000000000000000 : ℝ) ≤ ((15784503329523246101/15790000000000000000 : ℝ)+2*(296018542309/157900000000000 : ℝ)*(14239/100000 : ℝ))^(4143/1024 : ℝ) := by
    rw [show (15784503329523246101/15790000000000000000 : ℝ)+2*(296018542309/157900000000000 : ℝ)*(14239/100000 : ℝ)=(10001857723604257/10000000000000000 : ℝ) by norm_num, show 1+2*(3758927863450717/10000000000000000000 : ℝ)=(5003758927863450717/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15784503329523246101/15790000000000000000 : ℝ)*(X 1 0+X 2 0)+(296018542309/157900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (15784503329523246101/15790000000000000000 : ℝ)) (alpha := (296018542309/157900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15784503329523246101/15790000000000000000 : ℝ)*(X 0 1+X 2 1)+(296018542309/157900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (15784503329523246101/15790000000000000000 : ℝ)) (alpha := (296018542309/157900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15784503329523246101/15790000000000000000 : ℝ)*(X 0 2+X 1 2)+(296018542309/157900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4143/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (15784503329523246101/15790000000000000000 : ℝ)) (alpha := (296018542309/157900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2189849663/10000000000 : ℝ)*X 0 0+(5396205729/10000000000 : ℝ)*X 0 1+(2631375199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672746363/5000000000 : ℝ)*X 1 0+(-2257586643/10000000000 : ℝ)*X 1 1+(5262751277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167046657/312500000 : ℝ)*X 2 0+(2631375371/5000000000 : ℝ)*X 2 1+(-1128793477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874272661/2000000000 : ℝ)*X 0 0+(2120924731/5000000000 : ℝ)*X 0 1+(4504857007/10000000000 : ℝ)*X 0 2+(874272661/2000000000 : ℝ)*X 1 0+(2120924731/5000000000 : ℝ)*X 1 1+(4504857007/10000000000 : ℝ)*X 1 2+(874272661/2000000000 : ℝ)*X 2 0+(2120924731/5000000000 : ℝ)*X 2 1+(4504857007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21898549/100000000 : ℝ)*X 0 0+(2631548573/5000000000 : ℝ)*X 0 1+(5395857917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311804933/10000000000 : ℝ)*X 1 0+(-424895967/2000000000 : ℝ)*X 1 1+(2697928911/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311804913/10000000000 : ℝ)*X 2 0+(1348964471/2500000000 : ℝ)*X 2 1+(-2124479777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185686871/5000000000 : ℝ)*X 0 0+(90083493/200000000 : ℝ)*X 0 1+(84850697/200000000 : ℝ)*X 0 2+(2185686871/5000000000 : ℝ)*X 1 0+(90083493/200000000 : ℝ)*X 1 1+(84850697/200000000 : ℝ)*X 1 2+(2185686871/5000000000 : ℝ)*X 2 0+(90083493/200000000 : ℝ)*X 2 1+(84850697/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1094_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (752245801114854771050264571/197375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (670815109/100000000000000 : ℝ)*(base19) + (526171037/50000000000000 : ℝ)*(base23) + (18359187/50000000000000 : ℝ)*(lower2) + (212749249/50000000000000 : ℝ)*(upper3) + (17364761/100000000000000 : ℝ)*(lower4) + (1411931231069281/25000000000000 : ℝ)*(major0) + (1411931231069281/25000000000000 : ℝ)*(major1) + (1411931231069281/25000000000000 : ℝ)*(major2) + (1873300116669423/25000000000000 : ℝ)*(sp0) + (1873310296601661/25000000000000 : ℝ)*(sp1) + (7493240804879679/100000000000000 : ℝ)*(sp2) + (3802184721346861/100000000000000 : ℝ)*(sp3) + (41390544061/100000000000000 : ℝ)*(sp4) + (23142943903/100000000000000 : ℝ)*(sp7) + (950551966072691/25000000000000 : ℝ)*(f.failure) + (7493241857221753/100000000000000 : ℝ)*(f.sum) + (44409865427509/7895000000000000000000000000 : ℝ)*base66 + (3929213970733523381/394750000000000000000000000000000 : ℝ)*base67 + (3399664020709523381/394750000000000000000000000000000 : ℝ)*base69 + (6044182992745773381/394750000000000000000000000000000 : ℝ)*base71 + (6264958477121/1973750000000000000000000000 : ℝ)*base74 + (3021737462393273381/394750000000000000000000000000000 : ℝ)*base75 + (646455277643773381/394750000000000000000000000000000 : ℝ)*base77 + (6347166496464523381/394750000000000000000000000000000 : ℝ)*base79 + (45773749383529/7895000000000000000000000000 : ℝ)*base82 + (20447567/2500000000000000000000 : ℝ)*base89 + (20447567/2500000000000000000000 : ℝ)*base91 + (20447567/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99231033504929756048490471/24671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132576829/50000000000000 : ℝ)*(base19) + (481652377/100000000000000 : ℝ)*(base23) + (838599/6250000000000 : ℝ)*(upper3) + (12517513/12500000000000 : ℝ)*(lower4) + (354824710337543/6250000000000 : ℝ)*(major0) + (354824710337543/6250000000000 : ℝ)*(major1) + (354824710337543/6250000000000 : ℝ)*(major2) + (1393833611/50000000000000 : ℝ)*(sp1) + (11670441559/100000000000000 : ℝ)*(sp2) + (18413347/12500000000000 : ℝ)*(sp3) + (3766171199737917/50000000000000 : ℝ)*(sp4) + (1506467869330991/20000000000000 : ℝ)*(sp5) + (3766165123690949/50000000000000 : ℝ)*(sp6) + (3822048049951067/100000000000000 : ℝ)*(sp7) + (955512049314461/25000000000000 : ℝ)*(f.failure) + (3766171199737917/50000000000000 : ℝ)*(f.sum) + (27062093344981/3947500000000000000000000000 : ℝ)*base65 + (720258154618994843/98687500000000000000000000000000 : ℝ)*base67 + (1198333333282369843/98687500000000000000000000000000 : ℝ)*base69 + (2262715973922432343/98687500000000000000000000000000 : ℝ)*base71 + (16279448159147/7895000000000000000000000000 : ℝ)*base73 + (1304803331364755157/98687500000000000000000000000000 : ℝ)*base76 + (1562989120570119843/98687500000000000000000000000000 : ℝ)*base77 + (3191817427379369843/98687500000000000000000000000000 : ℝ)*base79 + (16272724937671/3947500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (32653057/2500000000000000000000 : ℝ)*base89 + (32653057/2500000000000000000000 : ℝ)*base91 + (32653057/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1094_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1094_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1094_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (333/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1094_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1094_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1094_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4143/1024 : ℝ) ≤ p) (hpb : p ≤ (8287/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148538037/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (333/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1094_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

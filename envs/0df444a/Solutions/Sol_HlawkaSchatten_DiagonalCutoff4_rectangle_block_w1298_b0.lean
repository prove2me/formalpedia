-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:35:26.244335+00:00
-- url     : https://prove2.me/submissions/2f76160d-25dd-4c00-9049-4cfada7662da

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
theorem support_rectangle_w1298_s0_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-14683569/80000000 : ℝ)*x 0 + (3008068973/5000000000 : ℝ)*x 1 + (4800303297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14683569/80000000 : ℝ)^2129 ≤ (10730400389313/100000000000000 : ℝ)^1617 := by
    have hnat : (14683569 : ℕ)^2129*100000000000000^1617 ≤ 10730400389313^1617*80000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14683569 80000000 10730400389313 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3008068973/5000000000 : ℝ)^2129 ≤ (51220275303413/100000000000000 : ℝ)^1617 := by
    have hnat : (3008068973 : ℕ)^2129*100000000000000^1617 ≤ 51220275303413^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008068973 5000000000 51220275303413 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4800303297/10000000000 : ℝ)^2129 ≤ (9512331072433/25000000000000 : ℝ)^1617 := by
    have hnat : (4800303297 : ℕ)^2129*25000000000000^1617 ≤ 9512331072433^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800303297 10000000000 9512331072433 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14683569/80000000 : ℝ), (3008068973/5000000000 : ℝ), (4800303297/10000000000 : ℝ)] ![(10730400389313/100000000000000 : ℝ), (51220275303413/100000000000000 : ℝ), (9512331072433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14683569/80000000 : ℝ)|^2129 ≤ (10730400389313/100000000000000 : ℝ)^1617
        have hw : |(-14683569/80000000 : ℝ)|=(14683569/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3008068973/5000000000 : ℝ)|^2129 ≤ (51220275303413/100000000000000 : ℝ)^1617
        have hw : |(3008068973/5000000000 : ℝ)|=(3008068973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4800303297/10000000000 : ℝ)|^2129 ≤ (9512331072433/25000000000000 : ℝ)^1617
        have hw : |(4800303297/10000000000 : ℝ)|=(4800303297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s0_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1101349033/2000000000 : ℝ)*x 0 + (-2528762063/10000000000 : ℝ)*x 1 + (4800303269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101349033/2000000000 : ℝ)^2129 ≤ (1823530615403/4000000000000 : ℝ)^1617 := by
    have hnat : (1101349033 : ℕ)^2129*4000000000000^1617 ≤ 1823530615403^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101349033 2000000000 1823530615403 4000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2528762063/10000000000 : ℝ)^2129 ≤ (16362410605611/100000000000000 : ℝ)^1617 := by
    have hnat : (2528762063 : ℕ)^2129*100000000000000^1617 ≤ 16362410605611^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528762063 10000000000 16362410605611 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4800303269/10000000000 : ℝ)^2129 ≤ (38049323997517/100000000000000 : ℝ)^1617 := by
    have hnat : (4800303269 : ℕ)^2129*100000000000000^1617 ≤ 38049323997517^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800303269 10000000000 38049323997517 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1101349033/2000000000 : ℝ), (-2528762063/10000000000 : ℝ), (4800303269/10000000000 : ℝ)] ![(1823530615403/4000000000000 : ℝ), (16362410605611/100000000000000 : ℝ), (38049323997517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1101349033/2000000000 : ℝ)|^2129 ≤ (1823530615403/4000000000000 : ℝ)^1617
        have hw : |(1101349033/2000000000 : ℝ)|=(1101349033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2528762063/10000000000 : ℝ)|^2129 ≤ (16362410605611/100000000000000 : ℝ)^1617
        have hw : |(-2528762063/10000000000 : ℝ)|=(2528762063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4800303269/10000000000 : ℝ)|^2129 ≤ (38049323997517/100000000000000 : ℝ)^1617
        have hw : |(4800303269/10000000000 : ℝ)|=(4800303269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s0_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (275337257/500000000 : ℝ)*x 0 + (1200075827/2500000000 : ℝ)*x 1 + (-1264381023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275337257/500000000 : ℝ)^2129 ≤ (45588265112577/100000000000000 : ℝ)^1617 := by
    have hnat : (275337257 : ℕ)^2129*100000000000000^1617 ≤ 45588265112577^1617*500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275337257 500000000 45588265112577 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1200075827/2500000000 : ℝ)^2129 ≤ (3804932440453/10000000000000 : ℝ)^1617 := by
    have hnat : (1200075827 : ℕ)^2129*10000000000000^1617 ≤ 3804932440453^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200075827 2500000000 3804932440453 10000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1264381023/5000000000 : ℝ)^2129 ≤ (16362410460783/100000000000000 : ℝ)^1617 := by
    have hnat : (1264381023 : ℕ)^2129*100000000000000^1617 ≤ 16362410460783^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264381023 5000000000 16362410460783 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275337257/500000000 : ℝ), (1200075827/2500000000 : ℝ), (-1264381023/5000000000 : ℝ)] ![(45588265112577/100000000000000 : ℝ), (3804932440453/10000000000000 : ℝ), (16362410460783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275337257/500000000 : ℝ)|^2129 ≤ (45588265112577/100000000000000 : ℝ)^1617
        have hw : |(275337257/500000000 : ℝ)|=(275337257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1200075827/2500000000 : ℝ)|^2129 ≤ (3804932440453/10000000000000 : ℝ)^1617
        have hw : |(1200075827/2500000000 : ℝ)|=(1200075827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1264381023/5000000000 : ℝ)|^2129 ≤ (16362410460783/100000000000000 : ℝ)^1617
        have hw : |(-1264381023/5000000000 : ℝ)|=(1264381023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s0_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (20927053/50000000 : ℝ)*x 0 + (388631013/1250000000 : ℝ)*x 1 + (2806803291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20927053/50000000 : ℝ)^2129 ≤ (3970789225261/12500000000000 : ℝ)^1617 := by
    have hnat : (20927053 : ℕ)^2129*12500000000000^1617 ≤ 3970789225261^1617*50000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20927053 50000000 3970789225261 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388631013/1250000000 : ℝ)^2129 ≤ (5369268994191/25000000000000 : ℝ)^1617 := by
    have hnat : (388631013 : ℕ)^2129*25000000000000^1617 ≤ 5369268994191^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388631013 1250000000 5369268994191 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2806803291/5000000000 : ℝ)^2129 ≤ (23378305106471/50000000000000 : ℝ)^1617 := by
    have hnat : (2806803291 : ℕ)^2129*50000000000000^1617 ≤ 23378305106471^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806803291 5000000000 23378305106471 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20927053/50000000 : ℝ), (388631013/1250000000 : ℝ), (2806803291/5000000000 : ℝ)] ![(3970789225261/12500000000000 : ℝ), (5369268994191/25000000000000 : ℝ), (23378305106471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20927053/50000000 : ℝ)|^2129 ≤ (3970789225261/12500000000000 : ℝ)^1617
        have hw : |(20927053/50000000 : ℝ)|=(20927053/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388631013/1250000000 : ℝ)|^2129 ≤ (5369268994191/25000000000000 : ℝ)^1617
        have hw : |(388631013/1250000000 : ℝ)|=(388631013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2806803291/5000000000 : ℝ)|^2129 ≤ (23378305106471/50000000000000 : ℝ)^1617
        have hw : |(2806803291/5000000000 : ℝ)|=(2806803291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s0_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1840136489/10000000000 : ℝ)*x 0 + (4831674553/10000000000 : ℝ)*x 1 + (2991825487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1840136489/10000000000 : ℝ)^2129 ≤ (5383259125921/50000000000000 : ℝ)^1617 := by
    have hnat : (1840136489 : ℕ)^2129*50000000000000^1617 ≤ 5383259125921^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840136489 10000000000 5383259125921 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4831674553/10000000000 : ℝ)^2129 ≤ (9594265093867/25000000000000 : ℝ)^1617 := by
    have hnat : (4831674553 : ℕ)^2129*25000000000000^1617 ≤ 9594265093867^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4831674553 10000000000 9594265093867 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2991825487/5000000000 : ℝ)^2129 ≤ (50856421350197/100000000000000 : ℝ)^1617 := by
    have hnat : (2991825487 : ℕ)^2129*100000000000000^1617 ≤ 50856421350197^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991825487 5000000000 50856421350197 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1840136489/10000000000 : ℝ), (4831674553/10000000000 : ℝ), (2991825487/5000000000 : ℝ)] ![(5383259125921/50000000000000 : ℝ), (9594265093867/25000000000000 : ℝ), (50856421350197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1840136489/10000000000 : ℝ)|^2129 ≤ (5383259125921/50000000000000 : ℝ)^1617
        have hw : |(-1840136489/10000000000 : ℝ)|=(1840136489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4831674553/10000000000 : ℝ)|^2129 ≤ (9594265093867/25000000000000 : ℝ)^1617
        have hw : |(4831674553/10000000000 : ℝ)|=(4831674553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2991825487/5000000000 : ℝ)|^2129 ≤ (50856421350197/100000000000000 : ℝ)^1617
        have hw : |(2991825487/5000000000 : ℝ)|=(2991825487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s0_5 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2587848861/5000000000 : ℝ)*x 0 + (-1345411649/10000000000 : ℝ)*x 1 + (2991826817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587848861/5000000000 : ℝ)^2129 ≤ (42014696913779/100000000000000 : ℝ)^1617 := by
    have hnat : (2587848861 : ℕ)^2129*100000000000000^1617 ≤ 42014696913779^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587848861 5000000000 42014696913779 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1345411649/10000000000 : ℝ)^2129 ≤ (3564425975037/50000000000000 : ℝ)^1617 := by
    have hnat : (1345411649 : ℕ)^2129*50000000000000^1617 ≤ 3564425975037^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345411649 10000000000 3564425975037 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2991826817/5000000000 : ℝ)^2129 ≤ (25428225558317/50000000000000 : ℝ)^1617 := by
    have hnat : (2991826817 : ℕ)^2129*50000000000000^1617 ≤ 25428225558317^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991826817 5000000000 25428225558317 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587848861/5000000000 : ℝ), (-1345411649/10000000000 : ℝ), (2991826817/5000000000 : ℝ)] ![(42014696913779/100000000000000 : ℝ), (3564425975037/50000000000000 : ℝ), (25428225558317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587848861/5000000000 : ℝ)|^2129 ≤ (42014696913779/100000000000000 : ℝ)^1617
        have hw : |(2587848861/5000000000 : ℝ)|=(2587848861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1345411649/10000000000 : ℝ)|^2129 ≤ (3564425975037/50000000000000 : ℝ)^1617
        have hw : |(-1345411649/10000000000 : ℝ)|=(1345411649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2991826817/5000000000 : ℝ)|^2129 ≤ (25428225558317/50000000000000 : ℝ)^1617
        have hw : |(2991826817/5000000000 : ℝ)|=(2991826817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s0_6 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5175699039/10000000000 : ℝ)*x 0 + (5983651329/10000000000 : ℝ)*x 1 + (-1345413329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175699039/10000000000 : ℝ)^2129 ≤ (1680588439597/4000000000000 : ℝ)^1617 := by
    have hnat : (5175699039 : ℕ)^2129*4000000000000^1617 ≤ 1680588439597^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175699039 10000000000 1680588439597 4000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5983651329/10000000000 : ℝ)^2129 ≤ (10171285064557/20000000000000 : ℝ)^1617 := by
    have hnat : (5983651329 : ℕ)^2129*20000000000000^1617 ≤ 10171285064557^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5983651329 10000000000 10171285064557 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1345413329/10000000000 : ℝ)^2129 ≤ (7128863670393/100000000000000 : ℝ)^1617 := by
    have hnat : (1345413329 : ℕ)^2129*100000000000000^1617 ≤ 7128863670393^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345413329 10000000000 7128863670393 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175699039/10000000000 : ℝ), (5983651329/10000000000 : ℝ), (-1345413329/10000000000 : ℝ)] ![(1680588439597/4000000000000 : ℝ), (10171285064557/20000000000000 : ℝ), (7128863670393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175699039/10000000000 : ℝ)|^2129 ≤ (1680588439597/4000000000000 : ℝ)^1617
        have hw : |(5175699039/10000000000 : ℝ)|=(5175699039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5983651329/10000000000 : ℝ)|^2129 ≤ (10171285064557/20000000000000 : ℝ)^1617
        have hw : |(5983651329/10000000000 : ℝ)|=(5983651329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1345413329/10000000000 : ℝ)|^2129 ≤ (7128863670393/100000000000000 : ℝ)^1617
        have hw : |(-1345413329/10000000000 : ℝ)|=(1345413329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s0_7 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4195078529/10000000000 : ℝ)*x 0 + (173405979/312500000 : ℝ)*x 1 + (793990479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195078529/10000000000 : ℝ)^2129 ≤ (31862960396437/100000000000000 : ℝ)^1617 := by
    have hnat : (4195078529 : ℕ)^2129*100000000000000^1617 ≤ 31862960396437^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195078529 10000000000 31862960396437 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173405979/312500000 : ℝ)^2129 ≤ (46049303937973/100000000000000 : ℝ)^1617 := by
    have hnat : (173405979 : ℕ)^2129*100000000000000^1617 ≤ 46049303937973^1617*312500000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173405979 312500000 46049303937973 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793990479/2500000000 : ℝ)^2129 ≤ (22087735652727/100000000000000 : ℝ)^1617 := by
    have hnat : (793990479 : ℕ)^2129*100000000000000^1617 ≤ 22087735652727^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793990479 2500000000 22087735652727 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195078529/10000000000 : ℝ), (173405979/312500000 : ℝ), (793990479/2500000000 : ℝ)] ![(31862960396437/100000000000000 : ℝ), (46049303937973/100000000000000 : ℝ), (22087735652727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195078529/10000000000 : ℝ)|^2129 ≤ (31862960396437/100000000000000 : ℝ)^1617
        have hw : |(4195078529/10000000000 : ℝ)|=(4195078529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173405979/312500000 : ℝ)|^2129 ≤ (46049303937973/100000000000000 : ℝ)^1617
        have hw : |(173405979/312500000 : ℝ)|=(173405979/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(793990479/2500000000 : ℝ)|^2129 ≤ (22087735652727/100000000000000 : ℝ)^1617
        have hw : |(793990479/2500000000 : ℝ)|=(793990479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1079/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27191/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4257/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4257 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4257*1^1024 ≤ 0^1024*1^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4257/1024 : ℝ) ≤ (138533001221354799/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4257 ≤ (138533001221354799/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4257*6250000000000000000^1024 ≤ 138533001221354799^1024*5^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 138533001221354799 6250000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (138533001221354799/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4257 := by
      have hnat : (1 : ℕ)^1024*1^4257 ≤ 1^4257*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6388533001221354799/6250000000000000000 : ℝ) ≤ (10052874455131041/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (6388533001221354799/6250000000000000000 : ℝ)^1024 ≤ (10052874455131041/10000000000000000 : ℝ)^4257 := by
      have hnat : (6388533001221354799 : ℕ)^1024*10000000000000000^4257 ≤ 10052874455131041^4257*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6388533001221354799 6250000000000000000 10052874455131041 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10052874455131041/10000000000000000 : ℝ)) (X := (6388533001221354799/6250000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3263533001221354799/3125000000000000000 : ℝ) ≤ (5052874455131041/5000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (3263533001221354799/3125000000000000000 : ℝ)^1024 ≤ (5052874455131041/5000000000000000 : ℝ)^4257 := by
      have hnat : (3263533001221354799 : ℕ)^1024*5000000000000000^4257 ≤ 5052874455131041^4257*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3263533001221354799 3125000000000000000 5052874455131041 5000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5052874455131041/5000000000000000 : ℝ)) (X := (3263533001221354799/3125000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(52874455131041/4000000000000000 : ℝ)*(0 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(52874455131041/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(138533001221354799/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(52874455131041/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (1 : ℝ)+(52874455131041/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10052874455131041/10000000000000000 : ℝ) by norm_num, show 1+(138533001221354799/6250000000000000000 : ℝ)+(0 : ℝ)=(6388533001221354799/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(138533001221354799/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(52874455131041/4000000000000000 : ℝ)*(2/5 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(52874455131041/4000000000000000 : ℝ)*(2/5 : ℝ)=(5052874455131041/5000000000000000 : ℝ) by norm_num, show 1+2*(138533001221354799/6250000000000000000 : ℝ)=(3263533001221354799/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(52874455131041/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52874455131041/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(52874455131041/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52874455131041/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(52874455131041/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (52874455131041/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-14683569/80000000 : ℝ)*X 0 0+(3008068973/5000000000 : ℝ)*X 0 1+(4800303297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1101349033/2000000000 : ℝ)*X 1 0+(-2528762063/10000000000 : ℝ)*X 1 1+(4800303269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((275337257/500000000 : ℝ)*X 2 0+(1200075827/2500000000 : ℝ)*X 2 1+(-1264381023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((20927053/50000000 : ℝ)*X 0 0+(388631013/1250000000 : ℝ)*X 0 1+(2806803291/5000000000 : ℝ)*X 0 2+(20927053/50000000 : ℝ)*X 1 0+(388631013/1250000000 : ℝ)*X 1 1+(2806803291/5000000000 : ℝ)*X 1 2+(20927053/50000000 : ℝ)*X 2 0+(388631013/1250000000 : ℝ)*X 2 1+(2806803291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1840136489/10000000000 : ℝ)*X 0 0+(4831674553/10000000000 : ℝ)*X 0 1+(2991825487/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587848861/5000000000 : ℝ)*X 1 0+(-1345411649/10000000000 : ℝ)*X 1 1+(2991826817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175699039/10000000000 : ℝ)*X 2 0+(5983651329/10000000000 : ℝ)*X 2 1+(-1345413329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4195078529/10000000000 : ℝ)*X 0 0+(173405979/312500000 : ℝ)*X 0 1+(793990479/2500000000 : ℝ)*X 0 2+(4195078529/10000000000 : ℝ)*X 1 0+(173405979/312500000 : ℝ)*X 1 1+(793990479/2500000000 : ℝ)*X 1 2+(4195078529/10000000000 : ℝ)*X 2 0+(173405979/312500000 : ℝ)*X 2 1+(793990479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23551505177551769267829/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47936117/100000000000000 : ℝ)*(base1) + (918579613/100000000000000 : ℝ)*(base19) + (114355703/12500000000000 : ℝ)*(base23) + (13202293/12500000000000 : ℝ)*(upper3) + (108485207/100000000000000 : ℝ)*(upper5) + (19090011931091/3125000000000 : ℝ)*(major0) + (19090011931091/3125000000000 : ℝ)*(major1) + (19090011931091/3125000000000 : ℝ)*(major2) + (411241512123789/50000000000000 : ℝ)*(sp0) + (411242493783859/50000000000000 : ℝ)*(sp1) + (822484991301707/100000000000000 : ℝ)*(sp2) + (3194186366551/800000000000 : ℝ)*(sp3) + (292983587/10000000000000 : ℝ)*(sp4) + (1388079469/100000000000000 : ℝ)*(sp7) + (19963736591723/5000000000000 : ℝ)*(f.failure) + (822485906147331/100000000000000 : ℝ)*(f.sum) + (9090510535519/6250000000000000000000000000 : ℝ)*base66 + (43466367029269/12500000000000000000000000000 : ℝ)*base68 + (97924131654269/12500000000000000000000000000 : ℝ)*base70 + (94807127541769/12500000000000000000000000000 : ℝ)*base72 + (17308082108231/6250000000000000000000000000 : ℝ)*base73 + (26311232854269/12500000000000000000000000000 : ℝ)*base76 + (108424258916769/12500000000000000000000000000 : ℝ)*base78 + (10431934745731/12500000000000000000000000000 : ℝ)*base79 + (9745666229269/6250000000000000000000000000 : ℝ)*base82 + (378581/250000000000000000000 : ℝ)*base90 + (378581/250000000000000000000 : ℝ)*base92 + (378581/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (385156057092926369194557/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46783349/10000000000000 : ℝ)*(base1) + (553407207/100000000000000 : ℝ)*(base19) + (713132341/100000000000000 : ℝ)*(base23) + (452959/800000000000 : ℝ)*(upper3) + (322369350856159/50000000000000 : ℝ)*(major0) + (322369350856159/50000000000000 : ℝ)*(major1) + (322369350856159/50000000000000 : ℝ)*(major2) + (492752191/50000000000000 : ℝ)*(sp1) + (29262067/100000000000000 : ℝ)*(sp2) + (864122851/100000000000000 : ℝ)*(sp3) + (173614605888819/20000000000000 : ℝ)*(sp4) + (173614204539803/20000000000000 : ℝ)*(sp5) + (217017954804049/25000000000000 : ℝ)*(sp6) + (421403381472333/100000000000000 : ℝ)*(sp7) + (210702356714337/50000000000000 : ℝ)*(f.failure) + (173614512322121/20000000000000 : ℝ)*(f.sum) + (233213743268481/100000000000000000000000000000 : ℝ)*base66 + (559609565668481/200000000000000000000000000000 : ℝ)*base68 + (118389118931519/200000000000000000000000000000 : ℝ)*base69 + (43540763531519/200000000000000000000000000000 : ℝ)*base71 + (296362805768481/100000000000000000000000000000 : ℝ)*base74 + (1239169771331519/200000000000000000000000000000 : ℝ)*base75 + (100124130731519/200000000000000000000000000000 : ℝ)*base77 + (959364917331519/200000000000000000000000000000 : ℝ)*base79 + (287145087468481/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7721761/2500000000000000000000 : ℝ)*base89 + (7721761/2500000000000000000000 : ℝ)*base91 + (7721761/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1298_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27191/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1298_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1298_s1_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2026623379/10000000000 : ℝ)*x 0 + (5662446883/10000000000 : ℝ)*x 1 + (5031597393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026623379/10000000000 : ℝ)^2129 ≤ (1528208563267/12500000000000 : ℝ)^1617 := by
    have hnat : (2026623379 : ℕ)^2129*12500000000000^1617 ≤ 1528208563267^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026623379 10000000000 1528208563267 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5662446883/10000000000 : ℝ)^2129 ≤ (47292951998013/100000000000000 : ℝ)^1617 := by
    have hnat : (5662446883 : ℕ)^2129*100000000000000^1617 ≤ 47292951998013^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662446883 10000000000 47292951998013 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5031597393/10000000000 : ℝ)^2129 ≤ (10120344871103/25000000000000 : ℝ)^1617 := by
    have hnat : (5031597393 : ℕ)^2129*25000000000000^1617 ≤ 10120344871103^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031597393 10000000000 10120344871103 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2026623379/10000000000 : ℝ), (5662446883/10000000000 : ℝ), (5031597393/10000000000 : ℝ)] ![(1528208563267/12500000000000 : ℝ), (47292951998013/100000000000000 : ℝ), (10120344871103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2026623379/10000000000 : ℝ)|^2129 ≤ (1528208563267/12500000000000 : ℝ)^1617
        have hw : |(-2026623379/10000000000 : ℝ)|=(2026623379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5662446883/10000000000 : ℝ)|^2129 ≤ (47292951998013/100000000000000 : ℝ)^1617
        have hw : |(5662446883/10000000000 : ℝ)|=(5662446883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5031597393/10000000000 : ℝ)|^2129 ≤ (10120344871103/25000000000000 : ℝ)^1617
        have hw : |(5031597393/10000000000 : ℝ)|=(5031597393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s1_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2705173723/5000000000 : ℝ)*x 0 + (-1182282283/5000000000 : ℝ)*x 1 + (1006319509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705173723/5000000000 : ℝ)^2129 ≤ (44540460647993/100000000000000 : ℝ)^1617 := by
    have hnat : (2705173723 : ℕ)^2129*100000000000000^1617 ≤ 44540460647993^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705173723 5000000000 44540460647993 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1182282283/5000000000 : ℝ)^2129 ≤ (374453956043/2500000000000 : ℝ)^1617 := by
    have hnat : (1182282283 : ℕ)^2129*2500000000000^1617 ≤ 374453956043^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182282283 5000000000 374453956043 2500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006319509/2000000000 : ℝ)^2129 ≤ (20240690547267/50000000000000 : ℝ)^1617 := by
    have hnat : (1006319509 : ℕ)^2129*50000000000000^1617 ≤ 20240690547267^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006319509 2000000000 20240690547267 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705173723/5000000000 : ℝ), (-1182282283/5000000000 : ℝ), (1006319509/2000000000 : ℝ)] ![(44540460647993/100000000000000 : ℝ), (374453956043/2500000000000 : ℝ), (20240690547267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705173723/5000000000 : ℝ)|^2129 ≤ (44540460647993/100000000000000 : ℝ)^1617
        have hw : |(2705173723/5000000000 : ℝ)|=(2705173723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1182282283/5000000000 : ℝ)|^2129 ≤ (374453956043/2500000000000 : ℝ)^1617
        have hw : |(-1182282283/5000000000 : ℝ)|=(1182282283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006319509/2000000000 : ℝ)|^2129 ≤ (20240690547267/50000000000000 : ℝ)^1617
        have hw : |(1006319509/2000000000 : ℝ)|=(1006319509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s1_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5410347533/10000000000 : ℝ)*x 0 + (2515798659/5000000000 : ℝ)*x 1 + (-1182282371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410347533/10000000000 : ℝ)^2129 ≤ (44540461590999/100000000000000 : ℝ)^1617 := by
    have hnat : (5410347533 : ℕ)^2129*100000000000000^1617 ≤ 44540461590999^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410347533 10000000000 44540461590999 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2515798659/5000000000 : ℝ)^2129 ≤ (8096275737989/20000000000000 : ℝ)^1617 := by
    have hnat : (2515798659 : ℕ)^2129*20000000000000^1617 ≤ 8096275737989^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515798659 5000000000 8096275737989 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1182282371/5000000000 : ℝ)^2129 ≤ (14978159709583/100000000000000 : ℝ)^1617 := by
    have hnat : (1182282371 : ℕ)^2129*100000000000000^1617 ≤ 14978159709583^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182282371 5000000000 14978159709583 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410347533/10000000000 : ℝ), (2515798659/5000000000 : ℝ), (-1182282371/5000000000 : ℝ)] ![(44540461590999/100000000000000 : ℝ), (8096275737989/20000000000000 : ℝ), (14978159709583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410347533/10000000000 : ℝ)|^2129 ≤ (44540461590999/100000000000000 : ℝ)^1617
        have hw : |(5410347533/10000000000 : ℝ)|=(5410347533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2515798659/5000000000 : ℝ)|^2129 ≤ (8096275737989/20000000000000 : ℝ)^1617
        have hw : |(2515798659/5000000000 : ℝ)|=(2515798659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1182282371/5000000000 : ℝ)|^2129 ≤ (14978159709583/100000000000000 : ℝ)^1617
        have hw : |(-1182282371/5000000000 : ℝ)|=(1182282371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s1_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (537511249/1250000000 : ℝ)*x 0 + (924178457/2500000000 : ℝ)*x 1 + (1249057963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537511249/1250000000 : ℝ)^2129 ≤ (32917241501843/100000000000000 : ℝ)^1617 := by
    have hnat : (537511249 : ℕ)^2129*100000000000000^1617 ≤ 32917241501843^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537511249 1250000000 32917241501843 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924178457/2500000000 : ℝ)^2129 ≤ (3371948158067/12500000000000 : ℝ)^1617 := by
    have hnat : (924178457 : ℕ)^2129*12500000000000^1617 ≤ 3371948158067^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924178457 2500000000 3371948158067 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249057963/2500000000 : ℝ)^2129 ≤ (40107173220487/100000000000000 : ℝ)^1617 := by
    have hnat : (1249057963 : ℕ)^2129*100000000000000^1617 ≤ 40107173220487^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249057963 2500000000 40107173220487 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537511249/1250000000 : ℝ), (924178457/2500000000 : ℝ), (1249057963/2500000000 : ℝ)] ![(32917241501843/100000000000000 : ℝ), (3371948158067/12500000000000 : ℝ), (40107173220487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537511249/1250000000 : ℝ)|^2129 ≤ (32917241501843/100000000000000 : ℝ)^1617
        have hw : |(537511249/1250000000 : ℝ)|=(537511249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(924178457/2500000000 : ℝ)|^2129 ≤ (3371948158067/12500000000000 : ℝ)^1617
        have hw : |(924178457/2500000000 : ℝ)|=(924178457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1249057963/2500000000 : ℝ)|^2129 ≤ (40107173220487/100000000000000 : ℝ)^1617
        have hw : |(1249057963/2500000000 : ℝ)|=(1249057963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s1_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-506811871/2500000000 : ℝ)*x 0 + (2519892351/5000000000 : ℝ)*x 1 + (5654105349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506811871/2500000000 : ℝ)^2129 ≤ (12230625792907/100000000000000 : ℝ)^1617 := by
    have hnat : (506811871 : ℕ)^2129*100000000000000^1617 ≤ 12230625792907^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506811871 2500000000 12230625792907 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2519892351/5000000000 : ℝ)^2129 ≤ (20284064600699/50000000000000 : ℝ)^1617 := by
    have hnat : (2519892351 : ℕ)^2129*50000000000000^1617 ≤ 20284064600699^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519892351 5000000000 20284064600699 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5654105349/10000000000 : ℝ)^2129 ≤ (9440248998421/20000000000000 : ℝ)^1617 := by
    have hnat : (5654105349 : ℕ)^2129*20000000000000^1617 ≤ 9440248998421^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654105349 10000000000 9440248998421 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-506811871/2500000000 : ℝ), (2519892351/5000000000 : ℝ), (5654105349/10000000000 : ℝ)] ![(12230625792907/100000000000000 : ℝ), (20284064600699/50000000000000 : ℝ), (9440248998421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-506811871/2500000000 : ℝ)|^2129 ≤ (12230625792907/100000000000000 : ℝ)^1617
        have hw : |(-506811871/2500000000 : ℝ)|=(506811871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2519892351/5000000000 : ℝ)|^2129 ≤ (20284064600699/50000000000000 : ℝ)^1617
        have hw : |(2519892351/5000000000 : ℝ)|=(2519892351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5654105349/10000000000 : ℝ)|^2129 ≤ (9440248998421/20000000000000 : ℝ)^1617
        have hw : |(5654105349/10000000000 : ℝ)|=(5654105349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s1_5 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5247270627/10000000000 : ℝ)*x 0 + (-217757021/1250000000 : ℝ)*x 1 + (5654106079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247270627/10000000000 : ℝ)^2129 ≤ (42781340341771/100000000000000 : ℝ)^1617 := by
    have hnat : (5247270627 : ℕ)^2129*100000000000000^1617 ≤ 42781340341771^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247270627 10000000000 42781340341771 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217757021/1250000000 : ℝ)^2129 ≤ (78260989269/781250000000 : ℝ)^1617 := by
    have hnat : (217757021 : ℕ)^2129*781250000000^1617 ≤ 78260989269^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217757021 1250000000 78260989269 781250000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5654106079/10000000000 : ℝ)^2129 ≤ (11800313253967/25000000000000 : ℝ)^1617 := by
    have hnat : (5654106079 : ℕ)^2129*25000000000000^1617 ≤ 11800313253967^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654106079 10000000000 11800313253967 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247270627/10000000000 : ℝ), (-217757021/1250000000 : ℝ), (5654106079/10000000000 : ℝ)] ![(42781340341771/100000000000000 : ℝ), (78260989269/781250000000 : ℝ), (11800313253967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247270627/10000000000 : ℝ)|^2129 ≤ (42781340341771/100000000000000 : ℝ)^1617
        have hw : |(5247270627/10000000000 : ℝ)|=(5247270627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217757021/1250000000 : ℝ)|^2129 ≤ (78260989269/781250000000 : ℝ)^1617
        have hw : |(-217757021/1250000000 : ℝ)|=(217757021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5654106079/10000000000 : ℝ)|^2129 ≤ (11800313253967/25000000000000 : ℝ)^1617
        have hw : |(5654106079/10000000000 : ℝ)|=(5654106079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s1_6 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5247270541/10000000000 : ℝ)*x 0 + (1413526417/2500000000 : ℝ)*x 1 + (-1742056887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247270541/10000000000 : ℝ)^2129 ≤ (21390669709297/50000000000000 : ℝ)^1617 := by
    have hnat : (5247270541 : ℕ)^2129*50000000000000^1617 ≤ 21390669709297^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247270541 10000000000 21390669709297 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1413526417/2500000000 : ℝ)^2129 ≤ (2360062424919/5000000000000 : ℝ)^1617 := by
    have hnat : (1413526417 : ℕ)^2129*5000000000000^1617 ≤ 2360062424919^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413526417 2500000000 2360062424919 5000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1742056887/10000000000 : ℝ)^2129 ≤ (10017412070051/100000000000000 : ℝ)^1617 := by
    have hnat : (1742056887 : ℕ)^2129*100000000000000^1617 ≤ 10017412070051^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742056887 10000000000 10017412070051 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247270541/10000000000 : ℝ), (1413526417/2500000000 : ℝ), (-1742056887/10000000000 : ℝ)] ![(21390669709297/50000000000000 : ℝ), (2360062424919/5000000000000 : ℝ), (10017412070051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247270541/10000000000 : ℝ)|^2129 ≤ (21390669709297/50000000000000 : ℝ)^1617
        have hw : |(5247270541/10000000000 : ℝ)|=(5247270541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1413526417/2500000000 : ℝ)|^2129 ≤ (2360062424919/5000000000000 : ℝ)^1617
        have hw : |(1413526417/2500000000 : ℝ)|=(1413526417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1742056887/10000000000 : ℝ)|^2129 ≤ (10017412070051/100000000000000 : ℝ)^1617
        have hw : |(-1742056887/10000000000 : ℝ)|=(1742056887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s1_7 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2150687401/5000000000 : ℝ)*x 0 + (4979367/10000000 : ℝ)*x 1 + (3713896091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150687401/5000000000 : ℝ)^2129 ≤ (32930191537987/100000000000000 : ℝ)^1617 := by
    have hnat : (2150687401 : ℕ)^2129*100000000000000^1617 ≤ 32930191537987^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150687401 5000000000 32930191537987 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4979367/10000000 : ℝ)^2129 ≤ (39929019327817/100000000000000 : ℝ)^1617 := by
    have hnat : (4979367 : ℕ)^2129*100000000000000^1617 ≤ 39929019327817^1617*10000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979367 10000000 39929019327817 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3713896091/10000000000 : ℝ)^2129 ≤ (27140789117583/100000000000000 : ℝ)^1617 := by
    have hnat : (3713896091 : ℕ)^2129*100000000000000^1617 ≤ 27140789117583^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713896091 10000000000 27140789117583 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150687401/5000000000 : ℝ), (4979367/10000000 : ℝ), (3713896091/10000000000 : ℝ)] ![(32930191537987/100000000000000 : ℝ), (39929019327817/100000000000000 : ℝ), (27140789117583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150687401/5000000000 : ℝ)|^2129 ≤ (32930191537987/100000000000000 : ℝ)^1617
        have hw : |(2150687401/5000000000 : ℝ)|=(2150687401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4979367/10000000 : ℝ)|^2129 ≤ (39929019327817/100000000000000 : ℝ)^1617
        have hw : |(4979367/10000000 : ℝ)|=(4979367/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3713896091/10000000000 : ℝ)|^2129 ≤ (27140789117583/100000000000000 : ℝ)^1617
        have hw : |(3713896091/10000000000 : ℝ)|=(3713896091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27191/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1617/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9901/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27191/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27191/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27191/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27191/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27191/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27191/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1079/100000 : ℝ) ^ (4257/1024 : ℝ) ≤ (133000874839/20000000000000000000 : ℝ) := by
    have hpowers : (1079/100000 : ℝ)^4257 ≤ (133000874839/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1079 : ℕ)^4257*20000000000000000000^1024 ≤ 133000874839^1024*100000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1079 100000 133000874839 20000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1079/100000 : ℝ)) (X := (133000874839/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27191/100000 : ℝ) ^ (4257/1024 : ℝ) ≤ (222713908206491617/50000000000000000000 : ℝ) := by
    have hpowers : (27191/100000 : ℝ)^4257 ≤ (222713908206491617/50000000000000000000 : ℝ)^1024 := by
      have hnat : (27191 : ℕ)^4257*50000000000000000000^1024 ≤ 222713908206491617^1024*100000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27191 100000 222713908206491617 50000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27191/100000 : ℝ)) (X := (222713908206491617/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000133000874839/10000000000000000000 : ℝ) ≤ (5000000015996347/5000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (10000000133000874839/10000000000000000000 : ℝ)^1024 ≤ (5000000015996347/5000000000000000 : ℝ)^4257 := by
      have hnat : (10000000133000874839 : ℕ)^1024*5000000000000000^4257 ≤ 5000000015996347^4257*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000133000874839 10000000000000000000 5000000015996347 5000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000015996347/5000000000000000 : ℝ)) (X := (10000000133000874839/10000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100445428481417357429/100000000000000000000 : ℝ) ≤ (2502674120791209/2500000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (100445428481417357429/100000000000000000000 : ℝ)^1024 ≤ (2502674120791209/2500000000000000 : ℝ)^4257 := by
      have hnat : (100445428481417357429 : ℕ)^1024*2500000000000000^4257 ≤ 2502674120791209^4257*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100445428481417357429 100000000000000000000 2502674120791209 2500000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502674120791209/2500000000000000 : ℝ)) (X := (100445428481417357429/100000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25222713908206491617/25000000000000000000 : ℝ) ≤ (5010696467168489/5000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (25222713908206491617/25000000000000000000 : ℝ)^1024 ≤ (5010696467168489/5000000000000000 : ℝ)^4257 := by
      have hnat : (25222713908206491617 : ℕ)^1024*5000000000000000^4257 ≤ 5010696467168489^4257*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25222713908206491617 25000000000000000000 5010696467168489 5000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010696467168489/5000000000000000 : ℝ)) (X := (25222713908206491617/25000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(133000874839/20000000000000000000 : ℝ) ≤ ((3839660557261231519/3840000000000000000 : ℝ)+2*(314601505063/76800000000000 : ℝ)*(1079/100000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (3839660557261231519/3840000000000000000 : ℝ)+2*(314601505063/76800000000000 : ℝ)*(1079/100000 : ℝ)=(5000000015996347/5000000000000000 : ℝ) by norm_num, show 1+2*(133000874839/20000000000000000000 : ℝ)=(10000000133000874839/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(222713908206491617/50000000000000000000 : ℝ)+(133000874839/20000000000000000000 : ℝ) ≤ ((3839660557261231519/3840000000000000000 : ℝ)+(314601505063/76800000000000 : ℝ)*((27191/100000 : ℝ)+(1079/100000 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (3839660557261231519/3840000000000000000 : ℝ)+(314601505063/76800000000000 : ℝ)*((27191/100000 : ℝ)+(1079/100000 : ℝ))=(2502674120791209/2500000000000000 : ℝ) by norm_num, show 1+(222713908206491617/50000000000000000000 : ℝ)+(133000874839/20000000000000000000 : ℝ)=(100445428481417357429/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(222713908206491617/50000000000000000000 : ℝ) ≤ ((3839660557261231519/3840000000000000000 : ℝ)+2*(314601505063/76800000000000 : ℝ)*(27191/100000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (3839660557261231519/3840000000000000000 : ℝ)+2*(314601505063/76800000000000 : ℝ)*(27191/100000 : ℝ)=(5010696467168489/5000000000000000 : ℝ) by norm_num, show 1+2*(222713908206491617/50000000000000000000 : ℝ)=(25222713908206491617/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3839660557261231519/3840000000000000000 : ℝ)*(X 1 0+X 2 0)+(314601505063/76800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (1079/100000 : ℝ)) (hi := (27191/100000 : ℝ)) (c := (3839660557261231519/3840000000000000000 : ℝ)) (alpha := (314601505063/76800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3839660557261231519/3840000000000000000 : ℝ)*(X 0 1+X 2 1)+(314601505063/76800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (1079/100000 : ℝ)) (hi := (27191/100000 : ℝ)) (c := (3839660557261231519/3840000000000000000 : ℝ)) (alpha := (314601505063/76800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3839660557261231519/3840000000000000000 : ℝ)*(X 0 2+X 1 2)+(314601505063/76800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (1079/100000 : ℝ)) (hi := (27191/100000 : ℝ)) (c := (3839660557261231519/3840000000000000000 : ℝ)) (alpha := (314601505063/76800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2026623379/10000000000 : ℝ)*X 0 0+(5662446883/10000000000 : ℝ)*X 0 1+(5031597393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2705173723/5000000000 : ℝ)*X 1 0+(-1182282283/5000000000 : ℝ)*X 1 1+(1006319509/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5410347533/10000000000 : ℝ)*X 2 0+(2515798659/5000000000 : ℝ)*X 2 1+(-1182282371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((537511249/1250000000 : ℝ)*X 0 0+(924178457/2500000000 : ℝ)*X 0 1+(1249057963/2500000000 : ℝ)*X 0 2+(537511249/1250000000 : ℝ)*X 1 0+(924178457/2500000000 : ℝ)*X 1 1+(1249057963/2500000000 : ℝ)*X 1 2+(537511249/1250000000 : ℝ)*X 2 0+(924178457/2500000000 : ℝ)*X 2 1+(1249057963/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-506811871/2500000000 : ℝ)*X 0 0+(2519892351/5000000000 : ℝ)*X 0 1+(5654105349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5247270627/10000000000 : ℝ)*X 1 0+(-217757021/1250000000 : ℝ)*X 1 1+(5654106079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5247270541/10000000000 : ℝ)*X 2 0+(1413526417/2500000000 : ℝ)*X 2 1+(-1742056887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2150687401/5000000000 : ℝ)*X 0 0+(4979367/10000000 : ℝ)*X 0 1+(3713896091/10000000000 : ℝ)*X 0 2+(2150687401/5000000000 : ℝ)*X 1 0+(4979367/10000000 : ℝ)*X 1 1+(3713896091/10000000000 : ℝ)*X 1 2+(2150687401/5000000000 : ℝ)*X 2 0+(4979367/10000000 : ℝ)*X 2 1+(3713896091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121635915533081133027472607/16000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36063731/50000000000000 : ℝ)*(base1) + (57238559/4000000000000 : ℝ)*(base19) + (1456454127/100000000000000 : ℝ)*(base23) + (39689679/20000000000000 : ℝ)*(upper3) + (34095173/25000000000000 : ℝ)*(upper5) + (588676174890953/50000000000000 : ℝ)*(major0) + (588676174890953/50000000000000 : ℝ)*(major1) + (588676174890953/50000000000000 : ℝ)*(major2) + (396293149431189/25000000000000 : ℝ)*(sp0) + (1585179131722681/100000000000000 : ℝ)*(sp1) + (1585179106232529/100000000000000 : ℝ)*(sp2) + (384759865760579/50000000000000 : ℝ)*(sp3) + (4018544681/50000000000000 : ℝ)*(sp4) + (4079820373/100000000000000 : ℝ)*(sp7) + (769523883468993/100000000000000 : ℝ)*(f.failure) + (24768446291979/1562500000000 : ℝ)*(f.sum) + (1104917412961/1920000000000000000000000000 : ℝ)*base66 + (310504610277165869/64000000000000000000000000000000 : ℝ)*base67 + (354218942298834131/64000000000000000000000000000000 : ℝ)*base70 + (132239396890834131/64000000000000000000000000000000 : ℝ)*base72 + (1929093029279/1920000000000000000000000000 : ℝ)*base73 + (433838763034834131/64000000000000000000000000000000 : ℝ)*base76 + (354375603674834131/64000000000000000000000000000000 : ℝ)*base78 + (155548608922834131/64000000000000000000000000000000 : ℝ)*base80 + (12059166163681/1920000000000000000000000000 : ℝ)*base82 + (21334271/5000000000000000000000 : ℝ)*base90 + (21334271/5000000000000000000000 : ℝ)*base92 + (21334271/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (396225195522211175090052759/64000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1109939539/100000000000000 : ℝ)*(base19) + (220090601/20000000000000 : ℝ)*(base23) + (890031/3125000000000 : ℝ)*(upper2) + (39379527/20000000000000 : ℝ)*(upper3) + (129741383/100000000000000 : ℝ)*(upper5) + (1209016657077961/100000000000000 : ℝ)*(major0) + (1209016657077961/100000000000000 : ℝ)*(major1) + (1209016657077961/100000000000000 : ℝ)*(major2) + (649470103/10000000000000 : ℝ)*(sp1) + (1060282867/20000000000000 : ℝ)*(sp2) + (813906630639107/50000000000000 : ℝ)*(sp4) + (813902828318823/50000000000000 : ℝ)*(sp5) + (813903429705437/50000000000000 : ℝ)*(sp6) + (395109923255207/50000000000000 : ℝ)*(sp7) + (395109923255207/50000000000000 : ℝ)*(f.failure) + (813906630639107/50000000000000 : ℝ)*(f.sum) + (25783622679137/3840000000000000000000000000 : ℝ)*base66 + (3712517290465747/128000000000000000000000000000000 : ℝ)*base68 + (1461972201813534253/128000000000000000000000000000000 : ℝ)*base69 + (286229153706465747/128000000000000000000000000000000 : ℝ)*base72 + (20086061232737/3840000000000000000000000000 : ℝ)*base74 + (413388399530465747/128000000000000000000000000000000 : ℝ)*base76 + (145564189482465747/128000000000000000000000000000000 : ℝ)*base78 + (55947625557534253/128000000000000000000000000000000 : ℝ)*base79 + (6591116108897/3840000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11256871/2500000000000000000000 : ℝ)*base89 + (11256871/2500000000000000000000 : ℝ)*base91 + (11256871/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1298_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27191/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1617/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9901/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1298_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1298_s2_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-517688313/2500000000 : ℝ)*x 0 + (2746211259/5000000000 : ℝ)*x 1 + (1293356241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517688313/2500000000 : ℝ)^2129 ≤ (3144344715867/25000000000000 : ℝ)^1617 := by
    have hnat : (517688313 : ℕ)^2129*25000000000000^1617 ≤ 3144344715867^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517688313 2500000000 3144344715867 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746211259/5000000000 : ℝ)^2129 ≤ (45432213850189/100000000000000 : ℝ)^1617 := by
    have hnat : (2746211259 : ℕ)^2129*100000000000000^1617 ≤ 45432213850189^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746211259 5000000000 45432213850189 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293356241/2500000000 : ℝ)^2129 ≤ (41990407279773/100000000000000 : ℝ)^1617 := by
    have hnat : (1293356241 : ℕ)^2129*100000000000000^1617 ≤ 41990407279773^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293356241 2500000000 41990407279773 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517688313/2500000000 : ℝ), (2746211259/5000000000 : ℝ), (1293356241/2500000000 : ℝ)] ![(3144344715867/25000000000000 : ℝ), (45432213850189/100000000000000 : ℝ), (41990407279773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517688313/2500000000 : ℝ)|^2129 ≤ (3144344715867/25000000000000 : ℝ)^1617
        have hw : |(-517688313/2500000000 : ℝ)|=(517688313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746211259/5000000000 : ℝ)|^2129 ≤ (45432213850189/100000000000000 : ℝ)^1617
        have hw : |(2746211259/5000000000 : ℝ)|=(2746211259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293356241/2500000000 : ℝ)|^2129 ≤ (41990407279773/100000000000000 : ℝ)^1617
        have hw : |(1293356241/2500000000 : ℝ)|=(1293356241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s2_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073827271/2000000000 : ℝ)*x 0 + (-2236003217/10000000000 : ℝ)*x 1 + (5173424917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073827271/2000000000 : ℝ)^2129 ≤ (8818861420569/20000000000000 : ℝ)^1617 := by
    have hnat : (1073827271 : ℕ)^2129*20000000000000^1617 ≤ 8818861420569^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073827271 2000000000 8818861420569 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236003217/10000000000 : ℝ)^2129 ≤ (6957643055551/50000000000000 : ℝ)^1617 := by
    have hnat : (2236003217 : ℕ)^2129*50000000000000^1617 ≤ 6957643055551^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236003217 10000000000 6957643055551 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5173424917/10000000000 : ℝ)^2129 ≤ (8398081355501/20000000000000 : ℝ)^1617 := by
    have hnat : (5173424917 : ℕ)^2129*20000000000000^1617 ≤ 8398081355501^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173424917 10000000000 8398081355501 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073827271/2000000000 : ℝ), (-2236003217/10000000000 : ℝ), (5173424917/10000000000 : ℝ)] ![(8818861420569/20000000000000 : ℝ), (6957643055551/50000000000000 : ℝ), (8398081355501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073827271/2000000000 : ℝ)|^2129 ≤ (8818861420569/20000000000000 : ℝ)^1617
        have hw : |(1073827271/2000000000 : ℝ)|=(1073827271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2236003217/10000000000 : ℝ)|^2129 ≤ (6957643055551/50000000000000 : ℝ)^1617
        have hw : |(-2236003217/10000000000 : ℝ)|=(2236003217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5173424917/10000000000 : ℝ)|^2129 ≤ (8398081355501/20000000000000 : ℝ)^1617
        have hw : |(5173424917/10000000000 : ℝ)|=(5173424917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s2_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369136199/10000000000 : ℝ)*x 0 + (2586712489/5000000000 : ℝ)*x 1 + (-139750209/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369136199/10000000000 : ℝ)^2129 ≤ (44094305416027/100000000000000 : ℝ)^1617 := by
    have hnat : (5369136199 : ℕ)^2129*100000000000000^1617 ≤ 44094305416027^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369136199 10000000000 44094305416027 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586712489/5000000000 : ℝ)^2129 ≤ (5248800928673/12500000000000 : ℝ)^1617 := by
    have hnat : (2586712489 : ℕ)^2129*12500000000000^1617 ≤ 5248800928673^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586712489 5000000000 5248800928673 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139750209/625000000 : ℝ)^2129 ≤ (2783057430343/20000000000000 : ℝ)^1617 := by
    have hnat : (139750209 : ℕ)^2129*20000000000000^1617 ≤ 2783057430343^1617*625000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139750209 625000000 2783057430343 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369136199/10000000000 : ℝ), (2586712489/5000000000 : ℝ), (-139750209/625000000 : ℝ)] ![(44094305416027/100000000000000 : ℝ), (5248800928673/12500000000000 : ℝ), (2783057430343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369136199/10000000000 : ℝ)|^2129 ≤ (44094305416027/100000000000000 : ℝ)^1617
        have hw : |(5369136199/10000000000 : ℝ)|=(5369136199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586712489/5000000000 : ℝ)|^2129 ≤ (5248800928673/12500000000000 : ℝ)^1617
        have hw : |(2586712489/5000000000 : ℝ)|=(2586712489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139750209/625000000 : ℝ)|^2129 ≤ (2783057430343/20000000000000 : ℝ)^1617
        have hw : |(-139750209/625000000 : ℝ)|=(139750209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s2_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4330788501/10000000000 : ℝ)*x 0 + (1003517209/2500000000 : ℝ)*x 1 + (2335597831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330788501/10000000000 : ℝ)^2129 ≤ (1329079867827/4000000000000 : ℝ)^1617 := by
    have hnat : (4330788501 : ℕ)^2129*4000000000000^1617 ≤ 1329079867827^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330788501 10000000000 1329079867827 4000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003517209/2500000000 : ℝ)^2129 ≤ (15032651966649/50000000000000 : ℝ)^1617 := by
    have hnat : (1003517209 : ℕ)^2129*50000000000000^1617 ≤ 15032651966649^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003517209 2500000000 15032651966649 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2335597831/5000000000 : ℝ)^2129 ≤ (286778901179/781250000000 : ℝ)^1617 := by
    have hnat : (2335597831 : ℕ)^2129*781250000000^1617 ≤ 286778901179^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2335597831 5000000000 286778901179 781250000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330788501/10000000000 : ℝ), (1003517209/2500000000 : ℝ), (2335597831/5000000000 : ℝ)] ![(1329079867827/4000000000000 : ℝ), (15032651966649/50000000000000 : ℝ), (286778901179/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330788501/10000000000 : ℝ)|^2129 ≤ (1329079867827/4000000000000 : ℝ)^1617
        have hw : |(4330788501/10000000000 : ℝ)|=(4330788501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003517209/2500000000 : ℝ)|^2129 ≤ (15032651966649/50000000000000 : ℝ)^1617
        have hw : |(1003517209/2500000000 : ℝ)|=(1003517209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2335597831/5000000000 : ℝ)|^2129 ≤ (286778901179/781250000000 : ℝ)^1617
        have hw : |(2335597831/5000000000 : ℝ)|=(2335597831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s2_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2070833267/10000000000 : ℝ)*x 0 + (1293881929/2500000000 : ℝ)*x 1 + (1372575053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070833267/10000000000 : ℝ)^2129 ≤ (12578018747833/100000000000000 : ℝ)^1617 := by
    have hnat : (2070833267 : ℕ)^2129*100000000000000^1617 ≤ 12578018747833^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070833267 10000000000 12578018747833 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293881929/2500000000 : ℝ)^2129 ≤ (4201287989271/10000000000000 : ℝ)^1617 := by
    have hnat : (1293881929 : ℕ)^2129*10000000000000^1617 ≤ 4201287989271^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293881929 2500000000 4201287989271 10000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372575053/2500000000 : ℝ)^2129 ≤ (11352275336097/25000000000000 : ℝ)^1617 := by
    have hnat : (1372575053 : ℕ)^2129*25000000000000^1617 ≤ 11352275336097^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372575053 2500000000 11352275336097 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2070833267/10000000000 : ℝ), (1293881929/2500000000 : ℝ), (1372575053/2500000000 : ℝ)] ![(12578018747833/100000000000000 : ℝ), (4201287989271/10000000000000 : ℝ), (11352275336097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2070833267/10000000000 : ℝ)|^2129 ≤ (12578018747833/100000000000000 : ℝ)^1617
        have hw : |(-2070833267/10000000000 : ℝ)|=(2070833267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293881929/2500000000 : ℝ)|^2129 ≤ (4201287989271/10000000000000 : ℝ)^1617
        have hw : |(1293881929/2500000000 : ℝ)|=(1293881929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372575053/2500000000 : ℝ)|^2129 ≤ (11352275336097/25000000000000 : ℝ)^1617
        have hw : |(1372575053/2500000000 : ℝ)|=(1372575053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s2_5 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (165228749/312500000 : ℝ)*x 0 + (-38382547/200000000 : ℝ)*x 1 + (5490300337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165228749/312500000 : ℝ)^2129 ≤ (10802943318801/25000000000000 : ℝ)^1617 := by
    have hnat : (165228749 : ℕ)^2129*25000000000000^1617 ≤ 10802943318801^1617*312500000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165228749 312500000 10802943318801 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38382547/200000000 : ℝ)^2129 ≤ (11379124013547/100000000000000 : ℝ)^1617 := by
    have hnat : (38382547 : ℕ)^2129*100000000000000^1617 ≤ 11379124013547^1617*200000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38382547 200000000 11379124013547 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490300337/10000000000 : ℝ)^2129 ≤ (45409102705589/100000000000000 : ℝ)^1617 := by
    have hnat : (5490300337 : ℕ)^2129*100000000000000^1617 ≤ 45409102705589^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490300337 10000000000 45409102705589 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165228749/312500000 : ℝ), (-38382547/200000000 : ℝ), (5490300337/10000000000 : ℝ)] ![(10802943318801/25000000000000 : ℝ), (11379124013547/100000000000000 : ℝ), (45409102705589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165228749/312500000 : ℝ)|^2129 ≤ (10802943318801/25000000000000 : ℝ)^1617
        have hw : |(165228749/312500000 : ℝ)|=(165228749/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38382547/200000000 : ℝ)|^2129 ≤ (11379124013547/100000000000000 : ℝ)^1617
        have hw : |(-38382547/200000000 : ℝ)|=(38382547/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490300337/10000000000 : ℝ)|^2129 ≤ (45409102705589/100000000000000 : ℝ)^1617
        have hw : |(5490300337/10000000000 : ℝ)|=(5490300337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s2_6 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5287320121/10000000000 : ℝ)*x 0 + (274515011/500000000 : ℝ)*x 1 + (-959563651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287320121/10000000000 : ℝ)^2129 ≤ (1080294373039/2500000000000 : ℝ)^1617 := by
    have hnat : (5287320121 : ℕ)^2129*2500000000000^1617 ≤ 1080294373039^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287320121 10000000000 1080294373039 2500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274515011/500000000 : ℝ)^2129 ≤ (9081820286301/20000000000000 : ℝ)^1617 := by
    have hnat : (274515011 : ℕ)^2129*20000000000000^1617 ≤ 9081820286301^1617*500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274515011 500000000 9081820286301 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959563651/5000000000 : ℝ)^2129 ≤ (5689561819411/50000000000000 : ℝ)^1617 := by
    have hnat : (959563651 : ℕ)^2129*50000000000000^1617 ≤ 5689561819411^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959563651 5000000000 5689561819411 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287320121/10000000000 : ℝ), (274515011/500000000 : ℝ), (-959563651/5000000000 : ℝ)] ![(1080294373039/2500000000000 : ℝ), (9081820286301/20000000000000 : ℝ), (5689561819411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287320121/10000000000 : ℝ)|^2129 ≤ (1080294373039/2500000000000 : ℝ)^1617
        have hw : |(5287320121/10000000000 : ℝ)|=(5287320121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274515011/500000000 : ℝ)|^2129 ≤ (9081820286301/20000000000000 : ℝ)^1617
        have hw : |(274515011/500000000 : ℝ)|=(274515011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-959563651/5000000000 : ℝ)|^2129 ≤ (5689561819411/50000000000000 : ℝ)^1617
        have hw : |(-959563651/5000000000 : ℝ)|=(959563651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s2_7 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (216547633/500000000 : ℝ)*x 0 + (2333431139/5000000000 : ℝ)*x 1 + (4018445741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216547633/500000000 : ℝ)^2129 ≤ (6645730994521/20000000000000 : ℝ)^1617 := by
    have hnat : (216547633 : ℕ)^2129*20000000000000^1617 ≤ 6645730994521^1617*500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216547633 500000000 6645730994521 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2333431139/5000000000 : ℝ)^2129 ≤ (4582858805857/12500000000000 : ℝ)^1617 := by
    have hnat : (2333431139 : ℕ)^2129*12500000000000^1617 ≤ 4582858805857^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2333431139 5000000000 4582858805857 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018445741/10000000000 : ℝ)^2129 ≤ (15054237286853/50000000000000 : ℝ)^1617 := by
    have hnat : (4018445741 : ℕ)^2129*50000000000000^1617 ≤ 15054237286853^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018445741 10000000000 15054237286853 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216547633/500000000 : ℝ), (2333431139/5000000000 : ℝ), (4018445741/10000000000 : ℝ)] ![(6645730994521/20000000000000 : ℝ), (4582858805857/12500000000000 : ℝ), (15054237286853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216547633/500000000 : ℝ)|^2129 ≤ (6645730994521/20000000000000 : ℝ)^1617
        have hw : |(216547633/500000000 : ℝ)|=(216547633/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2333431139/5000000000 : ℝ)|^2129 ≤ (4582858805857/12500000000000 : ℝ)^1617
        have hw : |(2333431139/5000000000 : ℝ)|=(2333431139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018445741/10000000000 : ℝ)|^2129 ≤ (15054237286853/50000000000000 : ℝ)^1617
        have hw : |(4018445741/10000000000 : ℝ)|=(4018445741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9901/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1617/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2387/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1629/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9901/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1617/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9901/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1617/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9901/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1617/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9901/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1617/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9901/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1617/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9901/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1617/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1617/25000 : ℝ) ^ (4257/1024 : ℝ) ≤ (1137893199152511/100000000000000000000 : ℝ) := by
    have hpowers : (1617/25000 : ℝ)^4257 ≤ (1137893199152511/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1617 : ℕ)^4257*100000000000000000000^1024 ≤ 1137893199152511^1024*25000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1617 25000 1137893199152511 100000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1617/25000 : ℝ)) (X := (1137893199152511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9901/50000 : ℝ) ^ (4257/1024 : ℝ) ≤ (119195595351656379/100000000000000000000 : ℝ) := by
    have hpowers : (9901/50000 : ℝ)^4257 ≤ (119195595351656379/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9901 : ℕ)^4257*100000000000000000000^1024 ≤ 119195595351656379^1024*50000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9901 50000 119195595351656379 100000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9901/50000 : ℝ)) (X := (119195595351656379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001137893199152511/50000000000000000000 : ℝ) ≤ (10000054742427373/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (50001137893199152511/50000000000000000000 : ℝ)^1024 ≤ (10000054742427373/10000000000000000 : ℝ)^4257 := by
      have hnat : (50001137893199152511 : ℕ)^1024*10000000000000000^4257 ≤ 10000054742427373^4257*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001137893199152511 50000000000000000000 10000054742427373 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000054742427373/10000000000000000 : ℝ)) (X := (50001137893199152511/50000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10012033348855080889/10000000000000000000 : ℝ) ≤ (5001446620005051/5000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (10012033348855080889/10000000000000000000 : ℝ)^1024 ≤ (5001446620005051/5000000000000000 : ℝ)^4257 := by
      have hnat : (10012033348855080889 : ℕ)^1024*5000000000000000^4257 ≤ 5001446620005051^4257*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10012033348855080889 10000000000000000000 5001446620005051 5000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001446620005051/5000000000000000 : ℝ)) (X := (10012033348855080889/10000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50119195595351656379/50000000000000000000 : ℝ) ≤ (10005731737592831/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (50119195595351656379/50000000000000000000 : ℝ)^1024 ≤ (10005731737592831/10000000000000000 : ℝ)^4257 := by
      have hnat : (50119195595351656379 : ℕ)^1024*10000000000000000^4257 ≤ 10005731737592831^4257*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50119195595351656379 50000000000000000000 10005731737592831 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005731737592831/10000000000000000 : ℝ)) (X := (50119195595351656379/50000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1137893199152511/100000000000000000000 : ℝ) ≤ ((66652005565398204619/66670000000000000000 : ℝ)+2*(2838497582729/1333400000000000 : ℝ)*(1617/25000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (66652005565398204619/66670000000000000000 : ℝ)+2*(2838497582729/1333400000000000 : ℝ)*(1617/25000 : ℝ)=(10000054742427373/10000000000000000 : ℝ) by norm_num, show 1+2*(1137893199152511/100000000000000000000 : ℝ)=(50001137893199152511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(119195595351656379/100000000000000000000 : ℝ)+(1137893199152511/100000000000000000000 : ℝ) ≤ ((66652005565398204619/66670000000000000000 : ℝ)+(2838497582729/1333400000000000 : ℝ)*((9901/50000 : ℝ)+(1617/25000 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (66652005565398204619/66670000000000000000 : ℝ)+(2838497582729/1333400000000000 : ℝ)*((9901/50000 : ℝ)+(1617/25000 : ℝ))=(5001446620005051/5000000000000000 : ℝ) by norm_num, show 1+(119195595351656379/100000000000000000000 : ℝ)+(1137893199152511/100000000000000000000 : ℝ)=(10012033348855080889/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(119195595351656379/100000000000000000000 : ℝ) ≤ ((66652005565398204619/66670000000000000000 : ℝ)+2*(2838497582729/1333400000000000 : ℝ)*(9901/50000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (66652005565398204619/66670000000000000000 : ℝ)+2*(2838497582729/1333400000000000 : ℝ)*(9901/50000 : ℝ)=(10005731737592831/10000000000000000 : ℝ) by norm_num, show 1+2*(119195595351656379/100000000000000000000 : ℝ)=(50119195595351656379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66652005565398204619/66670000000000000000 : ℝ)*(X 1 0+X 2 0)+(2838497582729/1333400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (1617/25000 : ℝ)) (hi := (9901/50000 : ℝ)) (c := (66652005565398204619/66670000000000000000 : ℝ)) (alpha := (2838497582729/1333400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66652005565398204619/66670000000000000000 : ℝ)*(X 0 1+X 2 1)+(2838497582729/1333400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (1617/25000 : ℝ)) (hi := (9901/50000 : ℝ)) (c := (66652005565398204619/66670000000000000000 : ℝ)) (alpha := (2838497582729/1333400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66652005565398204619/66670000000000000000 : ℝ)*(X 0 2+X 1 2)+(2838497582729/1333400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (1617/25000 : ℝ)) (hi := (9901/50000 : ℝ)) (c := (66652005565398204619/66670000000000000000 : ℝ)) (alpha := (2838497582729/1333400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-517688313/2500000000 : ℝ)*X 0 0+(2746211259/5000000000 : ℝ)*X 0 1+(1293356241/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073827271/2000000000 : ℝ)*X 1 0+(-2236003217/10000000000 : ℝ)*X 1 1+(5173424917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369136199/10000000000 : ℝ)*X 2 0+(2586712489/5000000000 : ℝ)*X 2 1+(-139750209/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4330788501/10000000000 : ℝ)*X 0 0+(1003517209/2500000000 : ℝ)*X 0 1+(2335597831/5000000000 : ℝ)*X 0 2+(4330788501/10000000000 : ℝ)*X 1 0+(1003517209/2500000000 : ℝ)*X 1 1+(2335597831/5000000000 : ℝ)*X 1 2+(4330788501/10000000000 : ℝ)*X 2 0+(1003517209/2500000000 : ℝ)*X 2 1+(2335597831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2070833267/10000000000 : ℝ)*X 0 0+(1293881929/2500000000 : ℝ)*X 0 1+(1372575053/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165228749/312500000 : ℝ)*X 1 0+(-38382547/200000000 : ℝ)*X 1 1+(5490300337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287320121/10000000000 : ℝ)*X 2 0+(274515011/500000000 : ℝ)*X 2 1+(-959563651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216547633/500000000 : ℝ)*X 0 0+(2333431139/5000000000 : ℝ)*X 0 1+(4018445741/10000000000 : ℝ)*X 0 2+(216547633/500000000 : ℝ)*X 1 0+(2333431139/5000000000 : ℝ)*X 1 1+(4018445741/10000000000 : ℝ)*X 1 2+(216547633/500000000 : ℝ)*X 2 0+(2333431139/5000000000 : ℝ)*X 2 1+(4018445741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3313634308710859583926044657/416687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2545566461/100000000000000 : ℝ)*(base19) + (524874077/25000000000000 : ℝ)*(base23) + (95298677/50000000000000 : ℝ)*(lower2) + (674196379/100000000000000 : ℝ)*(upper3) + (270940977/100000000000000 : ℝ)*(upper5) + (291042177540599/12500000000000 : ℝ)*(major0) + (291042177540599/12500000000000 : ℝ)*(major1) + (291042177540599/12500000000000 : ℝ)*(major2) + (783710893313251/25000000000000 : ℝ)*(sp0) + (626971611966457/20000000000000 : ℝ)*(sp1) + (1567429252951219/50000000000000 : ℝ)*(sp2) + (760896483330873/50000000000000 : ℝ)*(sp3) + (17032145741/100000000000000 : ℝ)*(sp4) + (2625438949/12500000000000 : ℝ)*(sp7) + (1521813970173339/100000000000000 : ℝ)*(f.failure) + (1567430302699373/50000000000000 : ℝ)*(f.sum) + (108777715020999/33335000000000000000000000000 : ℝ)*base65 + (9666584410487876781/833375000000000000000000000000000 : ℝ)*base67 + (7045629525962376781/833375000000000000000000000000000 : ℝ)*base69 + (10182141202872001781/833375000000000000000000000000000 : ℝ)*base71 + (91032468603039/33335000000000000000000000000 : ℝ)*base73 + (4497661273887498219/833375000000000000000000000000000 : ℝ)*base76 + (3155179883205876781/833375000000000000000000000000000 : ℝ)*base77 + (3669661315126123219/833375000000000000000000000000000 : ℝ)*base80 + (2320703556051/520859375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (27346267/5000000000000000000000 : ℝ)*base89 + (27346267/5000000000000000000000 : ℝ)*base91 + (27346267/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1186659629355173534742964203/208343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (550171551/50000000000000 : ℝ)*(base19) + (139386593/10000000000000 : ℝ)*(base23) + (177963063/100000000000000 : ℝ)*(upper3) + (73624501/100000000000000 : ℝ)*(lower4) + (61595071/100000000000000 : ℝ)*(upper5) + (294944664213579/12500000000000 : ℝ)*(major0) + (294944664213579/12500000000000 : ℝ)*(major1) + (294944664213579/12500000000000 : ℝ)*(major2) + (2824215719/25000000000000 : ℝ)*(sp1) + (7662967431/50000000000000 : ℝ)*(sp2) + (3176894975690613/100000000000000 : ℝ)*(sp4) + (635376515696927/20000000000000 : ℝ)*(sp5) + (1588439127944911/50000000000000 : ℝ)*(sp6) + (385554865467649/25000000000000 : ℝ)*(sp7) + (385554865467649/25000000000000 : ℝ)*(f.failure) + (3176894975690613/100000000000000 : ℝ)*(f.sum) + (81630015529451/33335000000000000000000000000 : ℝ)*base66 + (2399313547801628599/833375000000000000000000000000000 : ℝ)*base68 + (5051557816718128599/833375000000000000000000000000000 : ℝ)*base70 + (9783371418902628599/833375000000000000000000000000000 : ℝ)*base72 + (4824469277773/16667500000000000000000000000 : ℝ)*base74 + (3515376066059746401/833375000000000000000000000000000 : ℝ)*base75 + (10534933445125128599/833375000000000000000000000000000 : ℝ)*base78 + (9459344838383628599/833375000000000000000000000000000 : ℝ)*base80 + (9615882453269/8333750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (10341697/1250000000000000000000 : ℝ)*base89 + (10341697/1250000000000000000000 : ℝ)*base91 + (10341697/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1298_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9901/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1617/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1298_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1298_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1298_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1298_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1298_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

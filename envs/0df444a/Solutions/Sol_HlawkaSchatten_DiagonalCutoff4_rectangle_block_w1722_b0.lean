-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1722_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:00:14.633034+00:00
-- url     : https://prove2.me/submissions/33120fb4-281c-4b55-aaad-02fedfb0d86e

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
theorem support_rectangle_w1722_s0_0 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-325499467/2500000000 : ℝ)*x 0 + (5674485991/10000000000 : ℝ)*x 1 + (4972482627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325499467/2500000000 : ℝ)^5399 ≤ (2019847085291/25000000000000 : ℝ)^4375 := by
    have hnat : (325499467 : ℕ)^5399*25000000000000^4375 ≤ 2019847085291^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325499467 2500000000 2019847085291 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5674485991/10000000000 : ℝ)^5399 ≤ (49697126040273/100000000000000 : ℝ)^4375 := by
    have hnat : (5674485991 : ℕ)^5399*100000000000000^4375 ≤ 49697126040273^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674485991 10000000000 49697126040273 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4972482627/10000000000 : ℝ)^5399 ≤ (21111742800561/50000000000000 : ℝ)^4375 := by
    have hnat : (4972482627 : ℕ)^5399*50000000000000^4375 ≤ 21111742800561^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4972482627 10000000000 21111742800561 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-325499467/2500000000 : ℝ), (5674485991/10000000000 : ℝ), (4972482627/10000000000 : ℝ)] ![(2019847085291/25000000000000 : ℝ), (49697126040273/100000000000000 : ℝ), (21111742800561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-325499467/2500000000 : ℝ)|^5399 ≤ (2019847085291/25000000000000 : ℝ)^4375
        have hw : |(-325499467/2500000000 : ℝ)|=(325499467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5674485991/10000000000 : ℝ)|^5399 ≤ (49697126040273/100000000000000 : ℝ)^4375
        have hw : |(5674485991/10000000000 : ℝ)|=(5674485991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4972482627/10000000000 : ℝ)|^5399 ≤ (21111742800561/50000000000000 : ℝ)^4375
        have hw : |(4972482627/10000000000 : ℝ)|=(4972482627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s0_1 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539601941/1000000000 : ℝ)*x 0 + (-1680689183/10000000000 : ℝ)*x 1 + (2486241021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539601941/1000000000 : ℝ)^5399 ≤ (23352500884517/50000000000000 : ℝ)^4375 := by
    have hnat : (539601941 : ℕ)^5399*50000000000000^4375 ≤ 23352500884517^4375*1000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539601941 1000000000 23352500884517 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1680689183/10000000000 : ℝ)^5399 ≤ (5535759374441/50000000000000 : ℝ)^4375 := by
    have hnat : (1680689183 : ℕ)^5399*50000000000000^4375 ≤ 5535759374441^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680689183 10000000000 5535759374441 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2486241021/5000000000 : ℝ)^5399 ≤ (527793493387/1250000000000 : ℝ)^4375 := by
    have hnat : (2486241021 : ℕ)^5399*1250000000000^4375 ≤ 527793493387^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486241021 5000000000 527793493387 1250000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539601941/1000000000 : ℝ), (-1680689183/10000000000 : ℝ), (2486241021/5000000000 : ℝ)] ![(23352500884517/50000000000000 : ℝ), (5535759374441/50000000000000 : ℝ), (527793493387/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539601941/1000000000 : ℝ)|^5399 ≤ (23352500884517/50000000000000 : ℝ)^4375
        have hw : |(539601941/1000000000 : ℝ)|=(539601941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1680689183/10000000000 : ℝ)|^5399 ≤ (5535759374441/50000000000000 : ℝ)^4375
        have hw : |(-1680689183/10000000000 : ℝ)|=(1680689183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2486241021/5000000000 : ℝ)|^5399 ≤ (527793493387/1250000000000 : ℝ)^4375
        have hw : |(2486241021/5000000000 : ℝ)|=(2486241021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s0_2 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396018311/10000000000 : ℝ)*x 0 + (2486241343/5000000000 : ℝ)*x 1 + (-1680689797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396018311/10000000000 : ℝ)^5399 ≤ (23352495015129/50000000000000 : ℝ)^4375 := by
    have hnat : (5396018311 : ℕ)^5399*50000000000000^4375 ≤ 23352495015129^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396018311 10000000000 23352495015129 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2486241343/5000000000 : ℝ)^5399 ≤ (21111743109689/50000000000000 : ℝ)^4375 := by
    have hnat : (2486241343 : ℕ)^5399*50000000000000^4375 ≤ 21111743109689^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486241343 5000000000 21111743109689 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1680689797/10000000000 : ℝ)^5399 ≤ (5535761870147/50000000000000 : ℝ)^4375 := by
    have hnat : (1680689797 : ℕ)^5399*50000000000000^4375 ≤ 5535761870147^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680689797 10000000000 5535761870147 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396018311/10000000000 : ℝ), (2486241343/5000000000 : ℝ), (-1680689797/10000000000 : ℝ)] ![(23352495015129/50000000000000 : ℝ), (21111743109689/50000000000000 : ℝ), (5535761870147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396018311/10000000000 : ℝ)|^5399 ≤ (23352495015129/50000000000000 : ℝ)^4375
        have hw : |(5396018311/10000000000 : ℝ)|=(5396018311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2486241343/5000000000 : ℝ)|^5399 ≤ (21111743109689/50000000000000 : ℝ)^4375
        have hw : |(2486241343/5000000000 : ℝ)|=(2486241343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1680689797/10000000000 : ℝ)|^5399 ≤ (5535761870147/50000000000000 : ℝ)^4375
        have hw : |(-1680689797/10000000000 : ℝ)|=(1680689797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s0_3 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (7870333/19531250 : ℝ)*x 0 + (153327623/500000000 : ℝ)*x 1 + (515762483/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7870333/19531250 : ℝ)^5399 ≤ (1017939794181/3125000000000 : ℝ)^4375 := by
    have hnat : (7870333 : ℕ)^5399*3125000000000^4375 ≤ 1017939794181^4375*19531250^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7870333 19531250 1017939794181 3125000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153327623/500000000 : ℝ)^5399 ≤ (726686813159/3125000000000 : ℝ)^4375 := by
    have hnat : (153327623 : ℕ)^5399*3125000000000^4375 ≤ 726686813159^4375*500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153327623 500000000 726686813159 3125000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515762483/1000000000 : ℝ)^5399 ≤ (44171948544797/100000000000000 : ℝ)^4375 := by
    have hnat : (515762483 : ℕ)^5399*100000000000000^4375 ≤ 44171948544797^4375*1000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515762483 1000000000 44171948544797 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7870333/19531250 : ℝ), (153327623/500000000 : ℝ), (515762483/1000000000 : ℝ)] ![(1017939794181/3125000000000 : ℝ), (726686813159/3125000000000 : ℝ), (44171948544797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7870333/19531250 : ℝ)|^5399 ≤ (1017939794181/3125000000000 : ℝ)^4375
        have hw : |(7870333/19531250 : ℝ)|=(7870333/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(153327623/500000000 : ℝ)|^5399 ≤ (726686813159/3125000000000 : ℝ)^4375
        have hw : |(153327623/500000000 : ℝ)|=(153327623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515762483/1000000000 : ℝ)|^5399 ≤ (44171948544797/100000000000000 : ℝ)^4375
        have hw : |(515762483/1000000000 : ℝ)|=(515762483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s0_4 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-26069837/200000000 : ℝ)*x 0 + (99790121/200000000 : ℝ)*x 1 + (5656909039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26069837/200000000 : ℝ)^5399 ≤ (4045415239083/50000000000000 : ℝ)^4375 := by
    have hnat : (26069837 : ℕ)^5399*50000000000000^4375 ≤ 4045415239083^4375*200000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26069837 200000000 4045415239083 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99790121/200000000 : ℝ)^5399 ≤ (13250607473/31250000000 : ℝ)^4375 := by
    have hnat : (99790121 : ℕ)^5399*31250000000^4375 ≤ 13250607473^4375*200000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99790121 200000000 13250607473 31250000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5656909039/10000000000 : ℝ)^5399 ≤ (1980289023543/4000000000000 : ℝ)^4375 := by
    have hnat : (5656909039 : ℕ)^5399*4000000000000^4375 ≤ 1980289023543^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5656909039 10000000000 1980289023543 4000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26069837/200000000 : ℝ), (99790121/200000000 : ℝ), (5656909039/10000000000 : ℝ)] ![(4045415239083/50000000000000 : ℝ), (13250607473/31250000000 : ℝ), (1980289023543/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26069837/200000000 : ℝ)|^5399 ≤ (4045415239083/50000000000000 : ℝ)^4375
        have hw : |(-26069837/200000000 : ℝ)|=(26069837/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(99790121/200000000 : ℝ)|^5399 ≤ (13250607473/31250000000 : ℝ)^4375
        have hw : |(99790121/200000000 : ℝ)|=(99790121/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5656909039/10000000000 : ℝ)|^5399 ≤ (1980289023543/4000000000000 : ℝ)^4375
        have hw : |(5656909039/10000000000 : ℝ)|=(5656909039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s0_5 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (325387989/625000000 : ℝ)*x 0 + (-498131271/5000000000 : ℝ)*x 1 + (707113639/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325387989/625000000 : ℝ)^5399 ≤ (22342992368693/50000000000000 : ℝ)^4375 := by
    have hnat : (325387989 : ℕ)^5399*50000000000000^4375 ≤ 22342992368693^4375*625000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325387989 625000000 22342992368693 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498131271/5000000000 : ℝ)^5399 ≤ (5806788868607/100000000000000 : ℝ)^4375 := by
    have hnat : (498131271 : ℕ)^5399*100000000000000^4375 ≤ 5806788868607^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498131271 5000000000 5806788868607 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (707113639/1250000000 : ℝ)^5399 ≤ (49507226376977/100000000000000 : ℝ)^4375 := by
    have hnat : (707113639 : ℕ)^5399*100000000000000^4375 ≤ 49507226376977^4375*1250000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707113639 1250000000 49507226376977 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(325387989/625000000 : ℝ), (-498131271/5000000000 : ℝ), (707113639/1250000000 : ℝ)] ![(22342992368693/50000000000000 : ℝ), (5806788868607/100000000000000 : ℝ), (49507226376977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(325387989/625000000 : ℝ)|^5399 ≤ (22342992368693/50000000000000 : ℝ)^4375
        have hw : |(325387989/625000000 : ℝ)|=(325387989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-498131271/5000000000 : ℝ)|^5399 ≤ (5806788868607/100000000000000 : ℝ)^4375
        have hw : |(-498131271/5000000000 : ℝ)|=(498131271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(707113639/1250000000 : ℝ)|^5399 ≤ (49507226376977/100000000000000 : ℝ)^4375
        have hw : |(707113639/1250000000 : ℝ)|=(707113639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s0_6 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520620753/1000000000 : ℝ)*x 0 + (5656909091/10000000000 : ℝ)*x 1 + (-996263007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520620753/1000000000 : ℝ)^5399 ≤ (44685981623287/100000000000000 : ℝ)^4375 := by
    have hnat : (520620753 : ℕ)^5399*100000000000000^4375 ≤ 44685981623287^4375*1000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520620753 1000000000 44685981623287 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5656909091/10000000000 : ℝ)^5399 ≤ (1547100817193/3125000000000 : ℝ)^4375 := by
    have hnat : (5656909091 : ℕ)^5399*3125000000000^4375 ≤ 1547100817193^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5656909091 10000000000 1547100817193 3125000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996263007/10000000000 : ℝ)^5399 ≤ (1161358442651/20000000000000 : ℝ)^4375 := by
    have hnat : (996263007 : ℕ)^5399*20000000000000^4375 ≤ 1161358442651^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996263007 10000000000 1161358442651 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520620753/1000000000 : ℝ), (5656909091/10000000000 : ℝ), (-996263007/10000000000 : ℝ)] ![(44685981623287/100000000000000 : ℝ), (1547100817193/3125000000000 : ℝ), (1161358442651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520620753/1000000000 : ℝ)|^5399 ≤ (44685981623287/100000000000000 : ℝ)^4375
        have hw : |(520620753/1000000000 : ℝ)|=(520620753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5656909091/10000000000 : ℝ)|^5399 ≤ (1547100817193/3125000000000 : ℝ)^4375
        have hw : |(5656909091/10000000000 : ℝ)|=(5656909091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-996263007/10000000000 : ℝ)|^5399 ≤ (1161358442651/20000000000000 : ℝ)^4375
        have hw : |(-996263007/10000000000 : ℝ)|=(996263007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s0_7 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4034058517/10000000000 : ℝ)*x 0 + (5106918001/10000000000 : ℝ)*x 1 + (3118908567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4034058517/10000000000 : ℝ)^5399 ≤ (8154612839597/25000000000000 : ℝ)^4375 := by
    have hnat : (4034058517 : ℕ)^5399*25000000000000^4375 ≤ 8154612839597^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034058517 10000000000 8154612839597 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5106918001/10000000000 : ℝ)^5399 ≤ (4363664847239/10000000000000 : ℝ)^4375 := by
    have hnat : (5106918001 : ℕ)^5399*10000000000000^4375 ≤ 4363664847239^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5106918001 10000000000 4363664847239 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3118908567/10000000000 : ℝ)^5399 ≤ (23744900151503/100000000000000 : ℝ)^4375 := by
    have hnat : (3118908567 : ℕ)^5399*100000000000000^4375 ≤ 23744900151503^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118908567 10000000000 23744900151503 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4034058517/10000000000 : ℝ), (5106918001/10000000000 : ℝ), (3118908567/10000000000 : ℝ)] ![(8154612839597/25000000000000 : ℝ), (4363664847239/10000000000000 : ℝ), (23744900151503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4034058517/10000000000 : ℝ)|^5399 ≤ (8154612839597/25000000000000 : ℝ)^4375
        have hw : |(4034058517/10000000000 : ℝ)|=(4034058517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5106918001/10000000000 : ℝ)|^5399 ≤ (4363664847239/10000000000000 : ℝ)^4375
        have hw : |(5106918001/10000000000 : ℝ)|=(5106918001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3118908567/10000000000 : ℝ)|^5399 ≤ (23744900151503/100000000000000 : ℝ)^4375
        have hw : |(3118908567/10000000000 : ℝ)|=(3118908567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1722_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6387/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10749/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5391/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5391 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5391*1^1024 ≤ 0^1024*1^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5391/1024 : ℝ) ≤ (200874941733333999/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5391 ≤ (200874941733333999/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5391*25000000000000000000^1024 ≤ 200874941733333999^1024*5^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 200874941733333999 25000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (200874941733333999/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5391 := by
      have hnat : (1 : ℕ)^1024*1^5391 ≤ 1^5391*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25200874941733333999/25000000000000000000 : ℝ) ≤ (10015212743650903/10000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (25200874941733333999/25000000000000000000 : ℝ)^1024 ≤ (10015212743650903/10000000000000000 : ℝ)^5391 := by
      have hnat : (25200874941733333999 : ℕ)^1024*10000000000000000^5391 ≤ 10015212743650903^5391*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25200874941733333999 25000000000000000000 10015212743650903 10000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015212743650903/10000000000000000 : ℝ)) (X := (25200874941733333999/25000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12700874941733333999/12500000000000000000 : ℝ) ≤ (5015212743650903/5000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (12700874941733333999/12500000000000000000 : ℝ)^1024 ≤ (5015212743650903/5000000000000000 : ℝ)^5391 := by
      have hnat : (12700874941733333999 : ℕ)^1024*5000000000000000^5391 ≤ 5015212743650903^5391*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12700874941733333999 12500000000000000000 5015212743650903 5000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015212743650903/5000000000000000 : ℝ)) (X := (12700874941733333999/12500000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15212743650903/4000000000000000 : ℝ)*(0 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15212743650903/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(200874941733333999/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15212743650903/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5391/1024 : ℝ) := by
    rw [show (1 : ℝ)+(15212743650903/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10015212743650903/10000000000000000 : ℝ) by norm_num, show 1+(200874941733333999/25000000000000000000 : ℝ)+(0 : ℝ)=(25200874941733333999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(200874941733333999/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15212743650903/4000000000000000 : ℝ)*(2/5 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15212743650903/4000000000000000 : ℝ)*(2/5 : ℝ)=(5015212743650903/5000000000000000 : ℝ) by norm_num, show 1+2*(200874941733333999/25000000000000000000 : ℝ)=(12700874941733333999/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15212743650903/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15212743650903/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15212743650903/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15212743650903/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15212743650903/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15212743650903/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-325499467/2500000000 : ℝ)*X 0 0+(5674485991/10000000000 : ℝ)*X 0 1+(4972482627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((539601941/1000000000 : ℝ)*X 1 0+(-1680689183/10000000000 : ℝ)*X 1 1+(2486241021/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5396018311/10000000000 : ℝ)*X 2 0+(2486241343/5000000000 : ℝ)*X 2 1+(-1680689797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((7870333/19531250 : ℝ)*X 0 0+(153327623/500000000 : ℝ)*X 0 1+(515762483/1000000000 : ℝ)*X 0 2+(7870333/19531250 : ℝ)*X 1 0+(153327623/500000000 : ℝ)*X 1 1+(515762483/1000000000 : ℝ)*X 1 2+(7870333/19531250 : ℝ)*X 2 0+(153327623/500000000 : ℝ)*X 2 1+(515762483/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-26069837/200000000 : ℝ)*X 0 0+(99790121/200000000 : ℝ)*X 0 1+(5656909039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((325387989/625000000 : ℝ)*X 1 0+(-498131271/5000000000 : ℝ)*X 1 1+(707113639/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((520620753/1000000000 : ℝ)*X 2 0+(5656909091/10000000000 : ℝ)*X 2 1+(-996263007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4034058517/10000000000 : ℝ)*X 0 0+(5106918001/10000000000 : ℝ)*X 0 1+(3118908567/10000000000 : ℝ)*X 0 2+(4034058517/10000000000 : ℝ)*X 1 0+(5106918001/10000000000 : ℝ)*X 1 1+(3118908567/10000000000 : ℝ)*X 1 2+(4034058517/10000000000 : ℝ)*X 2 0+(5106918001/10000000000 : ℝ)*X 2 1+(3118908567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98796863029719687793767/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54129713/25000000000000 : ℝ)*(base1) + (49661471/2500000000000 : ℝ)*(base19) + (848165709/50000000000000 : ℝ)*(base23) + (436851713/100000000000000 : ℝ)*(upper3) + (4784071/4000000000000 : ℝ)*(upper5) + (95136857695963/10000000000000 : ℝ)*(major0) + (95136857695963/10000000000000 : ℝ)*(major1) + (95136857695963/10000000000000 : ℝ)*(major2) + (356125874451161/25000000000000 : ℝ)*(sp0) + (7122533565919/500000000000 : ℝ)*(sp1) + (712253501655611/50000000000000 : ℝ)*(sp2) + (478225217601589/100000000000000 : ℝ)*(sp3) + (338647303/6250000000000 : ℝ)*(sp4) + (26908333/1000000000000 : ℝ)*(sp7) + (478228124953741/100000000000000 : ℝ)*(f.failure) + (17806358745533/1250000000000 : ℝ)*(f.sum) + (31552744635411/20000000000000000000000000000 : ℝ)*base66 + (48489209355411/40000000000000000000000000000 : ℝ)*base68 + (118485191204589/40000000000000000000000000000 : ℝ)*base69 + (68523294644589/40000000000000000000000000000 : ℝ)*base71 + (63803752395411/20000000000000000000000000000 : ℝ)*base74 + (90980838395411/40000000000000000000000000000 : ℝ)*base76 + (85325827035411/40000000000000000000000000000 : ℝ)*base78 + (59562396875411/40000000000000000000000000000 : ℝ)*base80 + (39706703684589/20000000000000000000000000000 : ℝ)*base81 + (38053481/10000000000000000000000 : ℝ)*base89 + (38053481/10000000000000000000000 : ℝ)*base91 + (38053481/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1628905741512697681355193/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1660745607/100000000000000 : ℝ)*(base19) + (154906909/10000000000000 : ℝ)*(base23) + (4703153/50000000000000 : ℝ)*(base32) + (276949229/100000000000000 : ℝ)*(upper3) + (22554969/10000000000000 : ℝ)*(upper5) + (1000680203957477/100000000000000 : ℝ)*(major0) + (1000680203957477/100000000000000 : ℝ)*(major1) + (1000680203957477/100000000000000 : ℝ)*(major2) + (1662944147/25000000000000 : ℝ)*(sp1) + (5909495143/100000000000000 : ℝ)*(sp2) + (374586086267001/25000000000000 : ℝ)*(sp4) + (149833603254581/10000000000000 : ℝ)*(sp5) + (1498336886503771/100000000000000 : ℝ)*(sp6) + (503015781956349/100000000000000 : ℝ)*(sp7) + (100603158272531/20000000000000 : ℝ)*(f.failure) + (374586086267001/25000000000000 : ℝ)*(f.sum) + (311855461948269/200000000000000000000000000000 : ℝ)*base66 + (3497820925051731/400000000000000000000000000000 : ℝ)*base67 + (698046070948269/400000000000000000000000000000 : ℝ)*base70 + (1211740036548269/400000000000000000000000000000 : ℝ)*base72 + (1003717599651731/200000000000000000000000000000 : ℝ)*base73 + (2888112174948269/400000000000000000000000000000 : ℝ)*base76 + (1246192530251731/400000000000000000000000000000 : ℝ)*base77 + (1367880101451731/400000000000000000000000000000 : ℝ)*base79 + (381011358348269/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3442871/2000000000000000000000 : ℝ)*base89 + (3442871/2000000000000000000000 : ℝ)*base91 + (3442871/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1722_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10749/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1722_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1722_s1_0 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-341771481/2500000000 : ℝ)*x 0 + (1094798377/2000000000 : ℝ)*x 1 + (5129988703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341771481/2500000000 : ℝ)^5399 ≤ (4290349310029/50000000000000 : ℝ)^4375 := by
    have hnat : (341771481 : ℕ)^5399*50000000000000^4375 ≤ 4290349310029^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341771481 2500000000 4290349310029 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094798377/2000000000 : ℝ)^5399 ≤ (47539254411071/100000000000000 : ℝ)^4375 := by
    have hnat : (1094798377 : ℕ)^5399*100000000000000^4375 ≤ 47539254411071^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094798377 2000000000 47539254411071 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129988703/10000000000 : ℝ)^5399 ≤ (43880046951673/100000000000000 : ℝ)^4375 := by
    have hnat : (5129988703 : ℕ)^5399*100000000000000^4375 ≤ 43880046951673^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129988703 10000000000 43880046951673 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341771481/2500000000 : ℝ), (1094798377/2000000000 : ℝ), (5129988703/10000000000 : ℝ)] ![(4290349310029/50000000000000 : ℝ), (47539254411071/100000000000000 : ℝ), (43880046951673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341771481/2500000000 : ℝ)|^5399 ≤ (4290349310029/50000000000000 : ℝ)^4375
        have hw : |(-341771481/2500000000 : ℝ)|=(341771481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094798377/2000000000 : ℝ)|^5399 ≤ (47539254411071/100000000000000 : ℝ)^4375
        have hw : |(1094798377/2000000000 : ℝ)|=(1094798377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129988703/10000000000 : ℝ)|^5399 ≤ (43880046951673/100000000000000 : ℝ)^4375
        have hw : |(5129988703/10000000000 : ℝ)|=(5129988703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s1_1 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335655727/2500000000 : ℝ)*x 0 + (-96605971/625000000 : ℝ)*x 1 + (2564993863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335655727/2500000000 : ℝ)^5399 ≤ (11533829627019/25000000000000 : ℝ)^4375 := by
    have hnat : (1335655727 : ℕ)^5399*25000000000000^4375 ≤ 11533829627019^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335655727 2500000000 11533829627019 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96605971/625000000 : ℝ)^5399 ≤ (4992322425407/50000000000000 : ℝ)^4375 := by
    have hnat : (96605971 : ℕ)^5399*50000000000000^4375 ≤ 4992322425407^4375*625000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96605971 625000000 4992322425407 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564993863/5000000000 : ℝ)^5399 ≤ (2194001831939/5000000000000 : ℝ)^4375 := by
    have hnat : (2564993863 : ℕ)^5399*5000000000000^4375 ≤ 2194001831939^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564993863 5000000000 2194001831939 5000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335655727/2500000000 : ℝ), (-96605971/625000000 : ℝ), (2564993863/5000000000 : ℝ)] ![(11533829627019/25000000000000 : ℝ), (4992322425407/50000000000000 : ℝ), (2194001831939/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335655727/2500000000 : ℝ)|^5399 ≤ (11533829627019/25000000000000 : ℝ)^4375
        have hw : |(1335655727/2500000000 : ℝ)|=(1335655727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96605971/625000000 : ℝ)|^5399 ≤ (4992322425407/50000000000000 : ℝ)^4375
        have hw : |(-96605971/625000000 : ℝ)|=(96605971/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564993863/5000000000 : ℝ)|^5399 ≤ (2194001831939/5000000000000 : ℝ)^4375
        have hw : |(2564993863/5000000000 : ℝ)|=(2564993863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s1_2 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5342621721/10000000000 : ℝ)*x 0 + (5129988551/10000000000 : ℝ)*x 1 + (-1545696029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342621721/10000000000 : ℝ)^5399 ≤ (2306765292941/5000000000000 : ℝ)^4375 := by
    have hnat : (5342621721 : ℕ)^5399*5000000000000^4375 ≤ 2306765292941^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342621721 10000000000 2306765292941 5000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129988551/10000000000 : ℝ)^5399 ≤ (4388004534721/10000000000000 : ℝ)^4375 := by
    have hnat : (5129988551 : ℕ)^5399*10000000000000^4375 ≤ 4388004534721^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129988551 10000000000 4388004534721 10000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1545696029/10000000000 : ℝ)^5399 ≤ (9984648780799/100000000000000 : ℝ)^4375 := by
    have hnat : (1545696029 : ℕ)^5399*100000000000000^4375 ≤ 9984648780799^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545696029 10000000000 9984648780799 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342621721/10000000000 : ℝ), (5129988551/10000000000 : ℝ), (-1545696029/10000000000 : ℝ)] ![(2306765292941/5000000000000 : ℝ), (4388004534721/10000000000000 : ℝ), (9984648780799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342621721/10000000000 : ℝ)|^5399 ≤ (2306765292941/5000000000000 : ℝ)^4375
        have hw : |(5342621721/10000000000 : ℝ)|=(5342621721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129988551/10000000000 : ℝ)|^5399 ≤ (4388004534721/10000000000000 : ℝ)^4375
        have hw : |(5129988551/10000000000 : ℝ)|=(5129988551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1545696029/10000000000 : ℝ)|^5399 ≤ (9984648780799/100000000000000 : ℝ)^4375
        have hw : |(-1545696029/10000000000 : ℝ)|=(1545696029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s1_3 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (817487019/2000000000 : ℝ)*x 0 + (3594773401/10000000000 : ℝ)*x 1 + (4619458897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (817487019/2000000000 : ℝ)^5399 ≤ (33151880643917/100000000000000 : ℝ)^4375 := by
    have hnat : (817487019 : ℕ)^5399*100000000000000^4375 ≤ 33151880643917^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817487019 2000000000 33151880643917 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3594773401/10000000000 : ℝ)^5399 ≤ (14146313202857/50000000000000 : ℝ)^4375 := by
    have hnat : (3594773401 : ℕ)^5399*50000000000000^4375 ≤ 14146313202857^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3594773401 10000000000 14146313202857 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4619458897/10000000000 : ℝ)^5399 ≤ (1542219717669/4000000000000 : ℝ)^4375 := by
    have hnat : (4619458897 : ℕ)^5399*4000000000000^4375 ≤ 1542219717669^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619458897 10000000000 1542219717669 4000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(817487019/2000000000 : ℝ), (3594773401/10000000000 : ℝ), (4619458897/10000000000 : ℝ)] ![(33151880643917/100000000000000 : ℝ), (14146313202857/50000000000000 : ℝ), (1542219717669/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(817487019/2000000000 : ℝ)|^5399 ≤ (33151880643917/100000000000000 : ℝ)^4375
        have hw : |(817487019/2000000000 : ℝ)|=(817487019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3594773401/10000000000 : ℝ)|^5399 ≤ (14146313202857/50000000000000 : ℝ)^4375
        have hw : |(3594773401/10000000000 : ℝ)|=(3594773401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4619458897/10000000000 : ℝ)|^5399 ≤ (1542219717669/4000000000000 : ℝ)^4375
        have hw : |(4619458897/10000000000 : ℝ)|=(4619458897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s1_4 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-341815519/2500000000 : ℝ)*x 0 + (256704393/500000000 : ℝ)*x 1 + (1367456617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341815519/2500000000 : ℝ)^5399 ≤ (4291031532843/50000000000000 : ℝ)^4375 := by
    have hnat : (341815519 : ℕ)^5399*50000000000000^4375 ≤ 4291031532843^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341815519 2500000000 4291031532843 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256704393/500000000 : ℝ)^5399 ≤ (10980830089911/25000000000000 : ℝ)^4375 := by
    have hnat : (256704393 : ℕ)^5399*25000000000000^4375 ≤ 10980830089911^4375*500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256704393 500000000 10980830089911 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367456617/2500000000 : ℝ)^5399 ≤ (1899784662363/4000000000000 : ℝ)^4375 := by
    have hnat : (1367456617 : ℕ)^5399*4000000000000^4375 ≤ 1899784662363^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367456617 2500000000 1899784662363 4000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341815519/2500000000 : ℝ), (256704393/500000000 : ℝ), (1367456617/2500000000 : ℝ)] ![(4291031532843/50000000000000 : ℝ), (10980830089911/25000000000000 : ℝ), (1899784662363/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341815519/2500000000 : ℝ)|^5399 ≤ (4291031532843/50000000000000 : ℝ)^4375
        have hw : |(-341815519/2500000000 : ℝ)|=(341815519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256704393/500000000 : ℝ)|^5399 ≤ (10980830089911/25000000000000 : ℝ)^4375
        have hw : |(256704393/500000000 : ℝ)|=(256704393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367456617/2500000000 : ℝ)|^5399 ≤ (1899784662363/4000000000000 : ℝ)^4375
        have hw : |(1367456617/2500000000 : ℝ)|=(1367456617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s1_5 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625256233/5000000000 : ℝ)*x 0 + (-1205857739/10000000000 : ℝ)*x 1 + (2734913069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625256233/5000000000 : ℝ)^5399 ≤ (22577866780579/50000000000000 : ℝ)^4375 := by
    have hnat : (2625256233 : ℕ)^5399*50000000000000^4375 ≤ 22577866780579^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625256233 5000000000 22577866780579 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1205857739/10000000000 : ℝ)^5399 ≤ (7349653405451/100000000000000 : ℝ)^4375 := by
    have hnat : (1205857739 : ℕ)^5399*100000000000000^4375 ≤ 7349653405451^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205857739 10000000000 7349653405451 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734913069/5000000000 : ℝ)^5399 ≤ (11873653255753/25000000000000 : ℝ)^4375 := by
    have hnat : (2734913069 : ℕ)^5399*25000000000000^4375 ≤ 11873653255753^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734913069 5000000000 11873653255753 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625256233/5000000000 : ℝ), (-1205857739/10000000000 : ℝ), (2734913069/5000000000 : ℝ)] ![(22577866780579/50000000000000 : ℝ), (7349653405451/100000000000000 : ℝ), (11873653255753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625256233/5000000000 : ℝ)|^5399 ≤ (22577866780579/50000000000000 : ℝ)^4375
        have hw : |(2625256233/5000000000 : ℝ)|=(2625256233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1205857739/10000000000 : ℝ)|^5399 ≤ (7349653405451/100000000000000 : ℝ)^4375
        have hw : |(-1205857739/10000000000 : ℝ)|=(1205857739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734913069/5000000000 : ℝ)|^5399 ≤ (11873653255753/25000000000000 : ℝ)^4375
        have hw : |(2734913069/5000000000 : ℝ)|=(2734913069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s1_6 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312628209/2500000000 : ℝ)*x 0 + (5469825981/10000000000 : ℝ)*x 1 + (-7536609/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312628209/2500000000 : ℝ)^5399 ≤ (45155737488043/100000000000000 : ℝ)^4375 := by
    have hnat : (1312628209 : ℕ)^5399*100000000000000^4375 ≤ 45155737488043^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312628209 2500000000 45155737488043 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469825981/10000000000 : ℝ)^5399 ≤ (47494611340703/100000000000000 : ℝ)^4375 := by
    have hnat : (5469825981 : ℕ)^5399*100000000000000^4375 ≤ 47494611340703^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469825981 10000000000 47494611340703 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7536609/62500000 : ℝ)^5399 ≤ (1469930231303/20000000000000 : ℝ)^4375 := by
    have hnat : (7536609 : ℕ)^5399*20000000000000^4375 ≤ 1469930231303^4375*62500000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7536609 62500000 1469930231303 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312628209/2500000000 : ℝ), (5469825981/10000000000 : ℝ), (-7536609/62500000 : ℝ)] ![(45155737488043/100000000000000 : ℝ), (47494611340703/100000000000000 : ℝ), (1469930231303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312628209/2500000000 : ℝ)|^5399 ≤ (45155737488043/100000000000000 : ℝ)^4375
        have hw : |(1312628209/2500000000 : ℝ)|=(1312628209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469825981/10000000000 : ℝ)|^5399 ≤ (47494611340703/100000000000000 : ℝ)^4375
        have hw : |(5469825981/10000000000 : ℝ)|=(5469825981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7536609/62500000 : ℝ)|^5399 ≤ (1469930231303/20000000000000 : ℝ)^4375
        have hw : |(-7536609/62500000 : ℝ)|=(7536609/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s1_7 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4087955231/10000000000 : ℝ)*x 0 + (575905989/1250000000 : ℝ)*x 1 + (901794401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4087955231/10000000000 : ℝ)^5399 ≤ (16578543392611/50000000000000 : ℝ)^4375 := by
    have hnat : (4087955231 : ℕ)^5399*50000000000000^4375 ≤ 16578543392611^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4087955231 10000000000 16578543392611 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (575905989/1250000000 : ℝ)^5399 ≤ (38429760699739/100000000000000 : ℝ)^4375 := by
    have hnat : (575905989 : ℕ)^5399*100000000000000^4375 ≤ 38429760699739^4375*1250000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575905989 1250000000 38429760699739 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901794401/2500000000 : ℝ)^5399 ≤ (28413152495849/100000000000000 : ℝ)^4375 := by
    have hnat : (901794401 : ℕ)^5399*100000000000000^4375 ≤ 28413152495849^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901794401 2500000000 28413152495849 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4087955231/10000000000 : ℝ), (575905989/1250000000 : ℝ), (901794401/2500000000 : ℝ)] ![(16578543392611/50000000000000 : ℝ), (38429760699739/100000000000000 : ℝ), (28413152495849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4087955231/10000000000 : ℝ)|^5399 ≤ (16578543392611/50000000000000 : ℝ)^4375
        have hw : |(4087955231/10000000000 : ℝ)|=(4087955231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(575905989/1250000000 : ℝ)|^5399 ≤ (38429760699739/100000000000000 : ℝ)^4375
        have hw : |(575905989/1250000000 : ℝ)|=(575905989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901794401/2500000000 : ℝ)|^5399 ≤ (28413152495849/100000000000000 : ℝ)^4375
        have hw : |(901794401/2500000000 : ℝ)|=(901794401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1722_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10749/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (989/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17249/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10749/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10749/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10749/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10749/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10749/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10749/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6387/100000 : ℝ) ^ (5391/1024 : ℝ) ≤ (51322555894961/100000000000000000000 : ℝ) := by
    have hpowers : (6387/100000 : ℝ)^5391 ≤ (51322555894961/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6387 : ℕ)^5391*100000000000000000000^1024 ≤ 51322555894961^1024*100000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6387 100000 51322555894961 100000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6387/100000 : ℝ)) (X := (51322555894961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10749/50000 : ℝ) ^ (5391/1024 : ℝ) ≤ (7642764729963413/25000000000000000000 : ℝ) := by
    have hpowers : (10749/50000 : ℝ)^5391 ≤ (7642764729963413/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10749 : ℕ)^5391*25000000000000000000^1024 ≤ 7642764729963413^1024*50000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10749 50000 7642764729963413 25000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10749/50000 : ℝ)) (X := (7642764729963413/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000051322555894961/50000000000000000000 : ℝ) ≤ (10000001949704151/10000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (50000051322555894961/50000000000000000000 : ℝ)^1024 ≤ (10000001949704151/10000000000000000 : ℝ)^5391 := by
      have hnat : (50000051322555894961 : ℕ)^1024*10000000000000000^5391 ≤ 10000001949704151^5391*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000051322555894961 50000000000000000000 10000001949704151 10000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001949704151/10000000000000000 : ℝ)) (X := (50000051322555894961/50000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030622381475748613/100000000000000000000 : ℝ) ≤ (2000116317678117/2000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (100030622381475748613/100000000000000000000 : ℝ)^1024 ≤ (2000116317678117/2000000000000000 : ℝ)^5391 := by
      have hnat : (100030622381475748613 : ℕ)^1024*2000000000000000^5391 ≤ 2000116317678117^5391*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030622381475748613 100000000000000000000 2000116317678117 2000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000116317678117/2000000000000000 : ℝ)) (X := (100030622381475748613/100000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507642764729963413/12500000000000000000 : ℝ) ≤ (10001161227077019/10000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (12507642764729963413/12500000000000000000 : ℝ)^1024 ≤ (10001161227077019/10000000000000000 : ℝ)^5391 := by
      have hnat : (12507642764729963413 : ℕ)^1024*10000000000000000^5391 ≤ 10001161227077019^5391*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507642764729963413 12500000000000000000 10001161227077019 10000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001161227077019/10000000000000000 : ℝ)) (X := (12507642764729963413/12500000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51322555894961/100000000000000000000 : ℝ) ≤ ((3357836114608864841/3358000000000000000 : ℝ)+2*(96606447739/251850000000000 : ℝ)*(6387/100000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (3357836114608864841/3358000000000000000 : ℝ)+2*(96606447739/251850000000000 : ℝ)*(6387/100000 : ℝ)=(10000001949704151/10000000000000000 : ℝ) by norm_num, show 1+2*(51322555894961/100000000000000000000 : ℝ)=(50000051322555894961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7642764729963413/25000000000000000000 : ℝ)+(51322555894961/100000000000000000000 : ℝ) ≤ ((3357836114608864841/3358000000000000000 : ℝ)+(96606447739/251850000000000 : ℝ)*((10749/50000 : ℝ)+(6387/100000 : ℝ)))^(5391/1024 : ℝ) := by
    rw [show (3357836114608864841/3358000000000000000 : ℝ)+(96606447739/251850000000000 : ℝ)*((10749/50000 : ℝ)+(6387/100000 : ℝ))=(2000116317678117/2000000000000000 : ℝ) by norm_num, show 1+(7642764729963413/25000000000000000000 : ℝ)+(51322555894961/100000000000000000000 : ℝ)=(100030622381475748613/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7642764729963413/25000000000000000000 : ℝ) ≤ ((3357836114608864841/3358000000000000000 : ℝ)+2*(96606447739/251850000000000 : ℝ)*(10749/50000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (3357836114608864841/3358000000000000000 : ℝ)+2*(96606447739/251850000000000 : ℝ)*(10749/50000 : ℝ)=(10001161227077019/10000000000000000 : ℝ) by norm_num, show 1+2*(7642764729963413/25000000000000000000 : ℝ)=(12507642764729963413/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3357836114608864841/3358000000000000000 : ℝ)*(X 1 0+X 2 0)+(96606447739/251850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (6387/100000 : ℝ)) (hi := (10749/50000 : ℝ)) (c := (3357836114608864841/3358000000000000000 : ℝ)) (alpha := (96606447739/251850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3357836114608864841/3358000000000000000 : ℝ)*(X 0 1+X 2 1)+(96606447739/251850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (6387/100000 : ℝ)) (hi := (10749/50000 : ℝ)) (c := (3357836114608864841/3358000000000000000 : ℝ)) (alpha := (96606447739/251850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3357836114608864841/3358000000000000000 : ℝ)*(X 0 2+X 1 2)+(96606447739/251850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (6387/100000 : ℝ)) (hi := (10749/50000 : ℝ)) (c := (3357836114608864841/3358000000000000000 : ℝ)) (alpha := (96606447739/251850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-341771481/2500000000 : ℝ)*X 0 0+(1094798377/2000000000 : ℝ)*X 0 1+(5129988703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1335655727/2500000000 : ℝ)*X 1 0+(-96605971/625000000 : ℝ)*X 1 1+(2564993863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5342621721/10000000000 : ℝ)*X 2 0+(5129988551/10000000000 : ℝ)*X 2 1+(-1545696029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((817487019/2000000000 : ℝ)*X 0 0+(3594773401/10000000000 : ℝ)*X 0 1+(4619458897/10000000000 : ℝ)*X 0 2+(817487019/2000000000 : ℝ)*X 1 0+(3594773401/10000000000 : ℝ)*X 1 1+(4619458897/10000000000 : ℝ)*X 1 2+(817487019/2000000000 : ℝ)*X 2 0+(3594773401/10000000000 : ℝ)*X 2 1+(4619458897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-341815519/2500000000 : ℝ)*X 0 0+(256704393/500000000 : ℝ)*X 0 1+(1367456617/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2625256233/5000000000 : ℝ)*X 1 0+(-1205857739/10000000000 : ℝ)*X 1 1+(2734913069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1312628209/2500000000 : ℝ)*X 2 0+(5469825981/10000000000 : ℝ)*X 2 1+(-7536609/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4087955231/10000000000 : ℝ)*X 0 0+(575905989/1250000000 : ℝ)*X 0 1+(901794401/2500000000 : ℝ)*X 0 2+(4087955231/10000000000 : ℝ)*X 1 0+(575905989/1250000000 : ℝ)*X 1 1+(901794401/2500000000 : ℝ)*X 1 2+(4087955231/10000000000 : ℝ)*X 2 0+(575905989/1250000000 : ℝ)*X 2 1+(901794401/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2140588507255975007367473841/167900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (137691499/10000000000000 : ℝ)*(base19) + (64365643/6250000000000 : ℝ)*(base23) + (26130189/25000000000000 : ℝ)*(lower2) + (8684557/5000000000000 : ℝ)*(upper3) + (264154311/100000000000000 : ℝ)*(lower4) + (485360154122417/25000000000000 : ℝ)*(major0) + (485360154122417/25000000000000 : ℝ)*(major1) + (1941440616489669/100000000000000 : ℝ)*(major2) + (2906963075266863/100000000000000 : ℝ)*(sp0) + (2906967961847813/100000000000000 : ℝ)*(sp1) + (726742077228129/25000000000000 : ℝ)*(sp2) + (19518208688711/2000000000000 : ℝ)*(sp3) + (313174797/5000000000000 : ℝ)*(sp4) + (41392323/4000000000000 : ℝ)*(sp7) + (7807291753949/800000000000 : ℝ)*(f.failure) + (2906969338762803/100000000000000 : ℝ)*(f.sum) + (19041442188089/3148125000000000000000000000 : ℝ)*base66 + (257870517365539303/83950000000000000000000000000000 : ℝ)*base68 + (4119985353790962887/1007400000000000000000000000000000 : ℝ)*base69 + (852507480597839303/83950000000000000000000000000000 : ℝ)*base72 + (41966396134627/25185000000000000000000000000 : ℝ)*base74 + (7900601780536362887/1007400000000000000000000000000000 : ℝ)*base75 + (2590438154960107909/251850000000000000000000000000000 : ℝ)*base78 + (612363338771857909/251850000000000000000000000000000 : ℝ)*base80 + (104890279697/12592500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1170809/80000000000000000000 : ℝ)*base89 + (1170809/80000000000000000000 : ℝ)*base91 + (370809/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5301375905617981846703/1679000000000000000000000000 : ℝ) := by norm_num
    linear_combination (458340061/50000000000000 : ℝ)*(base19) + (1403447873/100000000000000 : ℝ)*(base23) + (62248253/50000000000000 : ℝ)*(upper2) + (73217001/100000000000000 : ℝ)*(upper3) + (252427549/100000000000000 : ℝ)*(upper5) + (4973048484473/250000000000 : ℝ)*(major0) + (4973048484473/250000000000 : ℝ)*(major1) + (4973048484473/250000000000 : ℝ)*(major2) + (3586472133/50000000000000 : ℝ)*(sp1) + (4719794137/50000000000000 : ℝ)*(sp2) + (1489255035084043/50000000000000 : ℝ)*(sp4) + (2978501980543699/100000000000000 : ℝ)*(sp5) + (148924961356597/5000000000000 : ℝ)*(sp6) + (249982153040407/25000000000000 : ℝ)*(sp7) + (249982153040407/25000000000000 : ℝ)*(f.failure) + (1489255035084043/50000000000000 : ℝ)*(f.sum) + (6641181271291/1259250000000000000000000000 : ℝ)*base66 + (2930094655345379/2518500000000000000000000000000 : ℝ)*base67 + (12580173522361379/2518500000000000000000000000000 : ℝ)*base69 + (2719446437383621/2518500000000000000000000000000 : ℝ)*base72 + (2099603388643/5037000000000000000000000000 : ℝ)*base74 + (17872982794243621/2518500000000000000000000000000 : ℝ)*base76 + (17852569273825621/2518500000000000000000000000000 : ℝ)*base78 + (5930262429496379/2518500000000000000000000000000 : ℝ)*base79 + (7229278046089/2518500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14350613/2500000000000000000000 : ℝ)*base90 + (14350613/2500000000000000000000 : ℝ)*base92 + (14350613/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1722_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10749/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (989/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17249/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1722_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1722_s2_0 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1369786013/10000000000 : ℝ)*x 0 + (5462820071/10000000000 : ℝ)*x 1 + (2569672523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1369786013/10000000000 : ℝ)^5399 ≤ (4300808800083/50000000000000 : ℝ)^4375 := by
    have hnat : (1369786013 : ℕ)^5399*50000000000000^4375 ≤ 4300808800083^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369786013 10000000000 4300808800083 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462820071/10000000000 : ℝ)^5399 ≤ (23709775932347/50000000000000 : ℝ)^4375 := by
    have hnat : (5462820071 : ℕ)^5399*50000000000000^4375 ≤ 23709775932347^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462820071 10000000000 23709775932347 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569672523/5000000000 : ℝ)^5399 ≤ (21989415261539/50000000000000 : ℝ)^4375 := by
    have hnat : (2569672523 : ℕ)^5399*50000000000000^4375 ≤ 21989415261539^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569672523 5000000000 21989415261539 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1369786013/10000000000 : ℝ), (5462820071/10000000000 : ℝ), (2569672523/5000000000 : ℝ)] ![(4300808800083/50000000000000 : ℝ), (23709775932347/50000000000000 : ℝ), (21989415261539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1369786013/10000000000 : ℝ)|^5399 ≤ (4300808800083/50000000000000 : ℝ)^4375
        have hw : |(-1369786013/10000000000 : ℝ)|=(1369786013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462820071/10000000000 : ℝ)|^5399 ≤ (23709775932347/50000000000000 : ℝ)^4375
        have hw : |(5462820071/10000000000 : ℝ)|=(5462820071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569672523/5000000000 : ℝ)|^5399 ≤ (21989415261539/50000000000000 : ℝ)^4375
        have hw : |(2569672523/5000000000 : ℝ)|=(2569672523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s2_1 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339579329/10000000000 : ℝ)*x 0 + (-307473129/2000000000 : ℝ)*x 1 + (41114759/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339579329/10000000000 : ℝ)^5399 ≤ (46102886794843/100000000000000 : ℝ)^4375 := by
    have hnat : (5339579329 : ℕ)^5399*100000000000000^4375 ≤ 46102886794843^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339579329 10000000000 46102886794843 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307473129/2000000000 : ℝ)^5399 ≤ (9918284466321/100000000000000 : ℝ)^4375 := by
    have hnat : (307473129 : ℕ)^5399*100000000000000^4375 ≤ 9918284466321^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307473129 2000000000 9918284466321 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41114759/80000000 : ℝ)^5399 ≤ (5497353589661/12500000000000 : ℝ)^4375 := by
    have hnat : (41114759 : ℕ)^5399*12500000000000^4375 ≤ 5497353589661^4375*80000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41114759 80000000 5497353589661 12500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339579329/10000000000 : ℝ), (-307473129/2000000000 : ℝ), (41114759/80000000 : ℝ)] ![(46102886794843/100000000000000 : ℝ), (9918284466321/100000000000000 : ℝ), (5497353589661/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339579329/10000000000 : ℝ)|^5399 ≤ (46102886794843/100000000000000 : ℝ)^4375
        have hw : |(5339579329/10000000000 : ℝ)|=(5339579329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-307473129/2000000000 : ℝ)|^5399 ≤ (9918284466321/100000000000000 : ℝ)^4375
        have hw : |(-307473129/2000000000 : ℝ)|=(307473129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41114759/80000000 : ℝ)|^5399 ≤ (5497353589661/12500000000000 : ℝ)^4375
        have hw : |(41114759/80000000 : ℝ)|=(41114759/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s2_2 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5339579129/10000000000 : ℝ)*x 0 + (2569672527/5000000000 : ℝ)*x 1 + (-384341419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5339579129/10000000000 : ℝ)^5399 ≤ (46102884663829/100000000000000 : ℝ)^4375 := by
    have hnat : (5339579129 : ℕ)^5399*100000000000000^4375 ≤ 46102884663829^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5339579129 10000000000 46102884663829 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569672527/5000000000 : ℝ)^5399 ≤ (1099470765189/2500000000000 : ℝ)^4375 := by
    have hnat : (2569672527 : ℕ)^5399*2500000000000^4375 ≤ 1099470765189^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569672527 5000000000 1099470765189 2500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384341419/2500000000 : ℝ)^5399 ≤ (1239785589141/12500000000000 : ℝ)^4375 := by
    have hnat : (384341419 : ℕ)^5399*12500000000000^4375 ≤ 1239785589141^4375*2500000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384341419 2500000000 1239785589141 12500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5339579129/10000000000 : ℝ), (2569672527/5000000000 : ℝ), (-384341419/2500000000 : ℝ)] ![(46102884663829/100000000000000 : ℝ), (1099470765189/2500000000000 : ℝ), (1239785589141/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5339579129/10000000000 : ℝ)|^5399 ≤ (46102884663829/100000000000000 : ℝ)^4375
        have hw : |(5339579129/10000000000 : ℝ)|=(5339579129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569672527/5000000000 : ℝ)|^5399 ≤ (1099470765189/2500000000000 : ℝ)^4375
        have hw : |(2569672527/5000000000 : ℝ)|=(2569672527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-384341419/2500000000 : ℝ)|^5399 ≤ (1239785589141/12500000000000 : ℝ)^4375
        have hw : |(-384341419/2500000000 : ℝ)|=(384341419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s2_3 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4089534411/10000000000 : ℝ)*x 0 + (1812582251/5000000000 : ℝ)*x 1 + (2294353983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4089534411/10000000000 : ℝ)^5399 ≤ (16586447025793/50000000000000 : ℝ)^4375 := by
    have hnat : (4089534411 : ℕ)^5399*50000000000000^4375 ≤ 16586447025793^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4089534411 10000000000 16586447025793 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1812582251/5000000000 : ℝ)^5399 ≤ (28588095458379/100000000000000 : ℝ)^4375 := by
    have hnat : (1812582251 : ℕ)^5399*100000000000000^4375 ≤ 28588095458379^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812582251 5000000000 28588095458379 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2294353983/5000000000 : ℝ)^5399 ≤ (19119505239101/50000000000000 : ℝ)^4375 := by
    have hnat : (2294353983 : ℕ)^5399*50000000000000^4375 ≤ 19119505239101^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294353983 5000000000 19119505239101 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4089534411/10000000000 : ℝ), (1812582251/5000000000 : ℝ), (2294353983/5000000000 : ℝ)] ![(16586447025793/50000000000000 : ℝ), (28588095458379/100000000000000 : ℝ), (19119505239101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4089534411/10000000000 : ℝ)|^5399 ≤ (16586447025793/50000000000000 : ℝ)^4375
        have hw : |(4089534411/10000000000 : ℝ)|=(4089534411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1812582251/5000000000 : ℝ)|^5399 ≤ (28588095458379/100000000000000 : ℝ)^4375
        have hw : |(1812582251/5000000000 : ℝ)|=(1812582251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2294353983/5000000000 : ℝ)|^5399 ≤ (19119505239101/50000000000000 : ℝ)^4375
        have hw : |(2294353983/5000000000 : ℝ)|=(2294353983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s2_4 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-684965597/5000000000 : ℝ)*x 0 + (1028594339/2000000000 : ℝ)*x 1 + (2729569627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (684965597/5000000000 : ℝ)^5399 ≤ (4301371332881/50000000000000 : ℝ)^4375 := by
    have hnat : (684965597 : ℕ)^5399*50000000000000^4375 ≤ 4301371332881^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684965597 5000000000 4301371332881 50000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028594339/2000000000 : ℝ)^5399 ≤ (44017131738221/100000000000000 : ℝ)^4375 := by
    have hnat : (1028594339 : ℕ)^5399*100000000000000^4375 ≤ 44017131738221^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028594339 2000000000 44017131738221 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729569627/5000000000 : ℝ)^5399 ≤ (2961257849097/6250000000000 : ℝ)^4375 := by
    have hnat : (2729569627 : ℕ)^5399*6250000000000^4375 ≤ 2961257849097^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729569627 5000000000 2961257849097 6250000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-684965597/5000000000 : ℝ), (1028594339/2000000000 : ℝ), (2729569627/5000000000 : ℝ)] ![(4301371332881/50000000000000 : ℝ), (44017131738221/100000000000000 : ℝ), (2961257849097/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-684965597/5000000000 : ℝ)|^5399 ≤ (4301371332881/50000000000000 : ℝ)^4375
        have hw : |(-684965597/5000000000 : ℝ)|=(684965597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028594339/2000000000 : ℝ)|^5399 ≤ (44017131738221/100000000000000 : ℝ)^4375
        have hw : |(1028594339/2000000000 : ℝ)|=(1028594339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729569627/5000000000 : ℝ)|^5399 ≤ (2961257849097/6250000000000 : ℝ)^4375
        have hw : |(2729569627/5000000000 : ℝ)|=(2729569627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s2_5 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252989171/10000000000 : ℝ)*x 0 + (-152196433/1250000000 : ℝ)*x 1 + (1091827761/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252989171/10000000000 : ℝ)^5399 ≤ (45182020785397/100000000000000 : ℝ)^4375 := by
    have hnat : (5252989171 : ℕ)^5399*100000000000000^4375 ≤ 45182020785397^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252989171 10000000000 45182020785397 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152196433/1250000000 : ℝ)^5399 ≤ (1859464605901/25000000000000 : ℝ)^4375 := by
    have hnat : (152196433 : ℕ)^5399*25000000000000^4375 ≤ 1859464605901^4375*1250000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152196433 1250000000 1859464605901 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091827761/2000000000 : ℝ)^5399 ≤ (11845030194141/25000000000000 : ℝ)^4375 := by
    have hnat : (1091827761 : ℕ)^5399*25000000000000^4375 ≤ 11845030194141^4375*2000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091827761 2000000000 11845030194141 25000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252989171/10000000000 : ℝ), (-152196433/1250000000 : ℝ), (1091827761/2000000000 : ℝ)] ![(45182020785397/100000000000000 : ℝ), (1859464605901/25000000000000 : ℝ), (11845030194141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252989171/10000000000 : ℝ)|^5399 ≤ (45182020785397/100000000000000 : ℝ)^4375
        have hw : |(5252989171/10000000000 : ℝ)|=(5252989171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-152196433/1250000000 : ℝ)|^5399 ≤ (1859464605901/25000000000000 : ℝ)^4375
        have hw : |(-152196433/1250000000 : ℝ)|=(152196433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091827761/2000000000 : ℝ)|^5399 ≤ (11845030194141/25000000000000 : ℝ)^4375
        have hw : |(1091827761/2000000000 : ℝ)|=(1091827761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s2_6 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626494507/5000000000 : ℝ)*x 0 + (136478473/250000000 : ℝ)*x 1 + (-608785761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626494507/5000000000 : ℝ)^5399 ≤ (2259100955947/5000000000000 : ℝ)^4375 := by
    have hnat : (2626494507 : ℕ)^5399*5000000000000^4375 ≤ 2259100955947^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626494507 5000000000 2259100955947 5000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136478473/250000000 : ℝ)^5399 ≤ (9476024401653/20000000000000 : ℝ)^4375 := by
    have hnat : (136478473 : ℕ)^5399*20000000000000^4375 ≤ 9476024401653^4375*250000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136478473 250000000 9476024401653 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (608785761/5000000000 : ℝ)^5399 ≤ (185946471521/2500000000000 : ℝ)^4375 := by
    have hnat : (608785761 : ℕ)^5399*2500000000000^4375 ≤ 185946471521^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608785761 5000000000 185946471521 2500000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626494507/5000000000 : ℝ), (136478473/250000000 : ℝ), (-608785761/5000000000 : ℝ)] ![(2259100955947/5000000000000 : ℝ), (9476024401653/20000000000000 : ℝ), (185946471521/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626494507/5000000000 : ℝ)|^5399 ≤ (2259100955947/5000000000000 : ℝ)^4375
        have hw : |(2626494507/5000000000 : ℝ)|=(2626494507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136478473/250000000 : ℝ)|^5399 ≤ (9476024401653/20000000000000 : ℝ)^4375
        have hw : |(136478473/250000000 : ℝ)|=(136478473/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-608785761/5000000000 : ℝ)|^5399 ≤ (185946471521/2500000000000 : ℝ)^4375
        have hw : |(-608785761/5000000000 : ℝ)|=(608785761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1722_s2_7 (p : ℝ) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4089967089/10000000000 : ℝ)*x 0 + (2288951971/5000000000 : ℝ)*x 1 + (454516151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4089967089/10000000000 : ℝ)^5399 ≤ (33177225318577/100000000000000 : ℝ)^4375 := by
    have hnat : (4089967089 : ℕ)^5399*100000000000000^4375 ≤ 33177225318577^4375*10000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4089967089 10000000000 33177225318577 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288951971/5000000000 : ℝ)^5399 ≤ (7625587046539/20000000000000 : ℝ)^4375 := by
    have hnat : (2288951971 : ℕ)^5399*20000000000000^4375 ≤ 7625587046539^4375*5000000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288951971 5000000000 7625587046539 20000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454516151/1250000000 : ℝ)^5399 ≤ (28694839427147/100000000000000 : ℝ)^4375 := by
    have hnat : (454516151 : ℕ)^5399*100000000000000^4375 ≤ 28694839427147^4375*1250000000^5399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454516151 1250000000 28694839427147 100000000000000 5399 4375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5399/1024 : ℝ)) 5399 4375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4089967089/10000000000 : ℝ), (2288951971/5000000000 : ℝ), (454516151/1250000000 : ℝ)] ![(33177225318577/100000000000000 : ℝ), (7625587046539/20000000000000 : ℝ), (28694839427147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4089967089/10000000000 : ℝ)|^5399 ≤ (33177225318577/100000000000000 : ℝ)^4375
        have hw : |(4089967089/10000000000 : ℝ)|=(4089967089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2288951971/5000000000 : ℝ)|^5399 ≤ (7625587046539/20000000000000 : ℝ)^4375
        have hw : |(2288951971/5000000000 : ℝ)|=(2288951971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(454516151/1250000000 : ℝ)|^5399 ≤ (28694839427147/100000000000000 : ℝ)^4375
        have hw : |(454516151/1250000000 : ℝ)|=(454516151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1722_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (989/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5047/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8507/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (989/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (989/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (989/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (989/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (989/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (989/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (989/10000 : ℝ) ^ (5391/1024 : ℝ) ≤ (51293428250061/10000000000000000000 : ℝ) := by
    have hpowers : (989/10000 : ℝ)^5391 ≤ (51293428250061/10000000000000000000 : ℝ)^1024 := by
      have hnat : (989 : ℕ)^5391*10000000000000000000^1024 ≤ 51293428250061^1024*10000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        989 10000 51293428250061 10000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (989/10000 : ℝ)) (X := (51293428250061/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17249/100000 : ℝ) ^ (5391/1024 : ℝ) ≤ (4795129934681703/50000000000000000000 : ℝ) := by
    have hpowers : (17249/100000 : ℝ)^5391 ≤ (4795129934681703/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17249 : ℕ)^5391*50000000000000000000^1024 ≤ 4795129934681703^1024*100000^5391 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17249 100000 4795129934681703 50000000000000000000 5391 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17249/100000 : ℝ)) (X := (4795129934681703/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000051293428250061/5000000000000000000 : ℝ) ≤ (10000019485903279/10000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (5000051293428250061/5000000000000000000 : ℝ)^1024 ≤ (10000019485903279/10000000000000000 : ℝ)^5391 := by
      have hnat : (5000051293428250061 : ℕ)^1024*10000000000000000^5391 ≤ 10000019485903279^5391*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000051293428250061 5000000000000000000 10000019485903279 10000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000019485903279/10000000000000000 : ℝ)) (X := (5000051293428250061/5000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6250631449634491501/6250000000000000000 : ℝ) ≤ (2500047974621989/2500000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (6250631449634491501/6250000000000000000 : ℝ)^1024 ≤ (2500047974621989/2500000000000000 : ℝ)^5391 := by
      have hnat : (6250631449634491501 : ℕ)^1024*2500000000000000^5391 ≤ 2500047974621989^5391*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250631449634491501 6250000000000000000 2500047974621989 2500000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500047974621989/2500000000000000 : ℝ)) (X := (6250631449634491501/6250000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004795129934681703/25000000000000000000 : ℝ) ≤ (10000364311072633/10000000000000000 : ℝ) ^ (5391/1024 : ℝ) := by
    have hpowers : (25004795129934681703/25000000000000000000 : ℝ)^1024 ≤ (10000364311072633/10000000000000000 : ℝ)^5391 := by
      have hnat : (25004795129934681703 : ℕ)^1024*10000000000000000^5391 ≤ 10000364311072633^5391*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004795129934681703 25000000000000000000 10000364311072633 10000000000000000 1024 5391 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000364311072633/10000000000000000 : ℝ)) (X := (25004795129934681703/25000000000000000000 : ℝ)) (by norm_num) 5391 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51293428250061/10000000000000000000 : ℝ) ≤ ((24528911025279106367/24530000000000000000 : ℝ)+2*(57470861559/245300000000000 : ℝ)*(989/10000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (24528911025279106367/24530000000000000000 : ℝ)+2*(57470861559/245300000000000 : ℝ)*(989/10000 : ℝ)=(10000019485903279/10000000000000000 : ℝ) by norm_num, show 1+2*(51293428250061/10000000000000000000 : ℝ)=(5000051293428250061/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4795129934681703/50000000000000000000 : ℝ)+(51293428250061/10000000000000000000 : ℝ) ≤ ((24528911025279106367/24530000000000000000 : ℝ)+(57470861559/245300000000000 : ℝ)*((17249/100000 : ℝ)+(989/10000 : ℝ)))^(5391/1024 : ℝ) := by
    rw [show (24528911025279106367/24530000000000000000 : ℝ)+(57470861559/245300000000000 : ℝ)*((17249/100000 : ℝ)+(989/10000 : ℝ))=(2500047974621989/2500000000000000 : ℝ) by norm_num, show 1+(4795129934681703/50000000000000000000 : ℝ)+(51293428250061/10000000000000000000 : ℝ)=(6250631449634491501/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4795129934681703/50000000000000000000 : ℝ) ≤ ((24528911025279106367/24530000000000000000 : ℝ)+2*(57470861559/245300000000000 : ℝ)*(17249/100000 : ℝ))^(5391/1024 : ℝ) := by
    rw [show (24528911025279106367/24530000000000000000 : ℝ)+2*(57470861559/245300000000000 : ℝ)*(17249/100000 : ℝ)=(10000364311072633/10000000000000000 : ℝ) by norm_num, show 1+2*(4795129934681703/50000000000000000000 : ℝ)=(25004795129934681703/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24528911025279106367/24530000000000000000 : ℝ)*(X 1 0+X 2 0)+(57470861559/245300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (989/10000 : ℝ)) (hi := (17249/100000 : ℝ)) (c := (24528911025279106367/24530000000000000000 : ℝ)) (alpha := (57470861559/245300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24528911025279106367/24530000000000000000 : ℝ)*(X 0 1+X 2 1)+(57470861559/245300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (989/10000 : ℝ)) (hi := (17249/100000 : ℝ)) (c := (24528911025279106367/24530000000000000000 : ℝ)) (alpha := (57470861559/245300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24528911025279106367/24530000000000000000 : ℝ)*(X 0 2+X 1 2)+(57470861559/245300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5391/1024 : ℝ)) (lo := (989/10000 : ℝ)) (hi := (17249/100000 : ℝ)) (c := (24528911025279106367/24530000000000000000 : ℝ)) (alpha := (57470861559/245300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1369786013/10000000000 : ℝ)*X 0 0+(5462820071/10000000000 : ℝ)*X 0 1+(2569672523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5339579329/10000000000 : ℝ)*X 1 0+(-307473129/2000000000 : ℝ)*X 1 1+(41114759/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5339579129/10000000000 : ℝ)*X 2 0+(2569672527/5000000000 : ℝ)*X 2 1+(-384341419/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4089534411/10000000000 : ℝ)*X 0 0+(1812582251/5000000000 : ℝ)*X 0 1+(2294353983/5000000000 : ℝ)*X 0 2+(4089534411/10000000000 : ℝ)*X 1 0+(1812582251/5000000000 : ℝ)*X 1 1+(2294353983/5000000000 : ℝ)*X 1 2+(4089534411/10000000000 : ℝ)*X 2 0+(1812582251/5000000000 : ℝ)*X 2 1+(2294353983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-684965597/5000000000 : ℝ)*X 0 0+(1028594339/2000000000 : ℝ)*X 0 1+(2729569627/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252989171/10000000000 : ℝ)*X 1 0+(-152196433/1250000000 : ℝ)*X 1 1+(1091827761/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626494507/5000000000 : ℝ)*X 2 0+(136478473/250000000 : ℝ)*X 2 1+(-608785761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4089967089/10000000000 : ℝ)*X 0 0+(2288951971/5000000000 : ℝ)*X 0 1+(454516151/1250000000 : ℝ)*X 0 2+(4089967089/10000000000 : ℝ)*X 1 0+(2288951971/5000000000 : ℝ)*X 1 1+(454516151/1250000000 : ℝ)*X 1 2+(4089967089/10000000000 : ℝ)*X 2 0+(2288951971/5000000000 : ℝ)*X 2 1+(454516151/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1722_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2814921942072676987641921669/245300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6562869/400000000000 : ℝ)*(base19) + (362361803/25000000000000 : ℝ)*(base23) + (10075251/25000000000000 : ℝ)*(lower2) + (282204047/100000000000000 : ℝ)*(upper3) + (38885583/20000000000000 : ℝ)*(upper5) + (1032326638734423/50000000000000 : ℝ)*(major0) + (1032326638734423/50000000000000 : ℝ)*(major1) + (2064653277468847/100000000000000 : ℝ)*(major2) + (1545722228900509/50000000000000 : ℝ)*(sp0) + (772864319315121/25000000000000 : ℝ)*(sp1) + (1545728734265261/50000000000000 : ℝ)*(sp2) + (51892062863563/5000000000000 : ℝ)*(sp3) + (3615044179/25000000000000 : ℝ)*(sp4) + (11994349/200000000000 : ℝ)*(sp7) + (3243272670143/312500000000 : ℝ)*(f.failure) + (1545729458988867/50000000000000 : ℝ)*(f.sum) + (87223030142273/24530000000000000000000000000 : ℝ)*base66 + (4143930774271978759/1226500000000000000000000000000000 : ℝ)*base68 + (11443262799977248849/2453000000000000000000000000000000 : ℝ)*base69 + (3237812416588978759/1226500000000000000000000000000000 : ℝ)*base72 + (128540369433187/24530000000000000000000000000 : ℝ)*base73 + (451485561953248849/2453000000000000000000000000000000 : ℝ)*base75 + (12385151194769928759/1226500000000000000000000000000000 : ℝ)*base78 + (4328390451034928759/1226500000000000000000000000000000 : ℝ)*base80 + (40120749054297/6132500000000000000000000000 : ℝ)*base81 + (36837/31250000000000000000 : ℝ)*base90 + (36837/31250000000000000000 : ℝ)*base92 + (349337/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9110367576540380499708691083/1226500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (692550241/50000000000000 : ℝ)*(base19) + (85140347/6250000000000 : ℝ)*(base23) + (160156419/100000000000000 : ℝ)*(upper3) + (45283191/100000000000000 : ℝ)*(lower4) + (7148337/3125000000000 : ℝ)*(upper5) + (2112352470364217/100000000000000 : ℝ)*(major0) + (2112352470364217/100000000000000 : ℝ)*(major1) + (2112352470364217/100000000000000 : ℝ)*(major2) + (10218616669/100000000000000 : ℝ)*(sp1) + (9337266907/100000000000000 : ℝ)*(sp2) + (3162880300767163/100000000000000 : ℝ)*(sp4) + (790717174262503/25000000000000 : ℝ)*(sp5) + (632573920250941/20000000000000 : ℝ)*(sp6) + (265456098090821/25000000000000 : ℝ)*(sp7) + (265456098090821/25000000000000 : ℝ)*(f.failure) + (3162880300767163/100000000000000 : ℝ)*(f.sum) + (33328627507993/12265000000000000000000000000 : ℝ)*base65 + (12574236457914969639/2453000000000000000000000000000000 : ℝ)*base67 + (8543715442481969639/2453000000000000000000000000000000 : ℝ)*base69 + (6540841052866969639/2453000000000000000000000000000000 : ℝ)*base71 + (3216368870159/1533125000000000000000000000 : ℝ)*base74 + (5840213529732969639/2453000000000000000000000000000000 : ℝ)*base75 + (5851076480293030361/2453000000000000000000000000000000 : ℝ)*base78 + (14831894495814030361/2453000000000000000000000000000000 : ℝ)*base80 + (50710263232853/12265000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (27738239/2500000000000000000000 : ℝ)*base90 + (27738239/2500000000000000000000 : ℝ)*base92 + (27738239/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1722_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (989/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5047/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8507/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1722_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1722_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5047/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8507/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1722_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1722_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1722_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5391/1024 : ℝ) ≤ p) (hpb : p ≤ (5399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (198936141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5047/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8507/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1722_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

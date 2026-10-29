-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1655_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:17:37.291573+00:00
-- url     : https://prove2.me/submissions/4cf11e2f-d190-4a03-be3d-85be2f03c5b2

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
theorem support_rectangle_w1655_s0_0 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1483922893/10000000000 : ℝ)*x 0 + (1444784059/2500000000 : ℝ)*x 1 + (492493653/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1483922893/10000000000 : ℝ)^4939 ≤ (4504610596921/50000000000000 : ℝ)^3915 := by
    have hnat : (1483922893 : ℕ)^4939*50000000000000^3915 ≤ 4504610596921^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483922893 10000000000 4504610596921 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1444784059/2500000000 : ℝ)^4939 ≤ (5006984549939/10000000000000 : ℝ)^3915 := by
    have hnat : (1444784059 : ℕ)^4939*10000000000000^3915 ≤ 5006984549939^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444784059 2500000000 5006984549939 10000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492493653/1000000000 : ℝ)^4939 ≤ (40920933290171/100000000000000 : ℝ)^3915 := by
    have hnat : (492493653 : ℕ)^4939*100000000000000^3915 ≤ 40920933290171^3915*1000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492493653 1000000000 40920933290171 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1483922893/10000000000 : ℝ), (1444784059/2500000000 : ℝ), (492493653/1000000000 : ℝ)] ![(4504610596921/50000000000000 : ℝ), (5006984549939/10000000000000 : ℝ), (40920933290171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1483922893/10000000000 : ℝ)|^4939 ≤ (4504610596921/50000000000000 : ℝ)^3915
        have hw : |(-1483922893/10000000000 : ℝ)|=(1483922893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1444784059/2500000000 : ℝ)|^4939 ≤ (5006984549939/10000000000000 : ℝ)^3915
        have hw : |(1444784059/2500000000 : ℝ)|=(1444784059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(492493653/1000000000 : ℝ)|^4939 ≤ (40920933290171/100000000000000 : ℝ)^3915
        have hw : |(492493653/1000000000 : ℝ)|=(492493653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s0_1 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108711183/200000000 : ℝ)*x 0 + (-976170731/5000000000 : ℝ)*x 1 + (2462468521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108711183/200000000 : ℝ)^4939 ≤ (11586045107927/25000000000000 : ℝ)^3915 := by
    have hnat : (108711183 : ℕ)^4939*25000000000000^3915 ≤ 11586045107927^3915*200000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108711183 200000000 11586045107927 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976170731/5000000000 : ℝ)^4939 ≤ (509395235967/4000000000000 : ℝ)^3915 := by
    have hnat : (976170731 : ℕ)^4939*4000000000000^3915 ≤ 509395235967^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976170731 5000000000 509395235967 4000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2462468521/5000000000 : ℝ)^4939 ≤ (20460469328527/50000000000000 : ℝ)^3915 := by
    have hnat : (2462468521 : ℕ)^4939*50000000000000^3915 ≤ 20460469328527^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2462468521 5000000000 20460469328527 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108711183/200000000 : ℝ), (-976170731/5000000000 : ℝ), (2462468521/5000000000 : ℝ)] ![(11586045107927/25000000000000 : ℝ), (509395235967/4000000000000 : ℝ), (20460469328527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108711183/200000000 : ℝ)|^4939 ≤ (11586045107927/25000000000000 : ℝ)^3915
        have hw : |(108711183/200000000 : ℝ)|=(108711183/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976170731/5000000000 : ℝ)|^4939 ≤ (509395235967/4000000000000 : ℝ)^3915
        have hw : |(-976170731/5000000000 : ℝ)|=(976170731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2462468521/5000000000 : ℝ)|^4939 ≤ (20460469328527/50000000000000 : ℝ)^3915
        have hw : |(2462468521/5000000000 : ℝ)|=(2462468521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s0_2 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2717780059/5000000000 : ℝ)*x 0 + (4924936313/10000000000 : ℝ)*x 1 + (-15618729/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2717780059/5000000000 : ℝ)^4939 ≤ (9268838168739/20000000000000 : ℝ)^3915 := by
    have hnat : (2717780059 : ℕ)^4939*20000000000000^3915 ≤ 9268838168739^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717780059 5000000000 9268838168739 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4924936313/10000000000 : ℝ)^4939 ≤ (2557558188471/6250000000000 : ℝ)^3915 := by
    have hnat : (4924936313 : ℕ)^4939*6250000000000^3915 ≤ 2557558188471^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4924936313 10000000000 2557558188471 6250000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15618729/80000000 : ℝ)^4939 ≤ (12734878126007/100000000000000 : ℝ)^3915 := by
    have hnat : (15618729 : ℕ)^4939*100000000000000^3915 ≤ 12734878126007^3915*80000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15618729 80000000 12734878126007 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2717780059/5000000000 : ℝ), (4924936313/10000000000 : ℝ), (-15618729/80000000 : ℝ)] ![(9268838168739/20000000000000 : ℝ), (2557558188471/6250000000000 : ℝ), (12734878126007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2717780059/5000000000 : ℝ)|^4939 ≤ (9268838168739/20000000000000 : ℝ)^3915
        have hw : |(2717780059/5000000000 : ℝ)|=(2717780059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4924936313/10000000000 : ℝ)|^4939 ≤ (2557558188471/6250000000000 : ℝ)^3915
        have hw : |(4924936313/10000000000 : ℝ)|=(4924936313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15618729/80000000 : ℝ)|^4939 ≤ (12734878126007/100000000000000 : ℝ)^3915
        have hw : |(-15618729/80000000 : ℝ)|=(15618729/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s0_3 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4088281497/10000000000 : ℝ)*x 0 + (308387863/1000000000 : ℝ)*x 1 + (2653917817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4088281497/10000000000 : ℝ)^4939 ≤ (2022162965413/6250000000000 : ℝ)^3915 := by
    have hnat : (4088281497 : ℕ)^4939*6250000000000^3915 ≤ 2022162965413^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4088281497 10000000000 2022162965413 6250000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (308387863/1000000000 : ℝ)^4939 ≤ (4534156674241/20000000000000 : ℝ)^3915 := by
    have hnat : (308387863 : ℕ)^4939*20000000000000^3915 ≤ 4534156674241^3915*1000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308387863 1000000000 4534156674241 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2653917817/5000000000 : ℝ)^4939 ≤ (44974609173089/100000000000000 : ℝ)^3915 := by
    have hnat : (2653917817 : ℕ)^4939*100000000000000^3915 ≤ 44974609173089^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653917817 5000000000 44974609173089 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4088281497/10000000000 : ℝ), (308387863/1000000000 : ℝ), (2653917817/5000000000 : ℝ)] ![(2022162965413/6250000000000 : ℝ), (4534156674241/20000000000000 : ℝ), (44974609173089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4088281497/10000000000 : ℝ)|^4939 ≤ (2022162965413/6250000000000 : ℝ)^3915
        have hw : |(4088281497/10000000000 : ℝ)|=(4088281497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(308387863/1000000000 : ℝ)|^4939 ≤ (4534156674241/20000000000000 : ℝ)^3915
        have hw : |(308387863/1000000000 : ℝ)|=(308387863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2653917817/5000000000 : ℝ)|^4939 ≤ (44974609173089/100000000000000 : ℝ)^3915
        have hw : |(2653917817/5000000000 : ℝ)|=(2653917817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s0_4 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-297232601/2000000000 : ℝ)*x 0 + (4946069081/10000000000 : ℝ)*x 1 + (359829829/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (297232601/2000000000 : ℝ)^4939 ≤ (9026382036381/100000000000000 : ℝ)^3915 := by
    have hnat : (297232601 : ℕ)^4939*100000000000000^3915 ≤ 9026382036381^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297232601 2000000000 9026382036381 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4946069081/10000000000 : ℝ)^4939 ≤ (20571286471927/50000000000000 : ℝ)^3915 := by
    have hnat : (4946069081 : ℕ)^4939*50000000000000^3915 ≤ 20571286471927^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4946069081 10000000000 20571286471927 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359829829/625000000 : ℝ)^4939 ≤ (9966208999911/20000000000000 : ℝ)^3915 := by
    have hnat : (359829829 : ℕ)^4939*20000000000000^3915 ≤ 9966208999911^3915*625000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359829829 625000000 9966208999911 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-297232601/2000000000 : ℝ), (4946069081/10000000000 : ℝ), (359829829/625000000 : ℝ)] ![(9026382036381/100000000000000 : ℝ), (20571286471927/50000000000000 : ℝ), (9966208999911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-297232601/2000000000 : ℝ)|^4939 ≤ (9026382036381/100000000000000 : ℝ)^3915
        have hw : |(-297232601/2000000000 : ℝ)|=(297232601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4946069081/10000000000 : ℝ)|^4939 ≤ (20571286471927/50000000000000 : ℝ)^3915
        have hw : |(4946069081/10000000000 : ℝ)|=(4946069081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(359829829/625000000 : ℝ)|^4939 ≤ (9966208999911/20000000000000 : ℝ)^3915
        have hw : |(359829829/625000000 : ℝ)|=(359829829/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s0_5 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2601252787/5000000000 : ℝ)*x 0 + (-1120001259/10000000000 : ℝ)*x 1 + (5757277231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2601252787/5000000000 : ℝ)^4939 ≤ (43851620427397/100000000000000 : ℝ)^3915 := by
    have hnat : (2601252787 : ℕ)^4939*100000000000000^3915 ≤ 43851620427397^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601252787 5000000000 43851620427397 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120001259/10000000000 : ℝ)^4939 ≤ (3158667457287/50000000000000 : ℝ)^3915 := by
    have hnat : (1120001259 : ℕ)^4939*50000000000000^3915 ≤ 3158667457287^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120001259 10000000000 3158667457287 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5757277231/10000000000 : ℝ)^4939 ≤ (24915522319611/50000000000000 : ℝ)^3915 := by
    have hnat : (5757277231 : ℕ)^4939*50000000000000^3915 ≤ 24915522319611^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5757277231 10000000000 24915522319611 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2601252787/5000000000 : ℝ), (-1120001259/10000000000 : ℝ), (5757277231/10000000000 : ℝ)] ![(43851620427397/100000000000000 : ℝ), (3158667457287/50000000000000 : ℝ), (24915522319611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2601252787/5000000000 : ℝ)|^4939 ≤ (43851620427397/100000000000000 : ℝ)^3915
        have hw : |(2601252787/5000000000 : ℝ)|=(2601252787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1120001259/10000000000 : ℝ)|^4939 ≤ (3158667457287/50000000000000 : ℝ)^3915
        have hw : |(-1120001259/10000000000 : ℝ)|=(1120001259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5757277231/10000000000 : ℝ)|^4939 ≤ (24915522319611/50000000000000 : ℝ)^3915
        have hw : |(5757277231/10000000000 : ℝ)|=(5757277231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s0_6 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208100233/400000000 : ℝ)*x 0 + (1439319251/2500000000 : ℝ)*x 1 + (-1120001233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208100233/400000000 : ℝ)^4939 ≤ (43851623096431/100000000000000 : ℝ)^3915 := by
    have hnat : (208100233 : ℕ)^4939*100000000000000^3915 ≤ 43851623096431^3915*400000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208100233 400000000 43851623096431 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1439319251/2500000000 : ℝ)^4939 ≤ (6228880270071/12500000000000 : ℝ)^3915 := by
    have hnat : (1439319251 : ℕ)^4939*12500000000000^3915 ≤ 6228880270071^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439319251 2500000000 6228880270071 12500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120001233/10000000000 : ℝ)^4939 ≤ (1579333682391/25000000000000 : ℝ)^3915 := by
    have hnat : (1120001233 : ℕ)^4939*25000000000000^3915 ≤ 1579333682391^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120001233 10000000000 1579333682391 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208100233/400000000 : ℝ), (1439319251/2500000000 : ℝ), (-1120001233/10000000000 : ℝ)] ![(43851623096431/100000000000000 : ℝ), (6228880270071/12500000000000 : ℝ), (1579333682391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208100233/400000000 : ℝ)|^4939 ≤ (43851623096431/100000000000000 : ℝ)^3915
        have hw : |(208100233/400000000 : ℝ)|=(208100233/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1439319251/2500000000 : ℝ)|^4939 ≤ (6228880270071/12500000000000 : ℝ)^3915
        have hw : |(1439319251/2500000000 : ℝ)|=(1439319251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120001233/10000000000 : ℝ)|^4939 ≤ (1579333682391/25000000000000 : ℝ)^3915
        have hw : |(-1120001233/10000000000 : ℝ)|=(1120001233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s0_7 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4094114453/10000000000 : ℝ)*x 0 + (656602031/1250000000 : ℝ)*x 1 + (785197707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4094114453/10000000000 : ℝ)^4939 ≤ (32412854277669/100000000000000 : ℝ)^3915 := by
    have hnat : (4094114453 : ℕ)^4939*100000000000000^3915 ≤ 32412854277669^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4094114453 10000000000 32412854277669 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656602031/1250000000 : ℝ)^4939 ≤ (11096819759361/25000000000000 : ℝ)^3915 := by
    have hnat : (656602031 : ℕ)^4939*25000000000000^3915 ≤ 11096819759361^3915*1250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656602031 1250000000 11096819759361 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (785197707/2500000000 : ℝ)^4939 ≤ (11599933339651/50000000000000 : ℝ)^3915 := by
    have hnat : (785197707 : ℕ)^4939*50000000000000^3915 ≤ 11599933339651^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785197707 2500000000 11599933339651 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4094114453/10000000000 : ℝ), (656602031/1250000000 : ℝ), (785197707/2500000000 : ℝ)] ![(32412854277669/100000000000000 : ℝ), (11096819759361/25000000000000 : ℝ), (11599933339651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4094114453/10000000000 : ℝ)|^4939 ≤ (32412854277669/100000000000000 : ℝ)^3915
        have hw : |(4094114453/10000000000 : ℝ)|=(4094114453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656602031/1250000000 : ℝ)|^4939 ≤ (11096819759361/25000000000000 : ℝ)^3915
        have hw : |(656602031/1250000000 : ℝ)|=(656602031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(785197707/2500000000 : ℝ)|^4939 ≤ (11599933339651/50000000000000 : ℝ)^3915
        have hw : |(785197707/2500000000 : ℝ)|=(785197707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1655_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (247/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23251/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4935/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4935 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4935*1^1024 ≤ 0^1024*1^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4935/1024 : ℝ) ≤ (120835186088695187/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4935 ≤ (120835186088695187/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4935*10000000000000000000^1024 ≤ 120835186088695187^1024*5^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 120835186088695187 10000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (120835186088695187/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4935 := by
      have hnat : (1 : ℕ)^1024*1^4935 ≤ 1^4935*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10120835186088695187/10000000000000000000 : ℝ) ≤ (10024953802320709/10000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (10120835186088695187/10000000000000000000 : ℝ)^1024 ≤ (10024953802320709/10000000000000000 : ℝ)^4935 := by
      have hnat : (10120835186088695187 : ℕ)^1024*10000000000000000^4935 ≤ 10024953802320709^4935*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10120835186088695187 10000000000000000000 10024953802320709 10000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024953802320709/10000000000000000 : ℝ)) (X := (10120835186088695187/10000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5120835186088695187/5000000000000000000 : ℝ) ≤ (5024953802320709/5000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (5120835186088695187/5000000000000000000 : ℝ)^1024 ≤ (5024953802320709/5000000000000000 : ℝ)^4935 := by
      have hnat : (5120835186088695187 : ℕ)^1024*5000000000000000^4935 ≤ 5024953802320709^4935*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5120835186088695187 5000000000000000000 5024953802320709 5000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5024953802320709/5000000000000000 : ℝ)) (X := (5120835186088695187/5000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(24953802320709/4000000000000000 : ℝ)*(0 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24953802320709/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(120835186088695187/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(24953802320709/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4935/1024 : ℝ) := by
    rw [show (1 : ℝ)+(24953802320709/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10024953802320709/10000000000000000 : ℝ) by norm_num, show 1+(120835186088695187/10000000000000000000 : ℝ)+(0 : ℝ)=(10120835186088695187/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(120835186088695187/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(24953802320709/4000000000000000 : ℝ)*(2/5 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24953802320709/4000000000000000 : ℝ)*(2/5 : ℝ)=(5024953802320709/5000000000000000 : ℝ) by norm_num, show 1+2*(120835186088695187/10000000000000000000 : ℝ)=(5120835186088695187/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(24953802320709/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24953802320709/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(24953802320709/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24953802320709/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(24953802320709/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24953802320709/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1483922893/10000000000 : ℝ)*X 0 0+(1444784059/2500000000 : ℝ)*X 0 1+(492493653/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((108711183/200000000 : ℝ)*X 1 0+(-976170731/5000000000 : ℝ)*X 1 1+(2462468521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2717780059/5000000000 : ℝ)*X 2 0+(4924936313/10000000000 : ℝ)*X 2 1+(-15618729/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4088281497/10000000000 : ℝ)*X 0 0+(308387863/1000000000 : ℝ)*X 0 1+(2653917817/5000000000 : ℝ)*X 0 2+(4088281497/10000000000 : ℝ)*X 1 0+(308387863/1000000000 : ℝ)*X 1 1+(2653917817/5000000000 : ℝ)*X 1 2+(4088281497/10000000000 : ℝ)*X 2 0+(308387863/1000000000 : ℝ)*X 2 1+(2653917817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-297232601/2000000000 : ℝ)*X 0 0+(4946069081/10000000000 : ℝ)*X 0 1+(359829829/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2601252787/5000000000 : ℝ)*X 1 0+(-1120001259/10000000000 : ℝ)*X 1 1+(5757277231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((208100233/400000000 : ℝ)*X 2 0+(1439319251/2500000000 : ℝ)*X 2 1+(-1120001233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4094114453/10000000000 : ℝ)*X 0 0+(656602031/1250000000 : ℝ)*X 0 1+(785197707/2500000000 : ℝ)*X 0 2+(4094114453/10000000000 : ℝ)*X 1 0+(656602031/1250000000 : ℝ)*X 1 1+(785197707/2500000000 : ℝ)*X 1 2+(4094114453/10000000000 : ℝ)*X 2 0+(656602031/1250000000 : ℝ)*X 2 1+(785197707/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127370936400727826560041/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136956669/100000000000000 : ℝ)*(base1) + (1192410249/100000000000000 : ℝ)*(base19) + (1400895387/100000000000000 : ℝ)*(base23) + (68606701/100000000000000 : ℝ)*(upper3) + (118153077/50000000000000 : ℝ)*(upper5) + (162035053759417/20000000000000 : ℝ)*(major0) + (162035053759417/20000000000000 : ℝ)*(major1) + (162035053759417/20000000000000 : ℝ)*(major2) + (1170690737405217/100000000000000 : ℝ)*(sp0) + (1170695764069909/100000000000000 : ℝ)*(sp1) + (1170695555584771/100000000000000 : ℝ)*(sp2) + (449651253322447/100000000000000 : ℝ)*(sp3) + (6356031609/100000000000000 : ℝ)*(sp4) + (247318749/12500000000000 : ℝ)*(sp7) + (112413342207277/25000000000000 : ℝ)*(f.failure) + (585348478240079/50000000000000 : ℝ)*(f.sum) + (22280025493347/40000000000000000000000000000 : ℝ)*base66 + (1021573389506653/80000000000000000000000000000 : ℝ)*base67 + (422016398066653/80000000000000000000000000000 : ℝ)*base69 + (93132372066653/80000000000000000000000000000 : ℝ)*base71 + (225381136146653/40000000000000000000000000000 : ℝ)*base73 + (11236046706653/80000000000000000000000000000 : ℝ)*base75 + (228240721826653/80000000000000000000000000000 : ℝ)*base77 + (274856206946653/80000000000000000000000000000 : ℝ)*base79 + (86280133093347/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (14000287/1250000000000000000000 : ℝ)*base90 + (14000287/1250000000000000000000 : ℝ)*base92 + (14000287/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3377953166501019369/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (84357/2500000000000 : ℝ)*(base1) + (428837107/50000000000000 : ℝ)*(base19) + (190804779/20000000000000 : ℝ)*(base23) + (68563669/25000000000000 : ℝ)*(base32) + (91783399/50000000000000 : ℝ)*(upper3) + (85310328328047/10000000000000 : ℝ)*(major0) + (85310328328047/10000000000000 : ℝ)*(major1) + (85310328328047/10000000000000 : ℝ)*(major2) + (2094214943/100000000000000 : ℝ)*(sp1) + (1458693661/50000000000000 : ℝ)*(sp2) + (123272760493949/10000000000000 : ℝ)*(sp4) + (308181162419013/25000000000000 : ℝ)*(sp5) + (154090466269249/12500000000000 : ℝ)*(sp6) + (118369615542473/25000000000000 : ℝ)*(sp7) + (7398105309357/1562500000000 : ℝ)*(f.failure) + (123272760156521/10000000000000 : ℝ)*(f.sum) + (430821105323/20000000000000000000000000000 : ℝ)*base65 + (109984102614677/40000000000000000000000000000 : ℝ)*base68 + (208216185323/40000000000000000000000000000 : ℝ)*base69 + (9761201334677/40000000000000000000000000000 : ℝ)*base72 + (59887328014677/20000000000000000000000000000 : ℝ)*base74 + (299270805865323/40000000000000000000000000000 : ℝ)*base75 + (212865394745323/40000000000000000000000000000 : ℝ)*base77 + (35651294825323/40000000000000000000000000000 : ℝ)*base79 + (37172770174677/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (59733/78125000000000000000 : ℝ)*base89 + (59733/78125000000000000000 : ℝ)*base91 + (59733/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1655_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (247/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23251/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1655_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1655_s1_0 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-793876701/5000000000 : ℝ)*x 0 + (5492568997/10000000000 : ℝ)*x 1 + (1285993499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (793876701/5000000000 : ℝ)^4939 ≤ (981163486247/10000000000000 : ℝ)^3915 := by
    have hnat : (793876701 : ℕ)^4939*10000000000000^3915 ≤ 981163486247^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793876701 5000000000 981163486247 10000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492568997/10000000000 : ℝ)^4939 ≤ (9391645561361/20000000000000 : ℝ)^3915 := by
    have hnat : (5492568997 : ℕ)^4939*20000000000000^3915 ≤ 9391645561361^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492568997 10000000000 9391645561361 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285993499/2500000000 : ℝ)^4939 ≤ (5403767163999/12500000000000 : ℝ)^3915 := by
    have hnat : (1285993499 : ℕ)^4939*12500000000000^3915 ≤ 5403767163999^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285993499 2500000000 5403767163999 12500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-793876701/5000000000 : ℝ), (5492568997/10000000000 : ℝ), (1285993499/2500000000 : ℝ)] ![(981163486247/10000000000000 : ℝ), (9391645561361/20000000000000 : ℝ), (5403767163999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-793876701/5000000000 : ℝ)|^4939 ≤ (981163486247/10000000000000 : ℝ)^3915
        have hw : |(-793876701/5000000000 : ℝ)|=(793876701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492568997/10000000000 : ℝ)|^4939 ≤ (9391645561361/20000000000000 : ℝ)^3915
        have hw : |(5492568997/10000000000 : ℝ)|=(5492568997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1285993499/2500000000 : ℝ)|^4939 ≤ (5403767163999/12500000000000 : ℝ)^3915
        have hw : |(1285993499/2500000000 : ℝ)|=(1285993499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s1_1 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359335227/10000000000 : ℝ)*x 0 + (-1768864281/10000000000 : ℝ)*x 1 + (1028794767/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359335227/10000000000 : ℝ)^4939 ≤ (22762905344481/50000000000000 : ℝ)^3915 := by
    have hnat : (5359335227 : ℕ)^4939*50000000000000^3915 ≤ 22762905344481^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359335227 10000000000 22762905344481 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1768864281/10000000000 : ℝ)^4939 ≤ (5622026847/50000000000 : ℝ)^3915 := by
    have hnat : (1768864281 : ℕ)^4939*50000000000^3915 ≤ 5622026847^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768864281 10000000000 5622026847 50000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028794767/2000000000 : ℝ)^4939 ≤ (43230135605041/100000000000000 : ℝ)^3915 := by
    have hnat : (1028794767 : ℕ)^4939*100000000000000^3915 ≤ 43230135605041^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028794767 2000000000 43230135605041 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359335227/10000000000 : ℝ), (-1768864281/10000000000 : ℝ), (1028794767/2000000000 : ℝ)] ![(22762905344481/50000000000000 : ℝ), (5622026847/50000000000 : ℝ), (43230135605041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359335227/10000000000 : ℝ)|^4939 ≤ (22762905344481/50000000000000 : ℝ)^3915
        have hw : |(5359335227/10000000000 : ℝ)|=(5359335227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1768864281/10000000000 : ℝ)|^4939 ≤ (5622026847/50000000000 : ℝ)^3915
        have hw : |(-1768864281/10000000000 : ℝ)|=(1768864281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028794767/2000000000 : ℝ)|^4939 ≤ (43230135605041/100000000000000 : ℝ)^3915
        have hw : |(1028794767/2000000000 : ℝ)|=(1028794767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s1_2 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133983367/250000000 : ℝ)*x 0 + (2571987211/5000000000 : ℝ)*x 1 + (-1768864237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133983367/250000000 : ℝ)^4939 ≤ (45525804827023/100000000000000 : ℝ)^3915 := by
    have hnat : (133983367 : ℕ)^4939*100000000000000^3915 ≤ 45525804827023^3915*250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133983367 250000000 45525804827023 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571987211/5000000000 : ℝ)^4939 ≤ (1080753545713/2500000000000 : ℝ)^3915 := by
    have hnat : (2571987211 : ℕ)^4939*2500000000000^3915 ≤ 1080753545713^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571987211 5000000000 1080753545713 2500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768864237/10000000000 : ℝ)^4939 ≤ (11244053341151/100000000000000 : ℝ)^3915 := by
    have hnat : (1768864237 : ℕ)^4939*100000000000000^3915 ≤ 11244053341151^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768864237 10000000000 11244053341151 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133983367/250000000 : ℝ), (2571987211/5000000000 : ℝ), (-1768864237/10000000000 : ℝ)] ![(45525804827023/100000000000000 : ℝ), (1080753545713/2500000000000 : ℝ), (11244053341151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133983367/250000000 : ℝ)|^4939 ≤ (45525804827023/100000000000000 : ℝ)^3915
        have hw : |(133983367/250000000 : ℝ)|=(133983367/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571987211/5000000000 : ℝ)|^4939 ≤ (1080753545713/2500000000000 : ℝ)^3915
        have hw : |(2571987211/5000000000 : ℝ)|=(2571987211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1768864237/10000000000 : ℝ)|^4939 ≤ (11244053341151/100000000000000 : ℝ)^3915
        have hw : |(-1768864237/10000000000 : ℝ)|=(1768864237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s1_3 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4169884827/10000000000 : ℝ)*x 0 + (746766379/2000000000 : ℝ)*x 1 + (2320709091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169884827/10000000000 : ℝ)^4939 ≤ (8292861946737/25000000000000 : ℝ)^3915 := by
    have hnat : (4169884827 : ℕ)^4939*25000000000000^3915 ≤ 8292861946737^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169884827 10000000000 8292861946737 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746766379/2000000000 : ℝ)^4939 ≤ (28856813273661/100000000000000 : ℝ)^3915 := by
    have hnat : (746766379 : ℕ)^4939*100000000000000^3915 ≤ 28856813273661^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746766379 2000000000 28856813273661 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2320709091/5000000000 : ℝ)^4939 ≤ (18985869460381/50000000000000 : ℝ)^3915 := by
    have hnat : (2320709091 : ℕ)^4939*50000000000000^3915 ≤ 18985869460381^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320709091 5000000000 18985869460381 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169884827/10000000000 : ℝ), (746766379/2000000000 : ℝ), (2320709091/5000000000 : ℝ)] ![(8292861946737/25000000000000 : ℝ), (28856813273661/100000000000000 : ℝ), (18985869460381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169884827/10000000000 : ℝ)|^4939 ≤ (8292861946737/25000000000000 : ℝ)^3915
        have hw : |(4169884827/10000000000 : ℝ)|=(4169884827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746766379/2000000000 : ℝ)|^4939 ≤ (28856813273661/100000000000000 : ℝ)^3915
        have hw : |(746766379/2000000000 : ℝ)|=(746766379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2320709091/5000000000 : ℝ)|^4939 ≤ (18985869460381/50000000000000 : ℝ)^3915
        have hw : |(2320709091/5000000000 : ℝ)|=(2320709091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s1_4 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-793951501/5000000000 : ℝ)*x 0 + (5147483911/10000000000 : ℝ)*x 1 + (5489010023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (793951501/5000000000 : ℝ)^4939 ≤ (981280114167/10000000000000 : ℝ)^3915 := by
    have hnat : (793951501 : ℕ)^4939*10000000000000^3915 ≤ 981280114167^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793951501 5000000000 981280114167 10000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5147483911/10000000000 : ℝ)^4939 ≤ (2163367668867/5000000000000 : ℝ)^3915 := by
    have hnat : (5147483911 : ℕ)^4939*5000000000000^3915 ≤ 2163367668867^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147483911 10000000000 2163367668867 5000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489010023/10000000000 : ℝ)^4939 ≤ (11729961366821/25000000000000 : ℝ)^3915 := by
    have hnat : (5489010023 : ℕ)^4939*25000000000000^3915 ≤ 11729961366821^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489010023 10000000000 11729961366821 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-793951501/5000000000 : ℝ), (5147483911/10000000000 : ℝ), (5489010023/10000000000 : ℝ)] ![(981280114167/10000000000000 : ℝ), (2163367668867/5000000000000 : ℝ), (11729961366821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-793951501/5000000000 : ℝ)|^4939 ≤ (981280114167/10000000000000 : ℝ)^3915
        have hw : |(-793951501/5000000000 : ℝ)|=(793951501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5147483911/10000000000 : ℝ)|^4939 ≤ (2163367668867/5000000000000 : ℝ)^3915
        have hw : |(5147483911/10000000000 : ℝ)|=(5147483911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489010023/10000000000 : ℝ)|^4939 ≤ (11729961366821/25000000000000 : ℝ)^3915
        have hw : |(5489010023/10000000000 : ℝ)|=(5489010023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s1_5 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266082287/10000000000 : ℝ)*x 0 + (-1423828257/10000000000 : ℝ)*x 1 + (1097802013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266082287/10000000000 : ℝ)^4939 ≤ (5566093377973/12500000000000 : ℝ)^3915 := by
    have hnat : (5266082287 : ℕ)^4939*12500000000000^3915 ≤ 5566093377973^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266082287 10000000000 5566093377973 12500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1423828257/10000000000 : ℝ)^4939 ≤ (8551407051147/100000000000000 : ℝ)^3915 := by
    have hnat : (1423828257 : ℕ)^4939*100000000000000^3915 ≤ 8551407051147^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423828257 10000000000 8551407051147 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097802013/2000000000 : ℝ)^4939 ≤ (23459922960101/50000000000000 : ℝ)^3915 := by
    have hnat : (1097802013 : ℕ)^4939*50000000000000^3915 ≤ 23459922960101^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097802013 2000000000 23459922960101 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266082287/10000000000 : ℝ), (-1423828257/10000000000 : ℝ), (1097802013/2000000000 : ℝ)] ![(5566093377973/12500000000000 : ℝ), (8551407051147/100000000000000 : ℝ), (23459922960101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266082287/10000000000 : ℝ)|^4939 ≤ (5566093377973/12500000000000 : ℝ)^3915
        have hw : |(5266082287/10000000000 : ℝ)|=(5266082287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1423828257/10000000000 : ℝ)|^4939 ≤ (8551407051147/100000000000000 : ℝ)^3915
        have hw : |(-1423828257/10000000000 : ℝ)|=(1423828257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097802013/2000000000 : ℝ)|^4939 ≤ (23459922960101/50000000000000 : ℝ)^3915
        have hw : |(1097802013/2000000000 : ℝ)|=(1097802013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s1_6 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053216413/2000000000 : ℝ)*x 0 + (1372252591/2500000000 : ℝ)*x 1 + (-711914071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053216413/2000000000 : ℝ)^4939 ≤ (44528744655613/100000000000000 : ℝ)^3915 := by
    have hnat : (1053216413 : ℕ)^4939*100000000000000^3915 ≤ 44528744655613^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053216413 2000000000 44528744655613 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372252591/2500000000 : ℝ)^4939 ≤ (46919849144543/100000000000000 : ℝ)^3915 := by
    have hnat : (1372252591 : ℕ)^4939*100000000000000^3915 ≤ 46919849144543^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372252591 2500000000 46919849144543 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (711914071/5000000000 : ℝ)^4939 ≤ (2137851544953/25000000000000 : ℝ)^3915 := by
    have hnat : (711914071 : ℕ)^4939*25000000000000^3915 ≤ 2137851544953^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711914071 5000000000 2137851544953 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053216413/2000000000 : ℝ), (1372252591/2500000000 : ℝ), (-711914071/5000000000 : ℝ)] ![(44528744655613/100000000000000 : ℝ), (46919849144543/100000000000000 : ℝ), (2137851544953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053216413/2000000000 : ℝ)|^4939 ≤ (44528744655613/100000000000000 : ℝ)^3915
        have hw : |(1053216413/2000000000 : ℝ)|=(1053216413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372252591/2500000000 : ℝ)|^4939 ≤ (46919849144543/100000000000000 : ℝ)^3915
        have hw : |(1372252591/2500000000 : ℝ)|=(1372252591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-711914071/5000000000 : ℝ)|^4939 ≤ (2137851544953/25000000000000 : ℝ)^3915
        have hw : |(-711914071/5000000000 : ℝ)|=(711914071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s1_7 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65160541/156250000 : ℝ)*x 0 + (2316140171/5000000000 : ℝ)*x 1 + (3743098139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65160541/156250000 : ℝ)^4939 ≤ (33175359720131/100000000000000 : ℝ)^3915 := by
    have hnat : (65160541 : ℕ)^4939*100000000000000^3915 ≤ 33175359720131^3915*156250000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65160541 156250000 33175359720131 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2316140171/5000000000 : ℝ)^4939 ≤ (37877452595751/100000000000000 : ℝ)^3915 := by
    have hnat : (2316140171 : ℕ)^4939*100000000000000^3915 ≤ 37877452595751^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316140171 5000000000 37877452595751 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3743098139/10000000000 : ℝ)^4939 ≤ (14473593838489/50000000000000 : ℝ)^3915 := by
    have hnat : (3743098139 : ℕ)^4939*50000000000000^3915 ≤ 14473593838489^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743098139 10000000000 14473593838489 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65160541/156250000 : ℝ), (2316140171/5000000000 : ℝ), (3743098139/10000000000 : ℝ)] ![(33175359720131/100000000000000 : ℝ), (37877452595751/100000000000000 : ℝ), (14473593838489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65160541/156250000 : ℝ)|^4939 ≤ (33175359720131/100000000000000 : ℝ)^3915
        have hw : |(65160541/156250000 : ℝ)|=(65160541/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2316140171/5000000000 : ℝ)|^4939 ≤ (37877452595751/100000000000000 : ℝ)^3915
        have hw : |(2316140171/5000000000 : ℝ)|=(2316140171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3743098139/10000000000 : ℝ)|^4939 ≤ (14473593838489/50000000000000 : ℝ)^3915
        have hw : |(3743098139/10000000000 : ℝ)|=(3743098139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1655_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23251/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (247/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (307/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17233/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23251/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (247/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23251/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (247/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23251/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (247/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23251/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (247/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23251/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (247/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23251/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (247/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (247/5000 : ℝ) ^ (4935/1024 : ℝ) ≤ (25328026102689/50000000000000000000 : ℝ) := by
    have hpowers : (247/5000 : ℝ)^4935 ≤ (25328026102689/50000000000000000000 : ℝ)^1024 := by
      have hnat : (247 : ℕ)^4935*50000000000000000000^1024 ≤ 25328026102689^1024*5000^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        247 5000 25328026102689 50000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (247/5000 : ℝ)) (X := (25328026102689/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23251/100000 : ℝ) ^ (4935/1024 : ℝ) ≤ (88444210313181951/100000000000000000000 : ℝ) := by
    have hpowers : (23251/100000 : ℝ)^4935 ≤ (88444210313181951/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23251 : ℕ)^4935*100000000000000000000^1024 ≤ 88444210313181951^1024*100000^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23251 100000 88444210313181951 100000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23251/100000 : ℝ)) (X := (88444210313181951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000025328026102689/25000000000000000000 : ℝ) ≤ (10000002102199661/10000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (25000025328026102689/25000000000000000000 : ℝ)^1024 ≤ (10000002102199661/10000000000000000 : ℝ)^4935 := by
      have hnat : (25000025328026102689 : ℕ)^1024*10000000000000000^4935 ≤ 10000002102199661^4935*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000025328026102689 25000000000000000000 10000002102199661 10000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002102199661/10000000000000000 : ℝ)) (X := (25000025328026102689/25000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100088494866365387329/100000000000000000000 : ℝ) ≤ (5000917801250229/5000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (100088494866365387329/100000000000000000000 : ℝ)^1024 ≤ (5000917801250229/5000000000000000 : ℝ)^4935 := by
      have hnat : (100088494866365387329 : ℕ)^1024*5000000000000000^4935 ≤ 5000917801250229^4935*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100088494866365387329 100000000000000000000 5000917801250229 5000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000917801250229/5000000000000000 : ℝ)) (X := (100088494866365387329/100000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50088444210313181951/50000000000000000000 : ℝ) ≤ (2000733820560251/2000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (50088444210313181951/50000000000000000000 : ℝ)^1024 ≤ (2000733820560251/2000000000000000 : ℝ)^4935 := by
      have hnat : (50088444210313181951 : ℕ)^1024*2000000000000000^4935 ≤ 2000733820560251^4935*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50088444210313181951 50000000000000000000 2000733820560251 2000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000733820560251/2000000000000000 : ℝ)) (X := (50088444210313181951/50000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25328026102689/50000000000000000000 : ℝ) ≤ ((183091923510406118211/183110000000000000000 : ℝ)+2*(1833500300797/1831100000000000 : ℝ)*(247/5000 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (183091923510406118211/183110000000000000000 : ℝ)+2*(1833500300797/1831100000000000 : ℝ)*(247/5000 : ℝ)=(10000002102199661/10000000000000000 : ℝ) by norm_num, show 1+2*(25328026102689/50000000000000000000 : ℝ)=(25000025328026102689/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(88444210313181951/100000000000000000000 : ℝ)+(25328026102689/50000000000000000000 : ℝ) ≤ ((183091923510406118211/183110000000000000000 : ℝ)+(1833500300797/1831100000000000 : ℝ)*((23251/100000 : ℝ)+(247/5000 : ℝ)))^(4935/1024 : ℝ) := by
    rw [show (183091923510406118211/183110000000000000000 : ℝ)+(1833500300797/1831100000000000 : ℝ)*((23251/100000 : ℝ)+(247/5000 : ℝ))=(5000917801250229/5000000000000000 : ℝ) by norm_num, show 1+(88444210313181951/100000000000000000000 : ℝ)+(25328026102689/50000000000000000000 : ℝ)=(100088494866365387329/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(88444210313181951/100000000000000000000 : ℝ) ≤ ((183091923510406118211/183110000000000000000 : ℝ)+2*(1833500300797/1831100000000000 : ℝ)*(23251/100000 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (183091923510406118211/183110000000000000000 : ℝ)+2*(1833500300797/1831100000000000 : ℝ)*(23251/100000 : ℝ)=(2000733820560251/2000000000000000 : ℝ) by norm_num, show 1+2*(88444210313181951/100000000000000000000 : ℝ)=(50088444210313181951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (183091923510406118211/183110000000000000000 : ℝ)*(X 1 0+X 2 0)+(1833500300797/1831100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (247/5000 : ℝ)) (hi := (23251/100000 : ℝ)) (c := (183091923510406118211/183110000000000000000 : ℝ)) (alpha := (1833500300797/1831100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (183091923510406118211/183110000000000000000 : ℝ)*(X 0 1+X 2 1)+(1833500300797/1831100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (247/5000 : ℝ)) (hi := (23251/100000 : ℝ)) (c := (183091923510406118211/183110000000000000000 : ℝ)) (alpha := (1833500300797/1831100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (183091923510406118211/183110000000000000000 : ℝ)*(X 0 2+X 1 2)+(1833500300797/1831100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (247/5000 : ℝ)) (hi := (23251/100000 : ℝ)) (c := (183091923510406118211/183110000000000000000 : ℝ)) (alpha := (1833500300797/1831100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-793876701/5000000000 : ℝ)*X 0 0+(5492568997/10000000000 : ℝ)*X 0 1+(1285993499/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359335227/10000000000 : ℝ)*X 1 0+(-1768864281/10000000000 : ℝ)*X 1 1+(1028794767/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133983367/250000000 : ℝ)*X 2 0+(2571987211/5000000000 : ℝ)*X 2 1+(-1768864237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4169884827/10000000000 : ℝ)*X 0 0+(746766379/2000000000 : ℝ)*X 0 1+(2320709091/5000000000 : ℝ)*X 0 2+(4169884827/10000000000 : ℝ)*X 1 0+(746766379/2000000000 : ℝ)*X 1 1+(2320709091/5000000000 : ℝ)*X 1 2+(4169884827/10000000000 : ℝ)*X 2 0+(746766379/2000000000 : ℝ)*X 2 1+(2320709091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-793951501/5000000000 : ℝ)*X 0 0+(5147483911/10000000000 : ℝ)*X 0 1+(5489010023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266082287/10000000000 : ℝ)*X 1 0+(-1423828257/10000000000 : ℝ)*X 1 1+(1097802013/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1053216413/2000000000 : ℝ)*X 2 0+(1372252591/2500000000 : ℝ)*X 2 1+(-711914071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((65160541/156250000 : ℝ)*X 0 0+(2316140171/5000000000 : ℝ)*X 0 1+(3743098139/10000000000 : ℝ)*X 0 2+(65160541/156250000 : ℝ)*X 1 0+(2316140171/5000000000 : ℝ)*X 1 1+(3743098139/10000000000 : ℝ)*X 1 2+(65160541/156250000 : ℝ)*X 2 0+(2316140171/5000000000 : ℝ)*X 2 1+(3743098139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20058355497361451358521555997/2288875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1037219503/50000000000000 : ℝ)*(base19) + (337242627/20000000000000 : ℝ)*(base23) + (306937041/100000000000000 : ℝ)*(upper3) + (2557279/5000000000000 : ℝ)*(upper4) + (223172039/100000000000000 : ℝ)*(upper5) + (496317137290703/25000000000000 : ℝ)*(major0) + (496317137290703/25000000000000 : ℝ)*(major1) + (496317137290703/25000000000000 : ℝ)*(major2) + (717169716446089/25000000000000 : ℝ)*(sp0) + (573739150510359/20000000000000 : ℝ)*(sp1) + (2868696140777667/100000000000000 : ℝ)*(sp2) + (550915531065799/50000000000000 : ℝ)*(sp3) + (9480603223/50000000000000 : ℝ)*(sp4) + (7917089471/100000000000000 : ℝ)*(sp7) + (1101838979221069/100000000000000 : ℝ)*(f.failure) + (1434348913495401/50000000000000 : ℝ)*(f.sum) + (44138089953683/45777500000000000000000000000 : ℝ)*base66 + (52462901139989107667/4577750000000000000000000000000000 : ℝ)*base68 + (71417650021588857667/4577750000000000000000000000000000 : ℝ)*base70 + (26301661337672857667/4577750000000000000000000000000000 : ℝ)*base72 + (367193493173671/91555000000000000000000000000 : ℝ)*base74 + (8649688945139107667/4577750000000000000000000000000000 : ℝ)*base76 + (39288779722309107667/4577750000000000000000000000000000 : ℝ)*base78 + (45363416233338107667/4577750000000000000000000000000000 : ℝ)*base80 + (111069225300133/45777500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7180961/5000000000000000000000 : ℝ)*base89 + (7180961/5000000000000000000000 : ℝ)*base91 + (7180961/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (425114955208835401438457211/91555000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48757901/5000000000000 : ℝ)*(base19) + (959382099/100000000000000 : ℝ)*(base23) + (40667221/100000000000000 : ℝ)*(upper2) + (65226309/50000000000000 : ℝ)*(upper3) + (54670701/50000000000000 : ℝ)*(upper5) + (20263307700333/1000000000000 : ℝ)*(major0) + (20263307700333/1000000000000 : ℝ)*(major1) + (20263307700333/1000000000000 : ℝ)*(major2) + (1864951511/20000000000000 : ℝ)*(sp1) + (43138643/390625000000 : ℝ)*(sp2) + (2928032564590813/100000000000000 : ℝ)*(sp4) + (2928022264675239/100000000000000 : ℝ)*(sp5) + (1464010280858053/50000000000000 : ℝ)*(sp6) + (56231441034999/5000000000000 : ℝ)*(sp7) + (56231441034999/5000000000000 : ℝ)*(f.failure) + (2928032564590813/100000000000000 : ℝ)*(f.sum) + (12854382145993/9155500000000000000000000000 : ℝ)*base65 + (630602837044834263/183110000000000000000000000000000 : ℝ)*base67 + (1933420760974074263/183110000000000000000000000000000 : ℝ)*base69 + (342793048567384263/183110000000000000000000000000000 : ℝ)*base71 + (6793182496091/9155500000000000000000000000 : ℝ)*base74 + (632890656667635737/183110000000000000000000000000000 : ℝ)*base76 + (1413070494648664263/183110000000000000000000000000000 : ℝ)*base77 + (164439819973035737/183110000000000000000000000000000 : ℝ)*base80 + (6234110913093/4577750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (673869/250000000000000000000 : ℝ)*base90 + (673869/250000000000000000000 : ℝ)*base92 + (673869/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1655_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23251/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (247/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (307/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17233/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1655_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1655_s2_0 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-798295943/5000000000 : ℝ)*x 0 + (544932191/1000000000 : ℝ)*x 1 + (207255381/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798295943/5000000000 : ℝ)^4939 ≤ (247014719663/2500000000000 : ℝ)^3915 := by
    have hnat : (798295943 : ℕ)^4939*2500000000000^3915 ≤ 247014719663^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798295943 5000000000 247014719663 2500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544932191/1000000000 : ℝ)^4939 ≤ (46492264204809/100000000000000 : ℝ)^3915 := by
    have hnat : (544932191 : ℕ)^4939*100000000000000^3915 ≤ 46492264204809^3915*1000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544932191 1000000000 46492264204809 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207255381/400000000 : ℝ)^4939 ≤ (21813573493781/50000000000000 : ℝ)^3915 := by
    have hnat : (207255381 : ℕ)^4939*50000000000000^3915 ≤ 21813573493781^3915*400000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207255381 400000000 21813573493781 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-798295943/5000000000 : ℝ), (544932191/1000000000 : ℝ), (207255381/400000000 : ℝ)] ![(247014719663/2500000000000 : ℝ), (46492264204809/100000000000000 : ℝ), (21813573493781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-798295943/5000000000 : ℝ)|^4939 ≤ (247014719663/2500000000000 : ℝ)^3915
        have hw : |(-798295943/5000000000 : ℝ)|=(798295943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544932191/1000000000 : ℝ)|^4939 ≤ (46492264204809/100000000000000 : ℝ)^3915
        have hw : |(544932191/1000000000 : ℝ)|=(544932191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207255381/400000000 : ℝ)|^4939 ≤ (21813573493781/50000000000000 : ℝ)^3915
        have hw : |(207255381/400000000 : ℝ)|=(207255381/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s2_1 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673934557/5000000000 : ℝ)*x 0 + (-867293627/5000000000 : ℝ)*x 1 + (5181385317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673934557/5000000000 : ℝ)^4939 ≤ (22701484094407/50000000000000 : ℝ)^3915 := by
    have hnat : (2673934557 : ℕ)^4939*50000000000000^3915 ≤ 22701484094407^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673934557 5000000000 22701484094407 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (867293627/5000000000 : ℝ)^4939 ≤ (10969876393591/100000000000000 : ℝ)^3915 := by
    have hnat : (867293627 : ℕ)^4939*100000000000000^3915 ≤ 10969876393591^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867293627 5000000000 10969876393591 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181385317/10000000000 : ℝ)^4939 ≤ (21813577700209/50000000000000 : ℝ)^3915 := by
    have hnat : (5181385317 : ℕ)^4939*50000000000000^3915 ≤ 21813577700209^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181385317 10000000000 21813577700209 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673934557/5000000000 : ℝ), (-867293627/5000000000 : ℝ), (5181385317/10000000000 : ℝ)] ![(22701484094407/50000000000000 : ℝ), (10969876393591/100000000000000 : ℝ), (21813577700209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673934557/5000000000 : ℝ)|^4939 ≤ (22701484094407/50000000000000 : ℝ)^3915
        have hw : |(2673934557/5000000000 : ℝ)|=(2673934557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-867293627/5000000000 : ℝ)|^4939 ≤ (10969876393591/100000000000000 : ℝ)^3915
        have hw : |(-867293627/5000000000 : ℝ)|=(867293627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181385317/10000000000 : ℝ)|^4939 ≤ (21813577700209/50000000000000 : ℝ)^3915
        have hw : |(5181385317/10000000000 : ℝ)|=(5181385317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s2_2 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336967449/2500000000 : ℝ)*x 0 + (259069229/500000000 : ℝ)*x 1 + (-43364683/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336967449/2500000000 : ℝ)^4939 ≤ (45402975493391/100000000000000 : ℝ)^3915 := by
    have hnat : (1336967449 : ℕ)^4939*100000000000000^3915 ≤ 45402975493391^3915*2500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336967449 2500000000 45402975493391 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259069229/500000000 : ℝ)^4939 ≤ (10906786892947/25000000000000 : ℝ)^3915 := by
    have hnat : (259069229 : ℕ)^4939*25000000000000^3915 ≤ 10906786892947^3915*500000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259069229 500000000 10906786892947 25000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43364683/250000000 : ℝ)^4939 ≤ (5484938460081/50000000000000 : ℝ)^3915 := by
    have hnat : (43364683 : ℕ)^4939*50000000000000^3915 ≤ 5484938460081^3915*250000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43364683 250000000 5484938460081 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336967449/2500000000 : ℝ), (259069229/500000000 : ℝ), (-43364683/250000000 : ℝ)] ![(45402975493391/100000000000000 : ℝ), (10906786892947/25000000000000 : ℝ), (5484938460081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336967449/2500000000 : ℝ)|^4939 ≤ (45402975493391/100000000000000 : ℝ)^3915
        have hw : |(1336967449/2500000000 : ℝ)|=(1336967449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259069229/500000000 : ℝ)|^4939 ≤ (10906786892947/25000000000000 : ℝ)^3915
        have hw : |(259069229/500000000 : ℝ)|=(259069229/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43364683/250000000 : ℝ)|^4939 ≤ (5484938460081/50000000000000 : ℝ)^3915
        have hw : |(-43364683/250000000 : ℝ)|=(43364683/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s2_3 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4176481297/10000000000 : ℝ)*x 0 + (767634513/2000000000 : ℝ)*x 1 + (4535760211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176481297/10000000000 : ℝ)^4939 ≤ (6647532332939/20000000000000 : ℝ)^3915 := by
    have hnat : (4176481297 : ℕ)^4939*20000000000000^3915 ≤ 6647532332939^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176481297 10000000000 6647532332939 20000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (767634513/2000000000 : ℝ)^4939 ≤ (29877818606823/100000000000000 : ℝ)^3915 := by
    have hnat : (767634513 : ℕ)^4939*100000000000000^3915 ≤ 29877818606823^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767634513 2000000000 29877818606823 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4535760211/10000000000 : ℝ)^4939 ≤ (36884519708027/100000000000000 : ℝ)^3915 := by
    have hnat : (4535760211 : ℕ)^4939*100000000000000^3915 ≤ 36884519708027^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535760211 10000000000 36884519708027 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176481297/10000000000 : ℝ), (767634513/2000000000 : ℝ), (4535760211/10000000000 : ℝ)] ![(6647532332939/20000000000000 : ℝ), (29877818606823/100000000000000 : ℝ), (36884519708027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176481297/10000000000 : ℝ)|^4939 ≤ (6647532332939/20000000000000 : ℝ)^3915
        have hw : |(4176481297/10000000000 : ℝ)|=(4176481297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(767634513/2000000000 : ℝ)|^4939 ≤ (29877818606823/100000000000000 : ℝ)^3915
        have hw : |(767634513/2000000000 : ℝ)|=(767634513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4535760211/10000000000 : ℝ)|^4939 ≤ (36884519708027/100000000000000 : ℝ)^3915
        have hw : |(4535760211/10000000000 : ℝ)|=(4535760211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s2_4 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1596659743/10000000000 : ℝ)*x 0 + (1036692789/2000000000 : ℝ)*x 1 + (5447220299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1596659743/10000000000 : ℝ)^4939 ≤ (9881118563687/100000000000000 : ℝ)^3915 := by
    have hnat : (1596659743 : ℕ)^4939*100000000000000^3915 ≤ 9881118563687^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596659743 10000000000 9881118563687 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036692789/2000000000 : ℝ)^4939 ≤ (43649236353859/100000000000000 : ℝ)^3915 := by
    have hnat : (1036692789 : ℕ)^4939*100000000000000^3915 ≤ 43649236353859^3915*2000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036692789 2000000000 43649236353859 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447220299/10000000000 : ℝ)^4939 ≤ (46469645073653/100000000000000 : ℝ)^3915 := by
    have hnat : (5447220299 : ℕ)^4939*100000000000000^3915 ≤ 46469645073653^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447220299 10000000000 46469645073653 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1596659743/10000000000 : ℝ), (1036692789/2000000000 : ℝ), (5447220299/10000000000 : ℝ)] ![(9881118563687/100000000000000 : ℝ), (43649236353859/100000000000000 : ℝ), (46469645073653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1596659743/10000000000 : ℝ)|^4939 ≤ (9881118563687/100000000000000 : ℝ)^3915
        have hw : |(-1596659743/10000000000 : ℝ)|=(1596659743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036692789/2000000000 : ℝ)|^4939 ≤ (43649236353859/100000000000000 : ℝ)^3915
        have hw : |(1036692789/2000000000 : ℝ)|=(1036692789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447220299/10000000000 : ℝ)|^4939 ≤ (46469645073653/100000000000000 : ℝ)^3915
        have hw : |(5447220299/10000000000 : ℝ)|=(5447220299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s2_5 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527624431/1000000000 : ℝ)*x 0 + (-1468751491/10000000000 : ℝ)*x 1 + (2723610223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527624431/1000000000 : ℝ)^4939 ≤ (5579647138729/12500000000000 : ℝ)^3915 := by
    have hnat : (527624431 : ℕ)^4939*12500000000000^3915 ≤ 5579647138729^3915*1000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527624431 1000000000 5579647138729 12500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1468751491/10000000000 : ℝ)^4939 ≤ (8893176215343/100000000000000 : ℝ)^3915 := by
    have hnat : (1468751491 : ℕ)^4939*100000000000000^3915 ≤ 8893176215343^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468751491 10000000000 8893176215343 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723610223/5000000000 : ℝ)^4939 ≤ (46469646655699/100000000000000 : ℝ)^3915 := by
    have hnat : (2723610223 : ℕ)^4939*100000000000000^3915 ≤ 46469646655699^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723610223 5000000000 46469646655699 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527624431/1000000000 : ℝ), (-1468751491/10000000000 : ℝ), (2723610223/5000000000 : ℝ)] ![(5579647138729/12500000000000 : ℝ), (8893176215343/100000000000000 : ℝ), (46469646655699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527624431/1000000000 : ℝ)|^4939 ≤ (5579647138729/12500000000000 : ℝ)^3915
        have hw : |(527624431/1000000000 : ℝ)|=(527624431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1468751491/10000000000 : ℝ)|^4939 ≤ (8893176215343/100000000000000 : ℝ)^3915
        have hw : |(-1468751491/10000000000 : ℝ)|=(1468751491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723610223/5000000000 : ℝ)|^4939 ≤ (46469646655699/100000000000000 : ℝ)^3915
        have hw : |(2723610223/5000000000 : ℝ)|=(2723610223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s2_6 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164882643/312500000 : ℝ)*x 0 + (2723610031/5000000000 : ℝ)*x 1 + (-1468751661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164882643/312500000 : ℝ)^4939 ≤ (22318589974401/50000000000000 : ℝ)^3915 := by
    have hnat : (164882643 : ℕ)^4939*50000000000000^3915 ≤ 22318589974401^3915*312500000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164882643 312500000 22318589974401 50000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723610031/5000000000 : ℝ)^4939 ≤ (363044082211/781250000000 : ℝ)^3915 := by
    have hnat : (2723610031 : ℕ)^4939*781250000000^3915 ≤ 363044082211^3915*5000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723610031 5000000000 363044082211 781250000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1468751661/10000000000 : ℝ)^4939 ≤ (8893177513911/100000000000000 : ℝ)^3915 := by
    have hnat : (1468751661 : ℕ)^4939*100000000000000^3915 ≤ 8893177513911^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468751661 10000000000 8893177513911 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164882643/312500000 : ℝ), (2723610031/5000000000 : ℝ), (-1468751661/10000000000 : ℝ)] ![(22318589974401/50000000000000 : ℝ), (363044082211/781250000000 : ℝ), (8893177513911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164882643/312500000 : ℝ)|^4939 ≤ (22318589974401/50000000000000 : ℝ)^3915
        have hw : |(164882643/312500000 : ℝ)|=(164882643/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723610031/5000000000 : ℝ)|^4939 ≤ (363044082211/781250000000 : ℝ)^3915
        have hw : |(2723610031/5000000000 : ℝ)|=(2723610031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1468751661/10000000000 : ℝ)|^4939 ≤ (8893177513911/100000000000000 : ℝ)^3915
        have hw : |(-1468751661/10000000000 : ℝ)|=(1468751661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1655_s2_7 (p : ℝ) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4176659069/10000000000 : ℝ)*x 0 + (4530347801/10000000000 : ℝ)*x 1 + (3843642977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176659069/10000000000 : ℝ)^4939 ≤ (33239446478669/100000000000000 : ℝ)^3915 := by
    have hnat : (4176659069 : ℕ)^4939*100000000000000^3915 ≤ 33239446478669^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176659069 10000000000 33239446478669 100000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530347801/10000000000 : ℝ)^4939 ≤ (4603625367199/12500000000000 : ℝ)^3915 := by
    have hnat : (4530347801 : ℕ)^4939*12500000000000^3915 ≤ 4603625367199^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530347801 10000000000 4603625367199 12500000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3843642977/10000000000 : ℝ)^4939 ≤ (1496577527827/5000000000000 : ℝ)^3915 := by
    have hnat : (3843642977 : ℕ)^4939*5000000000000^3915 ≤ 1496577527827^3915*10000000000^4939 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843642977 10000000000 1496577527827 5000000000000 4939 3915 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4939/1024 : ℝ)) 4939 3915 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176659069/10000000000 : ℝ), (4530347801/10000000000 : ℝ), (3843642977/10000000000 : ℝ)] ![(33239446478669/100000000000000 : ℝ), (4603625367199/12500000000000 : ℝ), (1496577527827/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176659069/10000000000 : ℝ)|^4939 ≤ (33239446478669/100000000000000 : ℝ)^3915
        have hw : |(4176659069/10000000000 : ℝ)|=(4176659069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530347801/10000000000 : ℝ)|^4939 ≤ (4603625367199/12500000000000 : ℝ)^3915
        have hw : |(4530347801/10000000000 : ℝ)|=(4530347801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3843642977/10000000000 : ℝ)|^4939 ≤ (1496577527827/5000000000000 : ℝ)^3915
        have hw : |(3843642977/10000000000 : ℝ)|=(3843642977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1655_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (307/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1329/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16329/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17233/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (307/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17233/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (307/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17233/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (307/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17233/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (307/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17233/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (307/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17233/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (307/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (307/3125 : ℝ) ^ (4935/1024 : ℝ) ≤ (695775373547569/50000000000000000000 : ℝ) := by
    have hpowers : (307/3125 : ℝ)^4935 ≤ (695775373547569/50000000000000000000 : ℝ)^1024 := by
      have hnat : (307 : ℕ)^4935*50000000000000000000^1024 ≤ 695775373547569^1024*3125^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        307 3125 695775373547569 50000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (307/3125 : ℝ)) (X := (695775373547569/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17233/100000 : ℝ) ^ (4935/1024 : ℝ) ≤ (4176347041158163/20000000000000000000 : ℝ) := by
    have hpowers : (17233/100000 : ℝ)^4935 ≤ (4176347041158163/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17233 : ℕ)^4935*20000000000000000000^1024 ≤ 4176347041158163^1024*100000^4935 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17233 100000 4176347041158163 20000000000000000000 4935 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17233/100000 : ℝ)) (X := (4176347041158163/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000695775373547569/25000000000000000000 : ℝ) ≤ (10000057748014219/10000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (25000695775373547569/25000000000000000000 : ℝ)^1024 ≤ (10000057748014219/10000000000000000 : ℝ)^4935 := by
      have hnat : (25000695775373547569 : ℕ)^1024*10000000000000000^4935 ≤ 10000057748014219^4935*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000695775373547569 25000000000000000000 10000057748014219 10000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000057748014219/10000000000000000 : ℝ)) (X := (25000695775373547569/25000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022273285952885953/100000000000000000000 : ℝ) ≤ (10000462124257443/10000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (100022273285952885953/100000000000000000000 : ℝ)^1024 ≤ (10000462124257443/10000000000000000 : ℝ)^4935 := by
      have hnat : (100022273285952885953 : ℕ)^1024*10000000000000000^4935 ≤ 10000462124257443^4935*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022273285952885953 100000000000000000000 10000462124257443 10000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000462124257443/10000000000000000 : ℝ)) (X := (100022273285952885953/100000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004176347041158163/10000000000000000000 : ℝ) ≤ (10000866500500667/10000000000000000 : ℝ) ^ (4935/1024 : ℝ) := by
    have hpowers : (10004176347041158163/10000000000000000000 : ℝ)^1024 ≤ (10000866500500667/10000000000000000 : ℝ)^4935 := by
      have hnat : (10004176347041158163 : ℕ)^1024*10000000000000000^4935 ≤ 10000866500500667^4935*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004176347041158163 10000000000000000000 10000866500500667 10000000000000000 1024 4935 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000866500500667/10000000000000000 : ℝ)) (X := (10004176347041158163/10000000000000000000 : ℝ)) (by norm_num) 4935 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(695775373547569/50000000000000000000 : ℝ) ≤ ((74082482670610483419/74090000000000000000 : ℝ)+2*(50547030403/92612500000000 : ℝ)*(307/3125 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (74082482670610483419/74090000000000000000 : ℝ)+2*(50547030403/92612500000000 : ℝ)*(307/3125 : ℝ)=(10000057748014219/10000000000000000 : ℝ) by norm_num, show 1+2*(695775373547569/50000000000000000000 : ℝ)=(25000695775373547569/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4176347041158163/20000000000000000000 : ℝ)+(695775373547569/50000000000000000000 : ℝ) ≤ ((74082482670610483419/74090000000000000000 : ℝ)+(50547030403/92612500000000 : ℝ)*((17233/100000 : ℝ)+(307/3125 : ℝ)))^(4935/1024 : ℝ) := by
    rw [show (74082482670610483419/74090000000000000000 : ℝ)+(50547030403/92612500000000 : ℝ)*((17233/100000 : ℝ)+(307/3125 : ℝ))=(10000462124257443/10000000000000000 : ℝ) by norm_num, show 1+(4176347041158163/20000000000000000000 : ℝ)+(695775373547569/50000000000000000000 : ℝ)=(100022273285952885953/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4176347041158163/20000000000000000000 : ℝ) ≤ ((74082482670610483419/74090000000000000000 : ℝ)+2*(50547030403/92612500000000 : ℝ)*(17233/100000 : ℝ))^(4935/1024 : ℝ) := by
    rw [show (74082482670610483419/74090000000000000000 : ℝ)+2*(50547030403/92612500000000 : ℝ)*(17233/100000 : ℝ)=(10000866500500667/10000000000000000 : ℝ) by norm_num, show 1+2*(4176347041158163/20000000000000000000 : ℝ)=(10004176347041158163/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74082482670610483419/74090000000000000000 : ℝ)*(X 1 0+X 2 0)+(50547030403/92612500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (307/3125 : ℝ)) (hi := (17233/100000 : ℝ)) (c := (74082482670610483419/74090000000000000000 : ℝ)) (alpha := (50547030403/92612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74082482670610483419/74090000000000000000 : ℝ)*(X 0 1+X 2 1)+(50547030403/92612500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (307/3125 : ℝ)) (hi := (17233/100000 : ℝ)) (c := (74082482670610483419/74090000000000000000 : ℝ)) (alpha := (50547030403/92612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74082482670610483419/74090000000000000000 : ℝ)*(X 0 2+X 1 2)+(50547030403/92612500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4935/1024 : ℝ)) (lo := (307/3125 : ℝ)) (hi := (17233/100000 : ℝ)) (c := (74082482670610483419/74090000000000000000 : ℝ)) (alpha := (50547030403/92612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-798295943/5000000000 : ℝ)*X 0 0+(544932191/1000000000 : ℝ)*X 0 1+(207255381/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673934557/5000000000 : ℝ)*X 1 0+(-867293627/5000000000 : ℝ)*X 1 1+(5181385317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336967449/2500000000 : ℝ)*X 2 0+(259069229/500000000 : ℝ)*X 2 1+(-43364683/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4176481297/10000000000 : ℝ)*X 0 0+(767634513/2000000000 : ℝ)*X 0 1+(4535760211/10000000000 : ℝ)*X 0 2+(4176481297/10000000000 : ℝ)*X 1 0+(767634513/2000000000 : ℝ)*X 1 1+(4535760211/10000000000 : ℝ)*X 1 2+(4176481297/10000000000 : ℝ)*X 2 0+(767634513/2000000000 : ℝ)*X 2 1+(4535760211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1596659743/10000000000 : ℝ)*X 0 0+(1036692789/2000000000 : ℝ)*X 0 1+(5447220299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527624431/1000000000 : ℝ)*X 1 0+(-1468751491/10000000000 : ℝ)*X 1 1+(2723610223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((164882643/312500000 : ℝ)*X 2 0+(2723610031/5000000000 : ℝ)*X 2 1+(-1468751661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4176659069/10000000000 : ℝ)*X 0 0+(4530347801/10000000000 : ℝ)*X 0 1+(3843642977/10000000000 : ℝ)*X 0 2+(4176659069/10000000000 : ℝ)*X 1 0+(4530347801/10000000000 : ℝ)*X 1 1+(3843642977/10000000000 : ℝ)*X 1 2+(4176659069/10000000000 : ℝ)*X 2 0+(4530347801/10000000000 : ℝ)*X 2 1+(3843642977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1655_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18121945984586036012472824109/1852250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (228796993/20000000000000 : ℝ)*(base19) + (728613101/50000000000000 : ℝ)*(base23) + (137662199/50000000000000 : ℝ)*(upper3) + (43511253/50000000000000 : ℝ)*(upper4) + (8967797/5000000000000 : ℝ)*(upper5) + (1291445203570721/50000000000000 : ℝ)*(major0) + (1291445203570721/50000000000000 : ℝ)*(major1) + (1291445203570721/50000000000000 : ℝ)*(major2) + (74644707667243/2000000000000 : ℝ)*(sp0) + (933063934521797/25000000000000 : ℝ)*(sp1) + (29158245506609/781250000000 : ℝ)*(sp2) + (358379165155219/25000000000000 : ℝ)*(sp3) + (21498710003/100000000000000 : ℝ)*(sp4) + (6945464933/100000000000000 : ℝ)*(sp7) + (143352360608581/10000000000000 : ℝ)*(f.failure) + (1866128441036077/50000000000000 : ℝ)*(f.sum) + (7420190968777/9261250000000000000000000000 : ℝ)*base65 + (1554237734850928229/119500000000000000000000000000000 : ℝ)*base67 + (1366551941138928229/119500000000000000000000000000000 : ℝ)*base69 + (1460344508777428229/119500000000000000000000000000000 : ℝ)*base71 + (26848003073563/37045000000000000000000000000 : ℝ)*base73 + (597887436733428229/119500000000000000000000000000000 : ℝ)*base75 + (443476662757428229/119500000000000000000000000000000 : ℝ)*base77 + (771850701763428229/119500000000000000000000000000000 : ℝ)*base79 + (59047958157/37045000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3984889/500000000000000000000 : ℝ)*base89 + (3984889/500000000000000000000 : ℝ)*base91 + (3984889/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13997604770055240127106682861/3704500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (571559337/100000000000000 : ℝ)*(base19) + (168625923/20000000000000 : ℝ)*(base23) + (697819/625000000000 : ℝ)*(upper3) + (19700057/50000000000000 : ℝ)*(lower4) + (1177231/5000000000000 : ℝ)*(upper5) + (2623803210413791/100000000000000 : ℝ)*(major0) + (2623803210413791/100000000000000 : ℝ)*(major1) + (2623803210413791/100000000000000 : ℝ)*(major2) + (7685235247/100000000000000 : ℝ)*(sp1) + (506820197/6250000000000 : ℝ)*(sp2) + (3791375775202473/100000000000000 : ℝ)*(sp4) + (3791367518407889/100000000000000 : ℝ)*(sp5) + (1895683411474853/50000000000000 : ℝ)*(sp6) + (1456230519673741/100000000000000 : ℝ)*(sp7) + (1456230519673741/100000000000000 : ℝ)*(f.failure) + (3791375775202473/100000000000000 : ℝ)*(f.sum) + (84336712224433/18522500000000000000000000000 : ℝ)*base66 + (217696971302618341/239000000000000000000000000000000 : ℝ)*base68 + (2277646780364618341/239000000000000000000000000000000 : ℝ)*base70 + (864072555191618341/239000000000000000000000000000000 : ℝ)*base72 + (3447870605797/1157656250000000000000000000 : ℝ)*base73 + (2054078380838618341/239000000000000000000000000000000 : ℝ)*base76 + (715316302291618341/239000000000000000000000000000000 : ℝ)*base78 + (1117212176635618341/239000000000000000000000000000000 : ℝ)*base80 + (116281049954111/37045000000000000000000000000 : ℝ)*base82 + (25688929/5000000000000000000000 : ℝ)*base89 + (25688929/5000000000000000000000 : ℝ)*base91 + (25688929/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1655_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (307/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1655_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1655_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1655_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1655_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1655_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4935/1024 : ℝ) ≤ p) (hpb : p ≤ (4939/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90088869/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1329/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16329/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1655_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

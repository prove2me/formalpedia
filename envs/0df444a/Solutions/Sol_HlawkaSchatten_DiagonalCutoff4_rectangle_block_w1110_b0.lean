-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1110_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:53.954334+00:00
-- url     : https://prove2.me/submissions/4358b3d7-043d-41b5-af32-e5c70c7b85c8

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
theorem support_rectangle_w1110_s0_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901980129/10000000000 : ℝ)*x 0 + (1515438967/2500000000 : ℝ)*x 1 + (2388205917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901980129/10000000000 : ℝ)^8303 ≤ (11045998759117/100000000000000 : ℝ)^6255 := by
    have hnat : (1901980129 : ℕ)^8303*100000000000000^6255 ≤ 11045998759117^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901980129 10000000000 11045998759117 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1515438967/2500000000 : ℝ)^8303 ≤ (25726887544907/50000000000000 : ℝ)^6255 := by
    have hnat : (1515438967 : ℕ)^8303*50000000000000^6255 ≤ 25726887544907^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515438967 2500000000 25726887544907 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388205917/5000000000 : ℝ)^8303 ≤ (3750022612853/10000000000000 : ℝ)^6255 := by
    have hnat : (2388205917 : ℕ)^8303*10000000000000^6255 ≤ 3750022612853^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388205917 5000000000 3750022612853 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901980129/10000000000 : ℝ), (1515438967/2500000000 : ℝ), (2388205917/5000000000 : ℝ)] ![(11045998759117/100000000000000 : ℝ), (25726887544907/50000000000000 : ℝ), (3750022612853/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901980129/10000000000 : ℝ)|^8303 ≤ (11045998759117/100000000000000 : ℝ)^6255
        have hw : |(-1901980129/10000000000 : ℝ)|=(1901980129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1515438967/2500000000 : ℝ)|^8303 ≤ (25726887544907/50000000000000 : ℝ)^6255
        have hw : |(1515438967/2500000000 : ℝ)|=(1515438967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2388205917/5000000000 : ℝ)|^8303 ≤ (3750022612853/10000000000000 : ℝ)^6255
        have hw : |(2388205917/5000000000 : ℝ)|=(2388205917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s0_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5518595923/10000000000 : ℝ)*x 0 + (-528108583/2000000000 : ℝ)*x 1 + (955282389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518595923/10000000000 : ℝ)^8303 ≤ (22712692352277/50000000000000 : ℝ)^6255 := by
    have hnat : (5518595923 : ℕ)^8303*50000000000000^6255 ≤ 22712692352277^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518595923 10000000000 22712692352277 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528108583/2000000000 : ℝ)^8303 ≤ (17074388006697/100000000000000 : ℝ)^6255 := by
    have hnat : (528108583 : ℕ)^8303*100000000000000^6255 ≤ 17074388006697^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528108583 2000000000 17074388006697 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955282389/2000000000 : ℝ)^8303 ≤ (18750113642671/50000000000000 : ℝ)^6255 := by
    have hnat : (955282389 : ℕ)^8303*50000000000000^6255 ≤ 18750113642671^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955282389 2000000000 18750113642671 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518595923/10000000000 : ℝ), (-528108583/2000000000 : ℝ), (955282389/2000000000 : ℝ)] ![(22712692352277/50000000000000 : ℝ), (17074388006697/100000000000000 : ℝ), (18750113642671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518595923/10000000000 : ℝ)|^8303 ≤ (22712692352277/50000000000000 : ℝ)^6255
        have hw : |(5518595923/10000000000 : ℝ)|=(5518595923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528108583/2000000000 : ℝ)|^8303 ≤ (17074388006697/100000000000000 : ℝ)^6255
        have hw : |(-528108583/2000000000 : ℝ)|=(528108583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955282389/2000000000 : ℝ)|^8303 ≤ (18750113642671/50000000000000 : ℝ)^6255
        have hw : |(955282389/2000000000 : ℝ)|=(955282389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s0_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2759298081/5000000000 : ℝ)*x 0 + (4776411699/10000000000 : ℝ)*x 1 + (-660135727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2759298081/5000000000 : ℝ)^8303 ≤ (45425387315967/100000000000000 : ℝ)^6255 := by
    have hnat : (2759298081 : ℕ)^8303*100000000000000^6255 ≤ 45425387315967^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759298081 5000000000 45425387315967 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4776411699/10000000000 : ℝ)^8303 ≤ (9375056180399/25000000000000 : ℝ)^6255 := by
    have hnat : (4776411699 : ℕ)^8303*25000000000000^6255 ≤ 9375056180399^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4776411699 10000000000 9375056180399 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660135727/2500000000 : ℝ)^8303 ≤ (17074387946613/100000000000000 : ℝ)^6255 := by
    have hnat : (660135727 : ℕ)^8303*100000000000000^6255 ≤ 17074387946613^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660135727 2500000000 17074387946613 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2759298081/5000000000 : ℝ), (4776411699/10000000000 : ℝ), (-660135727/2500000000 : ℝ)] ![(45425387315967/100000000000000 : ℝ), (9375056180399/25000000000000 : ℝ), (17074387946613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2759298081/5000000000 : ℝ)|^8303 ≤ (45425387315967/100000000000000 : ℝ)^6255
        have hw : |(2759298081/5000000000 : ℝ)|=(2759298081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4776411699/10000000000 : ℝ)|^8303 ≤ (9375056180399/25000000000000 : ℝ)^6255
        have hw : |(4776411699/10000000000 : ℝ)|=(4776411699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-660135727/2500000000 : ℝ)|^8303 ≤ (17074387946613/100000000000000 : ℝ)^6255
        have hw : |(-660135727/2500000000 : ℝ)|=(660135727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s0_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2101795771/5000000000 : ℝ)*x 0 + (3122607591/10000000000 : ℝ)*x 1 + (707965773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101795771/5000000000 : ℝ)^8303 ≤ (31650972956281/100000000000000 : ℝ)^6255 := by
    have hnat : (2101795771 : ℕ)^8303*100000000000000^6255 ≤ 31650972956281^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101795771 5000000000 31650972956281 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122607591/10000000000 : ℝ)^8303 ≤ (21331101377351/100000000000000 : ℝ)^6255 := by
    have hnat : (3122607591 : ℕ)^8303*100000000000000^6255 ≤ 21331101377351^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122607591 10000000000 21331101377351 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (707965773/1250000000 : ℝ)^8303 ≤ (47017925657297/100000000000000 : ℝ)^6255 := by
    have hnat : (707965773 : ℕ)^8303*100000000000000^6255 ≤ 47017925657297^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707965773 1250000000 47017925657297 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101795771/5000000000 : ℝ), (3122607591/10000000000 : ℝ), (707965773/1250000000 : ℝ)] ![(31650972956281/100000000000000 : ℝ), (21331101377351/100000000000000 : ℝ), (47017925657297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101795771/5000000000 : ℝ)|^8303 ≤ (31650972956281/100000000000000 : ℝ)^6255
        have hw : |(2101795771/5000000000 : ℝ)|=(2101795771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122607591/10000000000 : ℝ)|^8303 ≤ (21331101377351/100000000000000 : ℝ)^6255
        have hw : |(3122607591/10000000000 : ℝ)|=(3122607591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(707965773/1250000000 : ℝ)|^8303 ≤ (47017925657297/100000000000000 : ℝ)^6255
        have hw : |(707965773/1250000000 : ℝ)|=(707965773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s0_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-953610817/5000000000 : ℝ)*x 0 + (961917039/2000000000 : ℝ)*x 1 + (602741797/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953610817/5000000000 : ℝ)^8303 ≤ (2217284909733/20000000000000 : ℝ)^6255 := by
    have hnat : (953610817 : ℕ)^8303*20000000000000^6255 ≤ 2217284909733^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953610817 5000000000 2217284909733 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961917039/2000000000 : ℝ)^8303 ≤ (37846342439347/100000000000000 : ℝ)^6255 := by
    have hnat : (961917039 : ℕ)^8303*100000000000000^6255 ≤ 37846342439347^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961917039 2000000000 37846342439347 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (602741797/1000000000 : ℝ)^8303 ≤ (51067233004313/100000000000000 : ℝ)^6255 := by
    have hnat : (602741797 : ℕ)^8303*100000000000000^6255 ≤ 51067233004313^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602741797 1000000000 51067233004313 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-953610817/5000000000 : ℝ), (961917039/2000000000 : ℝ), (602741797/1000000000 : ℝ)] ![(2217284909733/20000000000000 : ℝ), (37846342439347/100000000000000 : ℝ), (51067233004313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-953610817/5000000000 : ℝ)|^8303 ≤ (2217284909733/20000000000000 : ℝ)^6255
        have hw : |(-953610817/5000000000 : ℝ)|=(953610817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(961917039/2000000000 : ℝ)|^8303 ≤ (37846342439347/100000000000000 : ℝ)^6255
        have hw : |(961917039/2000000000 : ℝ)|=(961917039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(602741797/1000000000 : ℝ)|^8303 ≤ (51067233004313/100000000000000 : ℝ)^6255
        have hw : |(602741797/1000000000 : ℝ)|=(602741797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s0_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (206779949/400000000 : ℝ)*x 0 + (-1389537711/10000000000 : ℝ)*x 1 + (1205484003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206779949/400000000 : ℝ)^8303 ≤ (10412770135209/25000000000000 : ℝ)^6255 := by
    have hnat : (206779949 : ℕ)^8303*25000000000000^6255 ≤ 10412770135209^6255*400000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206779949 400000000 10412770135209 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389537711/10000000000 : ℝ)^8303 ≤ (7281663437669/100000000000000 : ℝ)^6255 := by
    have hnat : (1389537711 : ℕ)^8303*100000000000000^6255 ≤ 7281663437669^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389537711 10000000000 7281663437669 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205484003/2000000000 : ℝ)^8303 ≤ (51067256003479/100000000000000 : ℝ)^6255 := by
    have hnat : (1205484003 : ℕ)^8303*100000000000000^6255 ≤ 51067256003479^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205484003 2000000000 51067256003479 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206779949/400000000 : ℝ), (-1389537711/10000000000 : ℝ), (1205484003/2000000000 : ℝ)] ![(10412770135209/25000000000000 : ℝ), (7281663437669/100000000000000 : ℝ), (51067256003479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206779949/400000000 : ℝ)|^8303 ≤ (10412770135209/25000000000000 : ℝ)^6255
        have hw : |(206779949/400000000 : ℝ)|=(206779949/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1389537711/10000000000 : ℝ)|^8303 ≤ (7281663437669/100000000000000 : ℝ)^6255
        have hw : |(-1389537711/10000000000 : ℝ)|=(1389537711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1205484003/2000000000 : ℝ)|^8303 ≤ (51067256003479/100000000000000 : ℝ)^6255
        have hw : |(1205484003/2000000000 : ℝ)|=(1205484003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s0_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169501441/10000000000 : ℝ)*x 0 + (3013709239/5000000000 : ℝ)*x 1 + (-1389536021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169501441/10000000000 : ℝ)^8303 ≤ (20825554794389/50000000000000 : ℝ)^6255 := by
    have hnat : (5169501441 : ℕ)^8303*50000000000000^6255 ≤ 20825554794389^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169501441 10000000000 20825554794389 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3013709239/5000000000 : ℝ)^8303 ≤ (51067238717553/100000000000000 : ℝ)^6255 := by
    have hnat : (3013709239 : ℕ)^8303*100000000000000^6255 ≤ 51067238717553^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013709239 5000000000 51067238717553 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389536021/10000000000 : ℝ)^8303 ≤ (1820412920451/25000000000000 : ℝ)^6255 := by
    have hnat : (1389536021 : ℕ)^8303*25000000000000^6255 ≤ 1820412920451^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389536021 10000000000 1820412920451 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169501441/10000000000 : ℝ), (3013709239/5000000000 : ℝ), (-1389536021/10000000000 : ℝ)] ![(20825554794389/50000000000000 : ℝ), (51067238717553/100000000000000 : ℝ), (1820412920451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169501441/10000000000 : ℝ)|^8303 ≤ (20825554794389/50000000000000 : ℝ)^6255
        have hw : |(5169501441/10000000000 : ℝ)|=(5169501441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3013709239/5000000000 : ℝ)|^8303 ≤ (51067238717553/100000000000000 : ℝ)^6255
        have hw : |(3013709239/5000000000 : ℝ)|=(3013709239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1389536021/10000000000 : ℝ)|^8303 ≤ (1820412920451/25000000000000 : ℝ)^6255
        have hw : |(-1389536021/10000000000 : ℝ)|=(1389536021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s0_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4213950611/10000000000 : ℝ)*x 0 + (5598144943/10000000000 : ℝ)*x 1 + (3190490609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4213950611/10000000000 : ℝ)^8303 ≤ (1587727578359/5000000000000 : ℝ)^6255 := by
    have hnat : (4213950611 : ℕ)^8303*5000000000000^6255 ≤ 1587727578359^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213950611 10000000000 1587727578359 5000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5598144943/10000000000 : ℝ)^8303 ≤ (46296614943977/100000000000000 : ℝ)^6255 := by
    have hnat : (5598144943 : ℕ)^8303*100000000000000^6255 ≤ 46296614943977^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598144943 10000000000 46296614943977 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3190490609/10000000000 : ℝ)^8303 ≤ (685901045947/3125000000000 : ℝ)^6255 := by
    have hnat : (3190490609 : ℕ)^8303*3125000000000^6255 ≤ 685901045947^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3190490609 10000000000 685901045947 3125000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4213950611/10000000000 : ℝ), (5598144943/10000000000 : ℝ), (3190490609/10000000000 : ℝ)] ![(1587727578359/5000000000000 : ℝ), (46296614943977/100000000000000 : ℝ), (685901045947/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4213950611/10000000000 : ℝ)|^8303 ≤ (1587727578359/5000000000000 : ℝ)^6255
        have hw : |(4213950611/10000000000 : ℝ)|=(4213950611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5598144943/10000000000 : ℝ)|^8303 ≤ (46296614943977/100000000000000 : ℝ)^6255
        have hw : |(5598144943/10000000000 : ℝ)|=(5598144943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3190490609/10000000000 : ℝ)|^8303 ≤ (685901045947/3125000000000 : ℝ)^6255
        have hw : |(3190490609/10000000000 : ℝ)|=(3190490609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (281/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13969/50000 : ℝ)*pair X 0 0 := by
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
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4151/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4151 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4151*1^1024 ≤ 0^1024*1^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4151/1024 : ℝ) ≤ (609265017964176871/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4151 ≤ (609265017964176871/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4151*25000000000000000000^1024 ≤ 609265017964176871^1024*5^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 609265017964176871 25000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (609265017964176871/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4151 := by
      have hnat : (1 : ℕ)^1024*1^4151 ≤ 1^4151*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25609265017964176871/25000000000000000000 : ℝ) ≤ (10059575112463147/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (25609265017964176871/25000000000000000000 : ℝ)^1024 ≤ (10059575112463147/10000000000000000 : ℝ)^4151 := by
      have hnat : (25609265017964176871 : ℕ)^1024*10000000000000000^4151 ≤ 10059575112463147^4151*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25609265017964176871 25000000000000000000 10059575112463147 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059575112463147/10000000000000000 : ℝ)) (X := (25609265017964176871/25000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13109265017964176871/12500000000000000000 : ℝ) ≤ (5059575112463147/5000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (13109265017964176871/12500000000000000000 : ℝ)^1024 ≤ (5059575112463147/5000000000000000 : ℝ)^4151 := by
      have hnat : (13109265017964176871 : ℕ)^1024*5000000000000000^4151 ≤ 5059575112463147^4151*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13109265017964176871 12500000000000000000 5059575112463147 5000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059575112463147/5000000000000000 : ℝ)) (X := (13109265017964176871/12500000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59575112463147/4000000000000000 : ℝ)*(0 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(59575112463147/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(609265017964176871/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59575112463147/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (1 : ℝ)+(59575112463147/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059575112463147/10000000000000000 : ℝ) by norm_num, show 1+(609265017964176871/25000000000000000000 : ℝ)+(0 : ℝ)=(25609265017964176871/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(609265017964176871/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59575112463147/4000000000000000 : ℝ)*(2/5 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(59575112463147/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059575112463147/5000000000000000 : ℝ) by norm_num, show 1+2*(609265017964176871/25000000000000000000 : ℝ)=(13109265017964176871/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59575112463147/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59575112463147/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59575112463147/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59575112463147/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59575112463147/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59575112463147/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1901980129/10000000000 : ℝ)*X 0 0+(1515438967/2500000000 : ℝ)*X 0 1+(2388205917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5518595923/10000000000 : ℝ)*X 1 0+(-528108583/2000000000 : ℝ)*X 1 1+(955282389/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2759298081/5000000000 : ℝ)*X 2 0+(4776411699/10000000000 : ℝ)*X 2 1+(-660135727/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2101795771/5000000000 : ℝ)*X 0 0+(3122607591/10000000000 : ℝ)*X 0 1+(707965773/1250000000 : ℝ)*X 0 2+(2101795771/5000000000 : ℝ)*X 1 0+(3122607591/10000000000 : ℝ)*X 1 1+(707965773/1250000000 : ℝ)*X 1 2+(2101795771/5000000000 : ℝ)*X 2 0+(3122607591/10000000000 : ℝ)*X 2 1+(707965773/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-953610817/5000000000 : ℝ)*X 0 0+(961917039/2000000000 : ℝ)*X 0 1+(602741797/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((206779949/400000000 : ℝ)*X 1 0+(-1389537711/10000000000 : ℝ)*X 1 1+(1205484003/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5169501441/10000000000 : ℝ)*X 2 0+(3013709239/5000000000 : ℝ)*X 2 1+(-1389536021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4213950611/10000000000 : ℝ)*X 0 0+(5598144943/10000000000 : ℝ)*X 0 1+(3190490609/10000000000 : ℝ)*X 0 2+(4213950611/10000000000 : ℝ)*X 1 0+(5598144943/10000000000 : ℝ)*X 1 1+(3190490609/10000000000 : ℝ)*X 1 2+(4213950611/10000000000 : ℝ)*X 2 0+(5598144943/10000000000 : ℝ)*X 2 1+(3190490609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (234537118789222392698199/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10069077/20000000000000 : ℝ)*(base1) + (1159809121/100000000000000 : ℝ)*(base19) + (55372857/5000000000000 : ℝ)*(base23) + (86045997/100000000000000 : ℝ)*(base24) + (273648239/100000000000000 : ℝ)*(upper3) + (146442389379987/25000000000000 : ℝ)*(major0) + (146442389379987/25000000000000 : ℝ)*(major1) + (146442389379987/25000000000000 : ℝ)*(major2) + (778005668486093/100000000000000 : ℝ)*(sp0) + (778006990510443/100000000000000 : ℝ)*(sp1) + (389003478408213/50000000000000 : ℝ)*(sp2) + (39352867738937/10000000000000 : ℝ)*(sp3) + (316522357/12500000000000 : ℝ)*(sp4) + (2080627493/100000000000000 : ℝ)*(sp7) + (49191351045281/12500000000000 : ℝ)*(f.failure) + (778008150319563/100000000000000 : ℝ)*(f.sum) + (87195713739089/50000000000000000000000000000 : ℝ)*base65 + (596422904460911/100000000000000000000000000000 : ℝ)*base68 + (63993296939089/100000000000000000000000000000 : ℝ)*base69 + (129820348360911/100000000000000000000000000000 : ℝ)*base72 + (62784505639089/50000000000000000000000000000 : ℝ)*base73 + (557444178360911/100000000000000000000000000000 : ℝ)*base76 + (86836339339089/100000000000000000000000000000 : ℝ)*base77 + (292278382539089/100000000000000000000000000000 : ℝ)*base79 + (442209191389089/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2240027/1250000000000000000000 : ℝ)*base90 + (2240027/1250000000000000000000 : ℝ)*base92 + (2240027/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37846362524628773465643/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32694677/20000000000000 : ℝ)*(base13) + (110798387/12500000000000 : ℝ)*(base23) + (432264973/100000000000000 : ℝ)*(base39) + (26482799/50000000000000 : ℝ)*(base45) + (25006907/50000000000000 : ℝ)*(upper3) + (248920273/100000000000000 : ℝ)*(upper5) + (309117363578289/50000000000000 : ℝ)*(major0) + (309117363578289/50000000000000 : ℝ)*(major1) + (309117147445803/50000000000000 : ℝ)*(major2) + (520728313/100000000000000 : ℝ)*(sp2) + (410563624335017/50000000000000 : ℝ)*(sp4) + (821127412143419/100000000000000 : ℝ)*(sp5) + (410563218646491/50000000000000 : ℝ)*(sp6) + (415341508981127/100000000000000 : ℝ)*(sp7) + (415341508981127/100000000000000 : ℝ)*(f.failure) + (102640980551049/12500000000000 : ℝ)*(f.sum) + (33171257265619/50000000000000000000000000000 : ℝ)*base66 + (725664460877959/200000000000000000000000000000 : ℝ)*base68 + (1190763097215483/200000000000000000000000000000 : ℝ)*base69 + (322208857077959/200000000000000000000000000000 : ℝ)*base72 + (14156947815619/50000000000000000000000000000 : ℝ)*base74 + (49040963784517/200000000000000000000000000000 : ℝ)*base76 + (414764488815483/200000000000000000000000000000 : ℝ)*base77 + (616016626984517/200000000000000000000000000000 : ℝ)*base80 + (406995189884517/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (55989091/10000000000000000000000 : ℝ)*base89 + (55989091/10000000000000000000000 : ℝ)*base91 + (44010909/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1110_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13969/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1110_s1_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108956547/10000000000 : ℝ)*x 0 + (5710143297/10000000000 : ℝ)*x 1 + (2497751751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108956547/10000000000 : ℝ)^8303 ≤ (12669374186967/100000000000000 : ℝ)^6255 := by
    have hnat : (2108956547 : ℕ)^8303*100000000000000^6255 ≤ 12669374186967^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108956547 10000000000 12669374186967 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5710143297/10000000000 : ℝ)^8303 ≤ (2901007834/6103515625 : ℝ)^6255 := by
    have hnat : (5710143297 : ℕ)^8303*6103515625^6255 ≤ 2901007834^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5710143297 10000000000 2901007834 6103515625 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2497751751/5000000000 : ℝ)^8303 ≤ (497506418047/1250000000000 : ℝ)^6255 := by
    have hnat : (2497751751 : ℕ)^8303*1250000000000^6255 ≤ 497506418047^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497751751 5000000000 497506418047 1250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108956547/10000000000 : ℝ), (5710143297/10000000000 : ℝ), (2497751751/5000000000 : ℝ)] ![(12669374186967/100000000000000 : ℝ), (2901007834/6103515625 : ℝ), (497506418047/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108956547/10000000000 : ℝ)|^8303 ≤ (12669374186967/100000000000000 : ℝ)^6255
        have hw : |(-2108956547/10000000000 : ℝ)|=(2108956547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5710143297/10000000000 : ℝ)|^8303 ≤ (2901007834/6103515625 : ℝ)^6255
        have hw : |(5710143297/10000000000 : ℝ)|=(5710143297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2497751751/5000000000 : ℝ)|^8303 ≤ (497506418047/1250000000000 : ℝ)^6255
        have hw : |(2497751751/5000000000 : ℝ)|=(2497751751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s1_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (338805109/625000000 : ℝ)*x 0 + (-499050119/2000000000 : ℝ)*x 1 + (4995503477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338805109/625000000 : ℝ)^8303 ≤ (44360826117557/100000000000000 : ℝ)^6255 := by
    have hnat : (338805109 : ℕ)^8303*100000000000000^6255 ≤ 44360826117557^6255*625000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338805109 625000000 44360826117557 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499050119/2000000000 : ℝ)^8303 ≤ (1979832585521/12500000000000 : ℝ)^6255 := by
    have hnat : (499050119 : ℕ)^8303*12500000000000^6255 ≤ 1979832585521^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499050119 2000000000 1979832585521 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4995503477/10000000000 : ℝ)^8303 ≤ (39800513179363/100000000000000 : ℝ)^6255 := by
    have hnat : (4995503477 : ℕ)^8303*100000000000000^6255 ≤ 39800513179363^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4995503477 10000000000 39800513179363 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338805109/625000000 : ℝ), (-499050119/2000000000 : ℝ), (4995503477/10000000000 : ℝ)] ![(44360826117557/100000000000000 : ℝ), (1979832585521/12500000000000 : ℝ), (39800513179363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338805109/625000000 : ℝ)|^8303 ≤ (44360826117557/100000000000000 : ℝ)^6255
        have hw : |(338805109/625000000 : ℝ)|=(338805109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499050119/2000000000 : ℝ)|^8303 ≤ (1979832585521/12500000000000 : ℝ)^6255
        have hw : |(-499050119/2000000000 : ℝ)|=(499050119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4995503477/10000000000 : ℝ)|^8303 ≤ (39800513179363/100000000000000 : ℝ)^6255
        have hw : |(4995503477/10000000000 : ℝ)|=(4995503477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s1_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5420883029/10000000000 : ℝ)*x 0 + (2497751129/5000000000 : ℝ)*x 1 + (-623812617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420883029/10000000000 : ℝ)^8303 ≤ (8872168015223/20000000000000 : ℝ)^6255 := by
    have hnat : (5420883029 : ℕ)^8303*20000000000000^6255 ≤ 8872168015223^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420883029 10000000000 8872168015223 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2497751129/5000000000 : ℝ)^8303 ≤ (9950125071837/25000000000000 : ℝ)^6255 := by
    have hnat : (2497751129 : ℕ)^8303*25000000000000^6255 ≤ 9950125071837^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497751129 5000000000 9950125071837 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623812617/2500000000 : ℝ)^8303 ≤ (15838659614089/100000000000000 : ℝ)^6255 := by
    have hnat : (623812617 : ℕ)^8303*100000000000000^6255 ≤ 15838659614089^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623812617 2500000000 15838659614089 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420883029/10000000000 : ℝ), (2497751129/5000000000 : ℝ), (-623812617/2500000000 : ℝ)] ![(8872168015223/20000000000000 : ℝ), (9950125071837/25000000000000 : ℝ), (15838659614089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420883029/10000000000 : ℝ)|^8303 ≤ (8872168015223/20000000000000 : ℝ)^6255
        have hw : |(5420883029/10000000000 : ℝ)|=(5420883029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2497751129/5000000000 : ℝ)|^8303 ≤ (9950125071837/25000000000000 : ℝ)^6255
        have hw : |(2497751129/5000000000 : ℝ)|=(2497751129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-623812617/2500000000 : ℝ)|^8303 ≤ (15838659614089/100000000000000 : ℝ)^6255
        have hw : |(-623812617/2500000000 : ℝ)|=(623812617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s1_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4320137157/10000000000 : ℝ)*x 0 + (458874709/1250000000 : ℝ)*x 1 + (2541917557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320137157/10000000000 : ℝ)^8303 ≤ (32821078148893/100000000000000 : ℝ)^6255 := by
    have hnat : (4320137157 : ℕ)^8303*100000000000000^6255 ≤ 32821078148893^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320137157 10000000000 32821078148893 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458874709/1250000000 : ℝ)^8303 ≤ (13220764471743/50000000000000 : ℝ)^6255 := by
    have hnat : (458874709 : ℕ)^8303*50000000000000^6255 ≤ 13220764471743^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458874709 1250000000 13220764471743 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541917557/5000000000 : ℝ)^8303 ≤ (40737392881677/100000000000000 : ℝ)^6255 := by
    have hnat : (2541917557 : ℕ)^8303*100000000000000^6255 ≤ 40737392881677^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541917557 5000000000 40737392881677 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320137157/10000000000 : ℝ), (458874709/1250000000 : ℝ), (2541917557/5000000000 : ℝ)] ![(32821078148893/100000000000000 : ℝ), (13220764471743/50000000000000 : ℝ), (40737392881677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320137157/10000000000 : ℝ)|^8303 ≤ (32821078148893/100000000000000 : ℝ)^6255
        have hw : |(4320137157/10000000000 : ℝ)|=(4320137157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458874709/1250000000 : ℝ)|^8303 ≤ (13220764471743/50000000000000 : ℝ)^6255
        have hw : |(458874709/1250000000 : ℝ)|=(458874709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541917557/5000000000 : ℝ)|^8303 ≤ (40737392881677/100000000000000 : ℝ)^6255
        have hw : |(2541917557/5000000000 : ℝ)|=(2541917557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s1_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109808377/10000000000 : ℝ)*x 0 + (625672643/1250000000 : ℝ)*x 1 + (2850033979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109808377/10000000000 : ℝ)^8303 ≤ (633808371303/5000000000000 : ℝ)^6255 := by
    have hnat : (2109808377 : ℕ)^8303*5000000000000^6255 ≤ 633808371303^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109808377 10000000000 633808371303 5000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625672643/1250000000 : ℝ)^8303 ≤ (39905012149127/100000000000000 : ℝ)^6255 := by
    have hnat : (625672643 : ℕ)^8303*100000000000000^6255 ≤ 39905012149127^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625672643 1250000000 39905012149127 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850033979/5000000000 : ℝ)^8303 ≤ (23709410206791/50000000000000 : ℝ)^6255 := by
    have hnat : (2850033979 : ℕ)^8303*50000000000000^6255 ≤ 23709410206791^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850033979 5000000000 23709410206791 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109808377/10000000000 : ℝ), (625672643/1250000000 : ℝ), (2850033979/5000000000 : ℝ)] ![(633808371303/5000000000000 : ℝ), (39905012149127/100000000000000 : ℝ), (23709410206791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109808377/10000000000 : ℝ)|^8303 ≤ (633808371303/5000000000000 : ℝ)^6255
        have hw : |(-2109808377/10000000000 : ℝ)|=(2109808377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625672643/1250000000 : ℝ)|^8303 ≤ (39905012149127/100000000000000 : ℝ)^6255
        have hw : |(625672643/1250000000 : ℝ)|=(625672643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850033979/5000000000 : ℝ)|^8303 ≤ (23709410206791/50000000000000 : ℝ)^6255
        have hw : |(2850033979/5000000000 : ℝ)|=(2850033979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s1_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1047591519/2000000000 : ℝ)*x 0 + (-1790685761/10000000000 : ℝ)*x 1 + (1425016941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047591519/2000000000 : ℝ)^8303 ≤ (21192419428117/50000000000000 : ℝ)^6255 := by
    have hnat : (1047591519 : ℕ)^8303*50000000000000^6255 ≤ 21192419428117^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047591519 2000000000 21192419428117 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1790685761/10000000000 : ℝ)^8303 ≤ (10196342864429/100000000000000 : ℝ)^6255 := by
    have hnat : (1790685761 : ℕ)^8303*100000000000000^6255 ≤ 10196342864429^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790685761 10000000000 10196342864429 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1425016941/2500000000 : ℝ)^8303 ≤ (47418818271283/100000000000000 : ℝ)^6255 := by
    have hnat : (1425016941 : ℕ)^8303*100000000000000^6255 ≤ 47418818271283^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425016941 2500000000 47418818271283 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047591519/2000000000 : ℝ), (-1790685761/10000000000 : ℝ), (1425016941/2500000000 : ℝ)] ![(21192419428117/50000000000000 : ℝ), (10196342864429/100000000000000 : ℝ), (47418818271283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047591519/2000000000 : ℝ)|^8303 ≤ (21192419428117/50000000000000 : ℝ)^6255
        have hw : |(1047591519/2000000000 : ℝ)|=(1047591519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1790685761/10000000000 : ℝ)|^8303 ≤ (10196342864429/100000000000000 : ℝ)^6255
        have hw : |(-1790685761/10000000000 : ℝ)|=(1790685761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1425016941/2500000000 : ℝ)|^8303 ≤ (47418818271283/100000000000000 : ℝ)^6255
        have hw : |(1425016941/2500000000 : ℝ)|=(1425016941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s1_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2618978811/5000000000 : ℝ)*x 0 + (2850033953/5000000000 : ℝ)*x 1 + (-358137103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2618978811/5000000000 : ℝ)^8303 ≤ (42384839146249/100000000000000 : ℝ)^6255 := by
    have hnat : (2618978811 : ℕ)^8303*100000000000000^6255 ≤ 42384839146249^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618978811 5000000000 42384839146249 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850033953/5000000000 : ℝ)^8303 ≤ (23709409919679/50000000000000 : ℝ)^6255 := by
    have hnat : (2850033953 : ℕ)^8303*50000000000000^6255 ≤ 23709409919679^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850033953 5000000000 23709409919679 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (358137103/2000000000 : ℝ)^8303 ≤ (203926820101/2000000000000 : ℝ)^6255 := by
    have hnat : (358137103 : ℕ)^8303*2000000000000^6255 ≤ 203926820101^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358137103 2000000000 203926820101 2000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2618978811/5000000000 : ℝ), (2850033953/5000000000 : ℝ), (-358137103/2000000000 : ℝ)] ![(42384839146249/100000000000000 : ℝ), (23709409919679/50000000000000 : ℝ), (203926820101/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2618978811/5000000000 : ℝ)|^8303 ≤ (42384839146249/100000000000000 : ℝ)^6255
        have hw : |(2618978811/5000000000 : ℝ)|=(2618978811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2850033953/5000000000 : ℝ)|^8303 ≤ (23709409919679/50000000000000 : ℝ)^6255
        have hw : |(2850033953/5000000000 : ℝ)|=(2850033953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-358137103/2000000000 : ℝ)|^8303 ≤ (203926820101/2000000000000 : ℝ)^6255
        have hw : |(-358137103/2000000000 : ℝ)|=(358137103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s1_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1080454907/2500000000 : ℝ)*x 0 + (5064307807/10000000000 : ℝ)*x 1 + (3690915711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080454907/2500000000 : ℝ)^8303 ≤ (16419023223879/50000000000000 : ℝ)^6255 := by
    have hnat : (1080454907 : ℕ)^8303*50000000000000^6255 ≤ 16419023223879^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080454907 2500000000 16419023223879 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5064307807/10000000000 : ℝ)^8303 ≤ (4052981625969/10000000000000 : ℝ)^6255 := by
    have hnat : (5064307807 : ℕ)^8303*10000000000000^6255 ≤ 4052981625969^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064307807 10000000000 4052981625969 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3690915711/10000000000 : ℝ)^8303 ≤ (26632137275171/100000000000000 : ℝ)^6255 := by
    have hnat : (3690915711 : ℕ)^8303*100000000000000^6255 ≤ 26632137275171^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3690915711 10000000000 26632137275171 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080454907/2500000000 : ℝ), (5064307807/10000000000 : ℝ), (3690915711/10000000000 : ℝ)] ![(16419023223879/50000000000000 : ℝ), (4052981625969/10000000000000 : ℝ), (26632137275171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080454907/2500000000 : ℝ)|^8303 ≤ (16419023223879/50000000000000 : ℝ)^6255
        have hw : |(1080454907/2500000000 : ℝ)|=(1080454907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5064307807/10000000000 : ℝ)|^8303 ≤ (4052981625969/10000000000000 : ℝ)^6255
        have hw : |(5064307807/10000000000 : ℝ)|=(5064307807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3690915711/10000000000 : ℝ)|^8303 ≤ (26632137275171/100000000000000 : ℝ)^6255
        have hw : |(3690915711/10000000000 : ℝ)|=(3690915711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13969/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5469/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2573/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13969/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13969/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13969/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13969/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13969/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13969/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (281/100000 : ℝ) ^ (4151/1024 : ℝ) ≤ (4547711483/100000000000000000000 : ℝ) := by
    have hpowers : (281/100000 : ℝ)^4151 ≤ (4547711483/100000000000000000000 : ℝ)^1024 := by
      have hnat : (281 : ℕ)^4151*100000000000000000000^1024 ≤ 4547711483^1024*100000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 100000 4547711483 100000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/100000 : ℝ)) (X := (4547711483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13969/50000 : ℝ) ^ (4151/1024 : ℝ) ≤ (568899933665781823/100000000000000000000 : ℝ) := by
    have hpowers : (13969/50000 : ℝ)^4151 ≤ (568899933665781823/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13969 : ℕ)^4151*100000000000000000000^1024 ≤ 568899933665781823^1024*50000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13969 50000 568899933665781823 100000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13969/50000 : ℝ)) (X := (568899933665781823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000004547711483/50000000000000000000 : ℝ) ≤ (10000000000224373/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50000000004547711483/50000000000000000000 : ℝ)^1024 ≤ (10000000000224373/10000000000000000 : ℝ)^4151 := by
      have hnat : (50000000004547711483 : ℕ)^1024*10000000000000000^4151 ≤ 10000000000224373^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000004547711483 50000000000000000000 10000000000224373 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000224373/10000000000000000 : ℝ)) (X := (50000000004547711483/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50284449969106746653/50000000000000000000 : ℝ) ≤ (10014004080389267/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50284449969106746653/50000000000000000000 : ℝ)^1024 ≤ (10014004080389267/10000000000000000 : ℝ)^4151 := by
      have hnat : (50284449969106746653 : ℕ)^1024*10000000000000000^4151 ≤ 10014004080389267^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50284449969106746653 50000000000000000000 10014004080389267 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014004080389267/10000000000000000 : ℝ)) (X := (50284449969106746653/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50568899933665781823/50000000000000000000 : ℝ) ≤ (10028008160554161/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50568899933665781823/50000000000000000000 : ℝ)^1024 ≤ (10028008160554161/10000000000000000 : ℝ)^4151 := by
      have hnat : (50568899933665781823 : ℕ)^1024*10000000000000000^4151 ≤ 10028008160554161^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50568899933665781823 50000000000000000000 10028008160554161 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028008160554161/10000000000000000 : ℝ)) (X := (50568899933665781823/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4547711483/100000000000000000000 : ℝ) ≤ ((276562129713152813633/276570000000000000000 : ℝ)+2*(7002040082447/1382850000000000 : ℝ)*(281/100000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (276562129713152813633/276570000000000000000 : ℝ)+2*(7002040082447/1382850000000000 : ℝ)*(281/100000 : ℝ)=(10000000000224373/10000000000000000 : ℝ) by norm_num, show 1+2*(4547711483/100000000000000000000 : ℝ)=(50000000004547711483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(568899933665781823/100000000000000000000 : ℝ)+(4547711483/100000000000000000000 : ℝ) ≤ ((276562129713152813633/276570000000000000000 : ℝ)+(7002040082447/1382850000000000 : ℝ)*((13969/50000 : ℝ)+(281/100000 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (276562129713152813633/276570000000000000000 : ℝ)+(7002040082447/1382850000000000 : ℝ)*((13969/50000 : ℝ)+(281/100000 : ℝ))=(10014004080389267/10000000000000000 : ℝ) by norm_num, show 1+(568899933665781823/100000000000000000000 : ℝ)+(4547711483/100000000000000000000 : ℝ)=(50284449969106746653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(568899933665781823/100000000000000000000 : ℝ) ≤ ((276562129713152813633/276570000000000000000 : ℝ)+2*(7002040082447/1382850000000000 : ℝ)*(13969/50000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (276562129713152813633/276570000000000000000 : ℝ)+2*(7002040082447/1382850000000000 : ℝ)*(13969/50000 : ℝ)=(10028008160554161/10000000000000000 : ℝ) by norm_num, show 1+2*(568899933665781823/100000000000000000000 : ℝ)=(50568899933665781823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (276562129713152813633/276570000000000000000 : ℝ)*(X 1 0+X 2 0)+(7002040082447/1382850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (281/100000 : ℝ)) (hi := (13969/50000 : ℝ)) (c := (276562129713152813633/276570000000000000000 : ℝ)) (alpha := (7002040082447/1382850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (276562129713152813633/276570000000000000000 : ℝ)*(X 0 1+X 2 1)+(7002040082447/1382850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (281/100000 : ℝ)) (hi := (13969/50000 : ℝ)) (c := (276562129713152813633/276570000000000000000 : ℝ)) (alpha := (7002040082447/1382850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (276562129713152813633/276570000000000000000 : ℝ)*(X 0 2+X 1 2)+(7002040082447/1382850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (281/100000 : ℝ)) (hi := (13969/50000 : ℝ)) (c := (276562129713152813633/276570000000000000000 : ℝ)) (alpha := (7002040082447/1382850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2108956547/10000000000 : ℝ)*X 0 0+(5710143297/10000000000 : ℝ)*X 0 1+(2497751751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((338805109/625000000 : ℝ)*X 1 0+(-499050119/2000000000 : ℝ)*X 1 1+(4995503477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5420883029/10000000000 : ℝ)*X 2 0+(2497751129/5000000000 : ℝ)*X 2 1+(-623812617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320137157/10000000000 : ℝ)*X 0 0+(458874709/1250000000 : ℝ)*X 0 1+(2541917557/5000000000 : ℝ)*X 0 2+(4320137157/10000000000 : ℝ)*X 1 0+(458874709/1250000000 : ℝ)*X 1 1+(2541917557/5000000000 : ℝ)*X 1 2+(4320137157/10000000000 : ℝ)*X 2 0+(458874709/1250000000 : ℝ)*X 2 1+(2541917557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109808377/10000000000 : ℝ)*X 0 0+(625672643/1250000000 : ℝ)*X 0 1+(2850033979/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1047591519/2000000000 : ℝ)*X 1 0+(-1790685761/10000000000 : ℝ)*X 1 1+(1425016941/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2618978811/5000000000 : ℝ)*X 2 0+(2850033953/5000000000 : ℝ)*X 2 1+(-358137103/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080454907/2500000000 : ℝ)*X 0 0+(5064307807/10000000000 : ℝ)*X 0 1+(3690915711/10000000000 : ℝ)*X 0 2+(1080454907/2500000000 : ℝ)*X 1 0+(5064307807/10000000000 : ℝ)*X 1 1+(3690915711/10000000000 : ℝ)*X 1 2+(1080454907/2500000000 : ℝ)*X 2 0+(5064307807/10000000000 : ℝ)*X 2 1+(3690915711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (610111417732495505218366501/288093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194033921/100000000000000 : ℝ)*(base1) + (216200267/100000000000000 : ℝ)*(base19) + (581780321/100000000000000 : ℝ)*(base23) + (399693/2500000000000 : ℝ)*(base37) + (5580243/20000000000000 : ℝ)*(upper3) + (131693897041547/12500000000000 : ℝ)*(major0) + (131693897041547/12500000000000 : ℝ)*(major1) + (131693897041547/12500000000000 : ℝ)*(major2) + (1399306617662187/100000000000000 : ℝ)*(sp0) + (1399305921693107/100000000000000 : ℝ)*(sp1) + (55972262404843/4000000000000 : ℝ)*(sp2) + (353897465074971/50000000000000 : ℝ)*(sp3) + (71827313/10000000000000 : ℝ)*(sp4) + (502004011/50000000000000 : ℝ)*(sp5) + (353897570085791/50000000000000 : ℝ)*(f.failure) + (349826785475349/25000000000000 : ℝ)*(f.sum) + (282404084331431/138285000000000000000000000000 : ℝ)*base66 + (1544443051088521583/1152375000000000000000000000000000 : ℝ)*base68 + (2424056096171146583/1152375000000000000000000000000000 : ℝ)*base70 + (1913380872922396583/1152375000000000000000000000000000 : ℝ)*base72 + (262907976648701/138285000000000000000000000000 : ℝ)*base74 + (6028902241649521583/1152375000000000000000000000000000 : ℝ)*base76 + (4298763101355271583/1152375000000000000000000000000000 : ℝ)*base78 + (6679347356045353417/1152375000000000000000000000000000 : ℝ)*base79 + (1396494679127/4321406250000000000000000000 : ℝ)*base81 + (22556197/5000000000000000000000 : ℝ)*base90 + (22556197/5000000000000000000000 : ℝ)*base92 + (22556197/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12078231020207071507687756917/1536500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92545361/100000000000000 : ℝ)*(base1) + (874462559/50000000000000 : ℝ)*(base19) + (354701623/20000000000000 : ℝ)*(base23) + (43902013/25000000000000 : ℝ)*(upper3) + (17779971/10000000000000 : ℝ)*(upper5) + (1083811074910047/100000000000000 : ℝ)*(major0) + (1083811074910047/100000000000000 : ℝ)*(major1) + (1083811074910047/100000000000000 : ℝ)*(major2) + (7036123861/100000000000000 : ℝ)*(sp1) + (752752337/10000000000000 : ℝ)*(sp2) + (719748840688189/50000000000000 : ℝ)*(sp4) + (1439488803782039/100000000000000 : ℝ)*(sp5) + (719744143899767/50000000000000 : ℝ)*(sp6) + (91015525801827/12500000000000 : ℝ)*(sp7) + (728124298959977/100000000000000 : ℝ)*(f.failure) + (719748794415509/50000000000000 : ℝ)*(f.sum) + (3654610076207/3841250000000000000000000000 : ℝ)*base66 + (17361976958113785639/3073000000000000000000000000000000 : ℝ)*base67 + (8345780957525785639/3073000000000000000000000000000000 : ℝ)*base69 + (5497729224675214361/3073000000000000000000000000000000 : ℝ)*base72 + (4494722555579/1920625000000000000000000000 : ℝ)*base73 + (17585297383411214361/3073000000000000000000000000000000 : ℝ)*base76 + (14823995636172214361/3073000000000000000000000000000000 : ℝ)*base78 + (27779498282622214361/3073000000000000000000000000000000 : ℝ)*base80 + (23991325341453/3841250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (54136141/10000000000000000000000 : ℝ)*base89 + (54136141/10000000000000000000000 : ℝ)*base91 + (54136141/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1110_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13969/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5469/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2573/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1110_s2_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081961197/5000000000 : ℝ)*x 0 + (5517007891/10000000000 : ℝ)*x 1 + (2576860277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081961197/5000000000 : ℝ)^8303 ≤ (6554775216023/50000000000000 : ℝ)^6255 := by
    have hnat : (1081961197 : ℕ)^8303*50000000000000^6255 ≤ 6554775216023^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081961197 5000000000 6554775216023 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5517007891/10000000000 : ℝ)^8303 ≤ (11352008505833/25000000000000 : ℝ)^6255 := by
    have hnat : (5517007891 : ℕ)^8303*25000000000000^6255 ≤ 11352008505833^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517007891 10000000000 11352008505833 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576860277/5000000000 : ℝ)^8303 ≤ (20741207761453/50000000000000 : ℝ)^6255 := by
    have hnat : (2576860277 : ℕ)^8303*50000000000000^6255 ≤ 20741207761453^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576860277 5000000000 20741207761453 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081961197/5000000000 : ℝ), (5517007891/10000000000 : ℝ), (2576860277/5000000000 : ℝ)] ![(6554775216023/50000000000000 : ℝ), (11352008505833/25000000000000 : ℝ), (20741207761453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081961197/5000000000 : ℝ)|^8303 ≤ (6554775216023/50000000000000 : ℝ)^6255
        have hw : |(-1081961197/5000000000 : ℝ)|=(1081961197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5517007891/10000000000 : ℝ)|^8303 ≤ (11352008505833/25000000000000 : ℝ)^6255
        have hw : |(5517007891/10000000000 : ℝ)|=(5517007891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576860277/5000000000 : ℝ)|^8303 ≤ (20741207761453/50000000000000 : ℝ)^6255
        have hw : |(2576860277/5000000000 : ℝ)|=(2576860277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s2_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5375252681/10000000000 : ℝ)*x 0 + (-2353036189/10000000000 : ℝ)*x 1 + (2576860909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375252681/10000000000 : ℝ)^8303 ≤ (10966464003571/25000000000000 : ℝ)^6255 := by
    have hnat : (5375252681 : ℕ)^8303*25000000000000^6255 ≤ 10966464003571^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375252681 10000000000 10966464003571 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2353036189/10000000000 : ℝ)^8303 ≤ (2930342987363/20000000000000 : ℝ)^6255 := by
    have hnat : (2353036189 : ℕ)^8303*20000000000000^6255 ≤ 2930342987363^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353036189 10000000000 2930342987363 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576860909/5000000000 : ℝ)^8303 ≤ (10370607257003/25000000000000 : ℝ)^6255 := by
    have hnat : (2576860909 : ℕ)^8303*25000000000000^6255 ≤ 10370607257003^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576860909 5000000000 10370607257003 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375252681/10000000000 : ℝ), (-2353036189/10000000000 : ℝ), (2576860909/5000000000 : ℝ)] ![(10966464003571/25000000000000 : ℝ), (2930342987363/20000000000000 : ℝ), (10370607257003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375252681/10000000000 : ℝ)|^8303 ≤ (10966464003571/25000000000000 : ℝ)^6255
        have hw : |(5375252681/10000000000 : ℝ)|=(5375252681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2353036189/10000000000 : ℝ)|^8303 ≤ (2930342987363/20000000000000 : ℝ)^6255
        have hw : |(-2353036189/10000000000 : ℝ)|=(2353036189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576860909/5000000000 : ℝ)|^8303 ≤ (10370607257003/25000000000000 : ℝ)^6255
        have hw : |(2576860909/5000000000 : ℝ)|=(2576860909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s2_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5375252627/10000000000 : ℝ)*x 0 + (1649191/3200000 : ℝ)*x 1 + (-2353036187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375252627/10000000000 : ℝ)^8303 ≤ (1096646385733/2500000000000 : ℝ)^6255 := by
    have hnat : (5375252627 : ℕ)^8303*2500000000000^6255 ≤ 1096646385733^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375252627 10000000000 1096646385733 2500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1649191/3200000 : ℝ)^8303 ≤ (1296325926157/3125000000000 : ℝ)^6255 := by
    have hnat : (1649191 : ℕ)^8303*3125000000000^6255 ≤ 1296325926157^6255*3200000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649191 3200000 1296325926157 3125000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2353036187/10000000000 : ℝ)^8303 ≤ (3662928730071/25000000000000 : ℝ)^6255 := by
    have hnat : (2353036187 : ℕ)^8303*25000000000000^6255 ≤ 3662928730071^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353036187 10000000000 3662928730071 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375252627/10000000000 : ℝ), (1649191/3200000 : ℝ), (-2353036187/10000000000 : ℝ)] ![(1096646385733/2500000000000 : ℝ), (1296325926157/3125000000000 : ℝ), (3662928730071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375252627/10000000000 : ℝ)|^8303 ≤ (1096646385733/2500000000000 : ℝ)^6255
        have hw : |(5375252627/10000000000 : ℝ)|=(5375252627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1649191/3200000 : ℝ)|^8303 ≤ (1296325926157/3125000000000 : ℝ)^6255
        have hw : |(1649191/3200000 : ℝ)|=(1649191/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2353036187/10000000000 : ℝ)|^8303 ≤ (3662928730071/25000000000000 : ℝ)^6255
        have hw : |(-2353036187/10000000000 : ℝ)|=(2353036187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s2_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357764117/10000000000 : ℝ)*x 0 + (100335713/250000000 : ℝ)*x 1 + (473164281/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357764117/10000000000 : ℝ)^8303 ≤ (16600537395499/50000000000000 : ℝ)^6255 := by
    have hnat : (4357764117 : ℕ)^8303*50000000000000^6255 ≤ 16600537395499^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357764117 10000000000 16600537395499 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100335713/250000000 : ℝ)^8303 ≤ (1488227617029/5000000000000 : ℝ)^6255 := by
    have hnat : (100335713 : ℕ)^8303*5000000000000^6255 ≤ 1488227617029^6255*250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100335713 250000000 1488227617029 5000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473164281/1000000000 : ℝ)^8303 ≤ (18517186425773/50000000000000 : ℝ)^6255 := by
    have hnat : (473164281 : ℕ)^8303*50000000000000^6255 ≤ 18517186425773^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473164281 1000000000 18517186425773 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357764117/10000000000 : ℝ), (100335713/250000000 : ℝ), (473164281/1000000000 : ℝ)] ![(16600537395499/50000000000000 : ℝ), (1488227617029/5000000000000 : ℝ), (18517186425773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357764117/10000000000 : ℝ)|^8303 ≤ (16600537395499/50000000000000 : ℝ)^6255
        have hw : |(4357764117/10000000000 : ℝ)|=(4357764117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100335713/250000000 : ℝ)|^8303 ≤ (1488227617029/5000000000000 : ℝ)^6255
        have hw : |(100335713/250000000 : ℝ)|=(100335713/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(473164281/1000000000 : ℝ)|^8303 ≤ (18517186425773/50000000000000 : ℝ)^6255
        have hw : |(473164281/1000000000 : ℝ)|=(473164281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s2_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-54100849/250000000 : ℝ)*x 0 + (5156282801/10000000000 : ℝ)*x 1 + (5514419633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54100849/250000000 : ℝ)^8303 ≤ (6555223816131/50000000000000 : ℝ)^6255 := by
    have hnat : (54100849 : ℕ)^8303*50000000000000^6255 ≤ 6555223816131^6255*250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54100849 250000000 6555223816131 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5156282801/10000000000 : ℝ)^8303 ≤ (10377448467581/25000000000000 : ℝ)^6255 := by
    have hnat : (5156282801 : ℕ)^8303*25000000000000^6255 ≤ 10377448467581^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156282801 10000000000 10377448467581 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5514419633/10000000000 : ℝ)^8303 ≤ (22689879237907/50000000000000 : ℝ)^6255 := by
    have hnat : (5514419633 : ℕ)^8303*50000000000000^6255 ≤ 22689879237907^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514419633 10000000000 22689879237907 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54100849/250000000 : ℝ), (5156282801/10000000000 : ℝ), (5514419633/10000000000 : ℝ)] ![(6555223816131/50000000000000 : ℝ), (10377448467581/25000000000000 : ℝ), (22689879237907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54100849/250000000 : ℝ)|^8303 ≤ (6555223816131/50000000000000 : ℝ)^6255
        have hw : |(-54100849/250000000 : ℝ)|=(54100849/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5156282801/10000000000 : ℝ)|^8303 ≤ (10377448467581/25000000000000 : ℝ)^6255
        have hw : |(5156282801/10000000000 : ℝ)|=(5156282801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5514419633/10000000000 : ℝ)|^8303 ≤ (22689879237907/50000000000000 : ℝ)^6255
        have hw : |(5514419633/10000000000 : ℝ)|=(5514419633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s2_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5283275533/10000000000 : ℝ)*x 0 + (-1992337763/10000000000 : ℝ)*x 1 + (5514419717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283275533/10000000000 : ℝ)^8303 ≤ (5359037489459/12500000000000 : ℝ)^6255 := by
    have hnat : (5283275533 : ℕ)^8303*12500000000000^6255 ≤ 5359037489459^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283275533 10000000000 5359037489459 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1992337763/10000000000 : ℝ)^8303 ≤ (11747940671343/100000000000000 : ℝ)^6255 := by
    have hnat : (1992337763 : ℕ)^8303*100000000000000^6255 ≤ 11747940671343^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992337763 10000000000 11747940671343 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5514419717/10000000000 : ℝ)^8303 ≤ (22689879696703/50000000000000 : ℝ)^6255 := by
    have hnat : (5514419717 : ℕ)^8303*50000000000000^6255 ≤ 22689879696703^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514419717 10000000000 22689879696703 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283275533/10000000000 : ℝ), (-1992337763/10000000000 : ℝ), (5514419717/10000000000 : ℝ)] ![(5359037489459/12500000000000 : ℝ), (11747940671343/100000000000000 : ℝ), (22689879696703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283275533/10000000000 : ℝ)|^8303 ≤ (5359037489459/12500000000000 : ℝ)^6255
        have hw : |(5283275533/10000000000 : ℝ)|=(5283275533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1992337763/10000000000 : ℝ)|^8303 ≤ (11747940671343/100000000000000 : ℝ)^6255
        have hw : |(-1992337763/10000000000 : ℝ)|=(1992337763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5514419717/10000000000 : ℝ)|^8303 ≤ (22689879696703/50000000000000 : ℝ)^6255
        have hw : |(5514419717/10000000000 : ℝ)|=(5514419717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s2_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5283275669/10000000000 : ℝ)*x 0 + (5514419663/10000000000 : ℝ)*x 1 + (-1992337653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283275669/10000000000 : ℝ)^8303 ≤ (42872301380613/100000000000000 : ℝ)^6255 := by
    have hnat : (5283275669 : ℕ)^8303*100000000000000^6255 ≤ 42872301380613^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283275669 10000000000 42872301380613 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514419663/10000000000 : ℝ)^8303 ≤ (22689879401763/50000000000000 : ℝ)^6255 := by
    have hnat : (5514419663 : ℕ)^8303*50000000000000^6255 ≤ 22689879401763^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514419663 10000000000 22689879401763 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1992337653/10000000000 : ℝ)^8303 ≤ (11747939810351/100000000000000 : ℝ)^6255 := by
    have hnat : (1992337653 : ℕ)^8303*100000000000000^6255 ≤ 11747939810351^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992337653 10000000000 11747939810351 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283275669/10000000000 : ℝ), (5514419663/10000000000 : ℝ), (-1992337653/10000000000 : ℝ)] ![(42872301380613/100000000000000 : ℝ), (22689879401763/50000000000000 : ℝ), (11747939810351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283275669/10000000000 : ℝ)|^8303 ≤ (42872301380613/100000000000000 : ℝ)^6255
        have hw : |(5283275669/10000000000 : ℝ)|=(5283275669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514419663/10000000000 : ℝ)|^8303 ≤ (22689879401763/50000000000000 : ℝ)^6255
        have hw : |(5514419663/10000000000 : ℝ)|=(5514419663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1992337653/10000000000 : ℝ)|^8303 ≤ (11747939810351/100000000000000 : ℝ)^6255
        have hw : |(-1992337653/10000000000 : ℝ)|=(1992337653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s2_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089496509/2500000000 : ℝ)*x 0 + (472657843/1000000000 : ℝ)*x 1 + (502317923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089496509/2500000000 : ℝ)^8303 ≤ (33203319159969/100000000000000 : ℝ)^6255 := by
    have hnat : (1089496509 : ℕ)^8303*100000000000000^6255 ≤ 33203319159969^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089496509 2500000000 33203319159969 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472657843/1000000000 : ℝ)^8303 ≤ (36981764956091/100000000000000 : ℝ)^6255 := by
    have hnat : (472657843 : ℕ)^8303*100000000000000^6255 ≤ 36981764956091^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472657843 1000000000 36981764956091 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502317923/1250000000 : ℝ)^8303 ≤ (5962983175261/20000000000000 : ℝ)^6255 := by
    have hnat : (502317923 : ℕ)^8303*20000000000000^6255 ≤ 5962983175261^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502317923 1250000000 5962983175261 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089496509/2500000000 : ℝ), (472657843/1000000000 : ℝ), (502317923/1250000000 : ℝ)] ![(33203319159969/100000000000000 : ℝ), (36981764956091/100000000000000 : ℝ), (5962983175261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089496509/2500000000 : ℝ)|^8303 ≤ (33203319159969/100000000000000 : ℝ)^6255
        have hw : |(1089496509/2500000000 : ℝ)|=(1089496509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(472657843/1000000000 : ℝ)|^8303 ≤ (36981764956091/100000000000000 : ℝ)^6255
        have hw : |(472657843/1000000000 : ℝ)|=(472657843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502317923/1250000000 : ℝ)|^8303 ≤ (5962983175261/20000000000000 : ℝ)^6255
        have hw : |(502317923/1250000000 : ℝ)|=(502317923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2573/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8923/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (83/500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2573/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5469/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2573/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5469/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2573/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5469/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2573/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5469/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2573/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5469/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2573/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5469/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5469/100000 : ℝ) ^ (4151/1024 : ℝ) ≤ (765320849418267/100000000000000000000 : ℝ) := by
    have hpowers : (5469/100000 : ℝ)^4151 ≤ (765320849418267/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5469 : ℕ)^4151*100000000000000000000^1024 ≤ 765320849418267^1024*100000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5469 100000 765320849418267 100000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5469/100000 : ℝ)) (X := (765320849418267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2573/12500 : ℝ) ^ (4151/1024 : ℝ) ≤ (32982086703445497/20000000000000000000 : ℝ) := by
    have hpowers : (2573/12500 : ℝ)^4151 ≤ (32982086703445497/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2573 : ℕ)^4151*20000000000000000000^1024 ≤ 32982086703445497^1024*12500^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2573 12500 32982086703445497 20000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2573/12500 : ℝ)) (X := (32982086703445497/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000765320849418267/50000000000000000000 : ℝ) ≤ (5000018879403317/5000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50000765320849418267/50000000000000000000 : ℝ)^1024 ≤ (5000018879403317/5000000000000000 : ℝ)^4151 := by
      have hnat : (50000765320849418267 : ℕ)^1024*5000000000000000^4151 ≤ 5000018879403317^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000765320849418267 50000000000000000000 5000018879403317 5000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000018879403317/5000000000000000 : ℝ)) (X := (50000765320849418267/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12520709469295830719/12500000000000000000 : ℝ) ≤ (10004084466568883/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (12520709469295830719/12500000000000000000 : ℝ)^1024 ≤ (10004084466568883/10000000000000000 : ℝ)^4151 := by
      have hnat : (12520709469295830719 : ℕ)^1024*10000000000000000^4151 ≤ 10004084466568883^4151*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12520709469295830719 12500000000000000000 10004084466568883 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004084466568883/10000000000000000 : ℝ)) (X := (12520709469295830719/12500000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10032982086703445497/10000000000000000000 : ℝ) ≤ (2502032793582783/2500000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (10032982086703445497/10000000000000000000 : ℝ)^1024 ≤ (2502032793582783/2500000000000000 : ℝ)^4151 := by
      have hnat : (10032982086703445497 : ℕ)^1024*2500000000000000^4151 ≤ 2502032793582783^4151*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10032982086703445497 10000000000000000000 2502032793582783 2500000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502032793582783/2500000000000000 : ℝ)) (X := (10032982086703445497/10000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(765320849418267/100000000000000000000 : ℝ) ≤ ((37776576958714698337/37787500000000000000 : ℝ)+2*(4046707762249/1511500000000000 : ℝ)*(5469/100000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (37776576958714698337/37787500000000000000 : ℝ)+2*(4046707762249/1511500000000000 : ℝ)*(5469/100000 : ℝ)=(5000018879403317/5000000000000000 : ℝ) by norm_num, show 1+2*(765320849418267/100000000000000000000 : ℝ)=(50000765320849418267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32982086703445497/20000000000000000000 : ℝ)+(765320849418267/100000000000000000000 : ℝ) ≤ ((37776576958714698337/37787500000000000000 : ℝ)+(4046707762249/1511500000000000 : ℝ)*((2573/12500 : ℝ)+(5469/100000 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (37776576958714698337/37787500000000000000 : ℝ)+(4046707762249/1511500000000000 : ℝ)*((2573/12500 : ℝ)+(5469/100000 : ℝ))=(10004084466568883/10000000000000000 : ℝ) by norm_num, show 1+(32982086703445497/20000000000000000000 : ℝ)+(765320849418267/100000000000000000000 : ℝ)=(12520709469295830719/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32982086703445497/20000000000000000000 : ℝ) ≤ ((37776576958714698337/37787500000000000000 : ℝ)+2*(4046707762249/1511500000000000 : ℝ)*(2573/12500 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (37776576958714698337/37787500000000000000 : ℝ)+2*(4046707762249/1511500000000000 : ℝ)*(2573/12500 : ℝ)=(2502032793582783/2500000000000000 : ℝ) by norm_num, show 1+2*(32982086703445497/20000000000000000000 : ℝ)=(10032982086703445497/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37776576958714698337/37787500000000000000 : ℝ)*(X 1 0+X 2 0)+(4046707762249/1511500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (5469/100000 : ℝ)) (hi := (2573/12500 : ℝ)) (c := (37776576958714698337/37787500000000000000 : ℝ)) (alpha := (4046707762249/1511500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37776576958714698337/37787500000000000000 : ℝ)*(X 0 1+X 2 1)+(4046707762249/1511500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (5469/100000 : ℝ)) (hi := (2573/12500 : ℝ)) (c := (37776576958714698337/37787500000000000000 : ℝ)) (alpha := (4046707762249/1511500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37776576958714698337/37787500000000000000 : ℝ)*(X 0 2+X 1 2)+(4046707762249/1511500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (5469/100000 : ℝ)) (hi := (2573/12500 : ℝ)) (c := (37776576958714698337/37787500000000000000 : ℝ)) (alpha := (4046707762249/1511500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1081961197/5000000000 : ℝ)*X 0 0+(5517007891/10000000000 : ℝ)*X 0 1+(2576860277/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375252681/10000000000 : ℝ)*X 1 0+(-2353036189/10000000000 : ℝ)*X 1 1+(2576860909/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375252627/10000000000 : ℝ)*X 2 0+(1649191/3200000 : ℝ)*X 2 1+(-2353036187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357764117/10000000000 : ℝ)*X 0 0+(100335713/250000000 : ℝ)*X 0 1+(473164281/1000000000 : ℝ)*X 0 2+(4357764117/10000000000 : ℝ)*X 1 0+(100335713/250000000 : ℝ)*X 1 1+(473164281/1000000000 : ℝ)*X 1 2+(4357764117/10000000000 : ℝ)*X 2 0+(100335713/250000000 : ℝ)*X 2 1+(473164281/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-54100849/250000000 : ℝ)*X 0 0+(5156282801/10000000000 : ℝ)*X 0 1+(5514419633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283275533/10000000000 : ℝ)*X 1 0+(-1992337763/10000000000 : ℝ)*X 1 1+(5514419717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5283275669/10000000000 : ℝ)*X 2 0+(5514419663/10000000000 : ℝ)*X 2 1+(-1992337653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089496509/2500000000 : ℝ)*X 0 0+(472657843/1000000000 : ℝ)*X 0 1+(502317923/1250000000 : ℝ)*X 0 2+(1089496509/2500000000 : ℝ)*X 1 0+(472657843/1000000000 : ℝ)*X 1 1+(502317923/1250000000 : ℝ)*X 1 2+(1089496509/2500000000 : ℝ)*X 2 0+(472657843/1000000000 : ℝ)*X 2 1+(502317923/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12527642559604767293494129989/1889375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (310148909/50000000000000 : ℝ)*(base19) + (361903351/100000000000000 : ℝ)*(base23) + (1814027/20000000000000 : ℝ)*(upper2) + (726581/400000000000 : ℝ)*(upper3) + (33274819/25000000000000 : ℝ)*(upper4) + (2072510346404781/100000000000000 : ℝ)*(major0) + (2072510346404781/100000000000000 : ℝ)*(major1) + (1036255173202391/50000000000000 : ℝ)*(major2) + (172041049732849/6250000000000 : ℝ)*(sp0) + (172041819993511/6250000000000 : ℝ)*(sp1) + (2752669378290643/100000000000000 : ℝ)*(sp2) + (1392345538906303/100000000000000 : ℝ)*(sp3) + (12944468411/100000000000000 : ℝ)*(sp4) + (1298172523/25000000000000 : ℝ)*(sp7) + (348087682899099/25000000000000 : ℝ)*(f.failure) + (1376334870096997/50000000000000 : ℝ)*(f.sum) + (697661674564137/151150000000000000000000000000 : ℝ)*base65 + (28737639816128750803/3778750000000000000000000000000000 : ℝ)*base68 + (10810024404898611267/1889375000000000000000000000000000 : ℝ)*base69 + (19306533328268750803/3778750000000000000000000000000000 : ℝ)*base72 + (404937820752787/151150000000000000000000000000 : ℝ)*base73 + (21816009257281736267/1889375000000000000000000000000000 : ℝ)*base75 + (777032528593725803/3778750000000000000000000000000000 : ℝ)*base78 + (11929245526552524197/3778750000000000000000000000000000 : ℝ)*base79 + (232444238770097/37787500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (27090567/2500000000000000000000 : ℝ)*base89 + (27090567/2500000000000000000000 : ℝ)*base91 + (2090567/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3242649151314743570318432787/472343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68810209/5000000000000 : ℝ)*(base19) + (792805647/50000000000000 : ℝ)*(base23) + (186618703/100000000000000 : ℝ)*(upper3) + (24001197/50000000000000 : ℝ)*(lower4) + (32569459/25000000000000 : ℝ)*(upper5) + (525573492374461/25000000000000 : ℝ)*(major0) + (525573492374461/25000000000000 : ℝ)*(major1) + (525573492374461/25000000000000 : ℝ)*(major2) + (6295343627/50000000000000 : ℝ)*(sp1) + (15271697527/100000000000000 : ℝ)*(sp2) + (2792227790444641/100000000000000 : ℝ)*(sp4) + (2792213823553207/100000000000000 : ℝ)*(sp5) + (139610546656791/5000000000000 : ℝ)*(sp6) + (28247198394341/2000000000000 : ℝ)*(sp7) + (28247198394341/2000000000000 : ℝ)*(f.failure) + (2792227790444641/100000000000000 : ℝ)*(f.sum) + (14581755884211/18893750000000000000000000000 : ℝ)*base66 + (7311413043451758857/944687500000000000000000000000000 : ℝ)*base67 + (1920286466803008857/944687500000000000000000000000000 : ℝ)*base69 + (3698006818210508857/944687500000000000000000000000000 : ℝ)*base71 + (266854432798181/75575000000000000000000000000 : ℝ)*base73 + (1822366359592383857/944687500000000000000000000000000 : ℝ)*base75 + (4574955780650508857/944687500000000000000000000000000 : ℝ)*base77 + (4656829507229258857/944687500000000000000000000000000 : ℝ)*base79 + (199840822881331/75575000000000000000000000000 : ℝ)*base81 + (1439047/200000000000000000000 : ℝ)*base90 + (1439047/200000000000000000000 : ℝ)*base92 + (1439047/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1110_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2573/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (83/500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1110_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (83/500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1110_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1110_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1110_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8923/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (83/500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1110_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

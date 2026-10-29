-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1596_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:48.604985+00:00
-- url     : https://prove2.me/submissions/08ef95b9-ea08-4169-8ea8-6ced23385b8b

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
theorem support_rectangle_w1596_s0_0 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99521089/625000000 : ℝ)*x 0 + (2928187133/5000000000 : ℝ)*x 1 + (1220587723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99521089/625000000 : ℝ)^4703 ≤ (4774219103739/50000000000000 : ℝ)^3679 := by
    have hnat : (99521089 : ℕ)^4703*50000000000000^3679 ≤ 4774219103739^3679*625000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99521089 625000000 4774219103739 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2928187133/5000000000 : ℝ)^4703 ≤ (50460487578883/100000000000000 : ℝ)^3679 := by
    have hnat : (2928187133 : ℕ)^4703*100000000000000^3679 ≤ 50460487578883^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2928187133 5000000000 50460487578883 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1220587723/2500000000 : ℝ)^4703 ≤ (9997768549317/25000000000000 : ℝ)^3679 := by
    have hnat : (1220587723 : ℕ)^4703*25000000000000^3679 ≤ 9997768549317^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220587723 2500000000 9997768549317 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99521089/625000000 : ℝ), (2928187133/5000000000 : ℝ), (1220587723/2500000000 : ℝ)] ![(4774219103739/50000000000000 : ℝ), (50460487578883/100000000000000 : ℝ), (9997768549317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99521089/625000000 : ℝ)|^4703 ≤ (4774219103739/50000000000000 : ℝ)^3679
        have hw : |(-99521089/625000000 : ℝ)|=(99521089/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2928187133/5000000000 : ℝ)|^4703 ≤ (50460487578883/100000000000000 : ℝ)^3679
        have hw : |(2928187133/5000000000 : ℝ)|=(2928187133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1220587723/2500000000 : ℝ)|^4703 ≤ (9997768549317/25000000000000 : ℝ)^3679
        have hw : |(1220587723/2500000000 : ℝ)|=(1220587723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s0_1 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10663133/19531250 : ℝ)*x 0 + (-426670549/2000000000 : ℝ)*x 1 + (4882350677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10663133/19531250 : ℝ)^4703 ≤ (46131265580087/100000000000000 : ℝ)^3679 := by
    have hnat : (10663133 : ℕ)^4703*100000000000000^3679 ≤ 46131265580087^3679*19531250^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10663133 19531250 46131265580087 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426670549/2000000000 : ℝ)^4703 ≤ (216838475919/1562500000000 : ℝ)^3679 := by
    have hnat : (426670549 : ℕ)^4703*1562500000000^3679 ≤ 216838475919^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426670549 2000000000 216838475919 1562500000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4882350677/10000000000 : ℝ)^4703 ≤ (39991071946049/100000000000000 : ℝ)^3679 := by
    have hnat : (4882350677 : ℕ)^4703*100000000000000^3679 ≤ 39991071946049^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4882350677 10000000000 39991071946049 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10663133/19531250 : ℝ), (-426670549/2000000000 : ℝ), (4882350677/10000000000 : ℝ)] ![(46131265580087/100000000000000 : ℝ), (216838475919/1562500000000 : ℝ), (39991071946049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10663133/19531250 : ℝ)|^4703 ≤ (46131265580087/100000000000000 : ℝ)^3679
        have hw : |(10663133/19531250 : ℝ)|=(10663133/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426670549/2000000000 : ℝ)|^4703 ≤ (216838475919/1562500000000 : ℝ)^3679
        have hw : |(-426670549/2000000000 : ℝ)|=(426670549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4882350677/10000000000 : ℝ)|^4703 ≤ (39991071946049/100000000000000 : ℝ)^3679
        have hw : |(4882350677/10000000000 : ℝ)|=(4882350677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s0_2 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2729762031/5000000000 : ℝ)*x 0 + (4882350663/10000000000 : ℝ)*x 1 + (-1066676403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2729762031/5000000000 : ℝ)^4703 ≤ (9226253042567/20000000000000 : ℝ)^3679 := by
    have hnat : (2729762031 : ℕ)^4703*20000000000000^3679 ≤ 9226253042567^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729762031 5000000000 9226253042567 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4882350663/10000000000 : ℝ)^4703 ≤ (19995535899729/50000000000000 : ℝ)^3679 := by
    have hnat : (4882350663 : ℕ)^4703*50000000000000^3679 ≤ 19995535899729^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4882350663 10000000000 19995535899729 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066676403/5000000000 : ℝ)^4703 ≤ (13877662966073/100000000000000 : ℝ)^3679 := by
    have hnat : (1066676403 : ℕ)^4703*100000000000000^3679 ≤ 13877662966073^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066676403 5000000000 13877662966073 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2729762031/5000000000 : ℝ), (4882350663/10000000000 : ℝ), (-1066676403/5000000000 : ℝ)] ![(9226253042567/20000000000000 : ℝ), (19995535899729/50000000000000 : ℝ), (13877662966073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2729762031/5000000000 : ℝ)|^4703 ≤ (9226253042567/20000000000000 : ℝ)^3679
        have hw : |(2729762031/5000000000 : ℝ)|=(2729762031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4882350663/10000000000 : ℝ)|^4703 ≤ (19995535899729/50000000000000 : ℝ)^3679
        have hw : |(4882350663/10000000000 : ℝ)|=(4882350663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066676403/5000000000 : ℝ)|^4703 ≤ (13877662966073/100000000000000 : ℝ)^3679
        have hw : |(-1066676403/5000000000 : ℝ)|=(1066676403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s0_3 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4116713031/10000000000 : ℝ)*x 0 + (614450487/2000000000 : ℝ)*x 1 + (1084339623/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4116713031/10000000000 : ℝ)^4703 ≤ (32156291271419/100000000000000 : ℝ)^3679 := by
    have hnat : (4116713031 : ℕ)^4703*100000000000000^3679 ≤ 32156291271419^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116713031 10000000000 32156291271419 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (614450487/2000000000 : ℝ)^4703 ≤ (22120627445613/100000000000000 : ℝ)^3679 := by
    have hnat : (614450487 : ℕ)^4703*100000000000000^3679 ≤ 22120627445613^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614450487 2000000000 22120627445613 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084339623/2000000000 : ℝ)^4703 ≤ (914461625241/2000000000000 : ℝ)^3679 := by
    have hnat : (1084339623 : ℕ)^4703*2000000000000^3679 ≤ 914461625241^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084339623 2000000000 914461625241 2000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4116713031/10000000000 : ℝ), (614450487/2000000000 : ℝ), (1084339623/2000000000 : ℝ)] ![(32156291271419/100000000000000 : ℝ), (22120627445613/100000000000000 : ℝ), (914461625241/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4116713031/10000000000 : ℝ)|^4703 ≤ (32156291271419/100000000000000 : ℝ)^3679
        have hw : |(4116713031/10000000000 : ℝ)|=(4116713031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(614450487/2000000000 : ℝ)|^4703 ≤ (22120627445613/100000000000000 : ℝ)^3679
        have hw : |(614450487/2000000000 : ℝ)|=(614450487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084339623/2000000000 : ℝ)|^4703 ≤ (914461625241/2000000000000 : ℝ)^3679
        have hw : |(1084339623/2000000000 : ℝ)|=(1084339623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s0_4 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1595327423/10000000000 : ℝ)*x 0 + (2453581771/5000000000 : ℝ)*x 1 + (5830672827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1595327423/10000000000 : ℝ)^4703 ≤ (9571364134117/100000000000000 : ℝ)^3679 := by
    have hnat : (1595327423 : ℕ)^4703*100000000000000^3679 ≤ 9571364134117^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595327423 10000000000 9571364134117 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2453581771/5000000000 : ℝ)^4703 ≤ (4025106566839/10000000000000 : ℝ)^3679 := by
    have hnat : (2453581771 : ℕ)^4703*10000000000000^3679 ≤ 4025106566839^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453581771 5000000000 4025106566839 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5830672827/10000000000 : ℝ)^4703 ≤ (2007102807649/4000000000000 : ℝ)^3679 := by
    have hnat : (5830672827 : ℕ)^4703*4000000000000^3679 ≤ 2007102807649^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5830672827 10000000000 2007102807649 4000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1595327423/10000000000 : ℝ), (2453581771/5000000000 : ℝ), (5830672827/10000000000 : ℝ)] ![(9571364134117/100000000000000 : ℝ), (4025106566839/10000000000000 : ℝ), (2007102807649/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1595327423/10000000000 : ℝ)|^4703 ≤ (9571364134117/100000000000000 : ℝ)^3679
        have hw : |(-1595327423/10000000000 : ℝ)|=(1595327423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2453581771/5000000000 : ℝ)|^4703 ≤ (4025106566839/10000000000000 : ℝ)^3679
        have hw : |(2453581771/5000000000 : ℝ)|=(2453581771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5830672827/10000000000 : ℝ)|^4703 ≤ (2007102807649/4000000000000 : ℝ)^3679
        have hw : |(5830672827/10000000000 : ℝ)|=(5830672827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s0_5 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193485059/10000000000 : ℝ)*x 0 + (-592515107/5000000000 : ℝ)*x 1 + (182208531/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193485059/10000000000 : ℝ)^4703 ≤ (5409669346273/12500000000000 : ℝ)^3679 := by
    have hnat : (5193485059 : ℕ)^4703*12500000000000^3679 ≤ 5409669346273^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193485059 10000000000 5409669346273 12500000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (592515107/5000000000 : ℝ)^4703 ≤ (6545073213343/100000000000000 : ℝ)^3679 := by
    have hnat : (592515107 : ℕ)^4703*100000000000000^3679 ≤ 6545073213343^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592515107 5000000000 6545073213343 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182208531/312500000 : ℝ)^4703 ≤ (50177572006407/100000000000000 : ℝ)^3679 := by
    have hnat : (182208531 : ℕ)^4703*100000000000000^3679 ≤ 50177572006407^3679*312500000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182208531 312500000 50177572006407 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193485059/10000000000 : ℝ), (-592515107/5000000000 : ℝ), (182208531/312500000 : ℝ)] ![(5409669346273/12500000000000 : ℝ), (6545073213343/100000000000000 : ℝ), (50177572006407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193485059/10000000000 : ℝ)|^4703 ≤ (5409669346273/12500000000000 : ℝ)^3679
        have hw : |(5193485059/10000000000 : ℝ)|=(5193485059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-592515107/5000000000 : ℝ)|^4703 ≤ (6545073213343/100000000000000 : ℝ)^3679
        have hw : |(-592515107/5000000000 : ℝ)|=(592515107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182208531/312500000 : ℝ)|^4703 ≤ (50177572006407/100000000000000 : ℝ)^3679
        have hw : |(182208531/312500000 : ℝ)|=(182208531/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s0_6 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596742541/5000000000 : ℝ)*x 0 + (91104263/156250000 : ℝ)*x 1 + (-1185030429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596742541/5000000000 : ℝ)^4703 ≤ (43277355015189/100000000000000 : ℝ)^3679 := by
    have hnat : (2596742541 : ℕ)^4703*100000000000000^3679 ≤ 43277355015189^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596742541 5000000000 43277355015189 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91104263/156250000 : ℝ)^4703 ≤ (50177570246231/100000000000000 : ℝ)^3679 := by
    have hnat : (91104263 : ℕ)^4703*100000000000000^3679 ≤ 50177570246231^3679*156250000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91104263 156250000 50177570246231 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1185030429/10000000000 : ℝ)^4703 ≤ (6545074731333/100000000000000 : ℝ)^3679 := by
    have hnat : (1185030429 : ℕ)^4703*100000000000000^3679 ≤ 6545074731333^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185030429 10000000000 6545074731333 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596742541/5000000000 : ℝ), (91104263/156250000 : ℝ), (-1185030429/10000000000 : ℝ)] ![(43277355015189/100000000000000 : ℝ), (50177570246231/100000000000000 : ℝ), (6545074731333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596742541/5000000000 : ℝ)|^4703 ≤ (43277355015189/100000000000000 : ℝ)^3679
        have hw : |(2596742541/5000000000 : ℝ)|=(2596742541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91104263/156250000 : ℝ)|^4703 ≤ (50177570246231/100000000000000 : ℝ)^3679
        have hw : |(91104263/156250000 : ℝ)|=(91104263/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1185030429/10000000000 : ℝ)|^4703 ≤ (6545074731333/100000000000000 : ℝ)^3679
        have hw : |(-1185030429/10000000000 : ℝ)|=(1185030429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s0_7 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4123925867/10000000000 : ℝ)*x 0 + (2680923487/5000000000 : ℝ)*x 1 + (3134246613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4123925867/10000000000 : ℝ)^4703 ≤ (6445666212573/20000000000000 : ℝ)^3679 := by
    have hnat : (4123925867 : ℕ)^4703*20000000000000^3679 ≤ 6445666212573^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123925867 10000000000 6445666212573 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2680923487/5000000000 : ℝ)^4703 ≤ (22539420191857/50000000000000 : ℝ)^3679 := by
    have hnat : (2680923487 : ℕ)^4703*50000000000000^3679 ≤ 22539420191857^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680923487 5000000000 22539420191857 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134246613/10000000000 : ℝ)^4703 ≤ (1418301783589/6250000000000 : ℝ)^3679 := by
    have hnat : (3134246613 : ℕ)^4703*6250000000000^3679 ≤ 1418301783589^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134246613 10000000000 1418301783589 6250000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4123925867/10000000000 : ℝ), (2680923487/5000000000 : ℝ), (3134246613/10000000000 : ℝ)] ![(6445666212573/20000000000000 : ℝ), (22539420191857/50000000000000 : ℝ), (1418301783589/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4123925867/10000000000 : ℝ)|^4703 ≤ (6445666212573/20000000000000 : ℝ)^3679
        have hw : |(4123925867/10000000000 : ℝ)|=(4123925867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2680923487/5000000000 : ℝ)|^4703 ≤ (22539420191857/50000000000000 : ℝ)^3679
        have hw : |(2680923487/5000000000 : ℝ)|=(2680923487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134246613/10000000000 : ℝ)|^4703 ≤ (1418301783589/6250000000000 : ℝ)^3679
        have hw : |(3134246613/10000000000 : ℝ)|=(3134246613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1596_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (116/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24569/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4699/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4699 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4699*1^1024 ≤ 0^1024*1^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4699/1024 : ℝ) ≤ (746235930332001487/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4699 ≤ (746235930332001487/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4699*50000000000000000000^1024 ≤ 746235930332001487^1024*5^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 746235930332001487 50000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (746235930332001487/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4699 := by
      have hnat : (1 : ℕ)^1024*1^4699 ≤ 1^4699*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50746235930332001487/50000000000000000000 : ℝ) ≤ (10032335605029373/10000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (50746235930332001487/50000000000000000000 : ℝ)^1024 ≤ (10032335605029373/10000000000000000 : ℝ)^4699 := by
      have hnat : (50746235930332001487 : ℕ)^1024*10000000000000000^4699 ≤ 10032335605029373^4699*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50746235930332001487 50000000000000000000 10032335605029373 10000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032335605029373/10000000000000000 : ℝ)) (X := (50746235930332001487/50000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25746235930332001487/25000000000000000000 : ℝ) ≤ (5032335605029373/5000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (25746235930332001487/25000000000000000000 : ℝ)^1024 ≤ (5032335605029373/5000000000000000 : ℝ)^4699 := by
      have hnat : (25746235930332001487 : ℕ)^1024*5000000000000000^4699 ≤ 5032335605029373^4699*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25746235930332001487 25000000000000000000 5032335605029373 5000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5032335605029373/5000000000000000 : ℝ)) (X := (25746235930332001487/25000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(32335605029373/4000000000000000 : ℝ)*(0 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(32335605029373/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(746235930332001487/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(32335605029373/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4699/1024 : ℝ) := by
    rw [show (1 : ℝ)+(32335605029373/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10032335605029373/10000000000000000 : ℝ) by norm_num, show 1+(746235930332001487/50000000000000000000 : ℝ)+(0 : ℝ)=(50746235930332001487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(746235930332001487/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(32335605029373/4000000000000000 : ℝ)*(2/5 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(32335605029373/4000000000000000 : ℝ)*(2/5 : ℝ)=(5032335605029373/5000000000000000 : ℝ) by norm_num, show 1+2*(746235930332001487/50000000000000000000 : ℝ)=(25746235930332001487/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(32335605029373/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32335605029373/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(32335605029373/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32335605029373/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(32335605029373/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (32335605029373/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-99521089/625000000 : ℝ)*X 0 0+(2928187133/5000000000 : ℝ)*X 0 1+(1220587723/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((10663133/19531250 : ℝ)*X 1 0+(-426670549/2000000000 : ℝ)*X 1 1+(4882350677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2729762031/5000000000 : ℝ)*X 2 0+(4882350663/10000000000 : ℝ)*X 2 1+(-1066676403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4116713031/10000000000 : ℝ)*X 0 0+(614450487/2000000000 : ℝ)*X 0 1+(1084339623/2000000000 : ℝ)*X 0 2+(4116713031/10000000000 : ℝ)*X 1 0+(614450487/2000000000 : ℝ)*X 1 1+(1084339623/2000000000 : ℝ)*X 1 2+(4116713031/10000000000 : ℝ)*X 2 0+(614450487/2000000000 : ℝ)*X 2 1+(1084339623/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1595327423/10000000000 : ℝ)*X 0 0+(2453581771/5000000000 : ℝ)*X 0 1+(5830672827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5193485059/10000000000 : ℝ)*X 1 0+(-592515107/5000000000 : ℝ)*X 1 1+(182208531/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2596742541/5000000000 : ℝ)*X 2 0+(91104263/156250000 : ℝ)*X 2 1+(-1185030429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4123925867/10000000000 : ℝ)*X 0 0+(2680923487/5000000000 : ℝ)*X 0 1+(3134246613/10000000000 : ℝ)*X 0 2+(4123925867/10000000000 : ℝ)*X 1 0+(2680923487/5000000000 : ℝ)*X 1 1+(3134246613/10000000000 : ℝ)*X 1 2+(4123925867/10000000000 : ℝ)*X 2 0+(2680923487/5000000000 : ℝ)*X 2 1+(3134246613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2393908689550399539/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13645949/100000000000000 : ℝ)*(base1) + (2285119/625000000000 : ℝ)*(base19) + (35922529/10000000000000 : ℝ)*(base23) + (25818579/50000000000000 : ℝ)*(upper3) + (15538459/50000000000000 : ℝ)*(upper5) + (363076324637897/50000000000000 : ℝ)*(major0) + (363076324637897/50000000000000 : ℝ)*(major1) + (363076324637897/50000000000000 : ℝ)*(major2) + (1026670637125779/100000000000000 : ℝ)*(sp0) + (1026671383406531/100000000000000 : ℝ)*(sp1) + (25666784745007/2500000000000 : ℝ)*(sp2) + (425632841277567/100000000000000 : ℝ)*(sp3) + (56277287/5000000000000 : ℝ)*(sp4) + (122961107/20000000000000 : ℝ)*(sp7) + (8512669394581/2000000000000 : ℝ)*(f.failure) + (1026671749025571/100000000000000 : ℝ)*(f.sum) + (269540536651419/100000000000000000000000000000 : ℝ)*base66 + (308898068148581/200000000000000000000000000000 : ℝ)*base67 + (1425598072348581/200000000000000000000000000000 : ℝ)*base69 + (591022194348581/200000000000000000000000000000 : ℝ)*base71 + (634198640051419/100000000000000000000000000000 : ℝ)*base74 + (222874144548581/200000000000000000000000000000 : ℝ)*base75 + (695808917548581/200000000000000000000000000000 : ℝ)*base77 + (1914223798948581/200000000000000000000000000000 : ℝ)*base79 + (334244074051419/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1545783/200000000000000000000 : ℝ)*base90 + (1545783/200000000000000000000 : ℝ)*base92 + (1545783/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142433456185931621782533/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1223325727/100000000000000 : ℝ)*(base19) + (1978631/160000000000 : ℝ)*(base23) + (65689877/50000000000000 : ℝ)*(base32) + (104564893/50000000000000 : ℝ)*(upper3) + (50371371/50000000000000 : ℝ)*(upper5) + (95733679806769/12500000000000 : ℝ)*(major0) + (95733679806769/12500000000000 : ℝ)*(major1) + (95733679806769/12500000000000 : ℝ)*(major2) + (840382341/25000000000000 : ℝ)*(sp1) + (1763958197/50000000000000 : ℝ)*(sp2) + (541412635412557/50000000000000 : ℝ)*(sp4) + (135352585746253/12500000000000 : ℝ)*(sp5) + (541410253132173/50000000000000 : ℝ)*(sp6) + (448913284792157/100000000000000 : ℝ)*(sp7) + (448913416171911/100000000000000 : ℝ)*(f.failure) + (541412635412557/50000000000000 : ℝ)*(f.sum) + (50155888199163/25000000000000000000000000000 : ℝ)*base66 + (198678373925837/50000000000000000000000000000 : ℝ)*base67 + (16327633275837/50000000000000000000000000000 : ℝ)*base69 + (191235364724163/50000000000000000000000000000 : ℝ)*base72 + (26002130824163/25000000000000000000000000000 : ℝ)*base74 + (2817935375837/50000000000000000000000000000 : ℝ)*base75 + (67801986724163/50000000000000000000000000000 : ℝ)*base78 + (181727791374163/50000000000000000000000000000 : ℝ)*base80 + (78040996849163/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15145027/10000000000000000000000 : ℝ)*base89 + (15145027/10000000000000000000000 : ℝ)*base91 + (15145027/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1596_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (116/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24569/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1596_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1596_s1_0 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-86117467/500000000 : ℝ)*x 0 + (5543561859/10000000000 : ℝ)*x 1 + (5111213073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86117467/500000000 : ℝ)^4703 ≤ (1319519804543/12500000000000 : ℝ)^3679 := by
    have hnat : (86117467 : ℕ)^4703*12500000000000^3679 ≤ 1319519804543^3679*500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86117467 500000000 1319519804543 12500000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5543561859/10000000000 : ℝ)^4703 ≤ (1881637617539/4000000000000 : ℝ)^3679 := by
    have hnat : (5543561859 : ℕ)^4703*4000000000000^3679 ≤ 1881637617539^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5543561859 10000000000 1881637617539 4000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5111213073/10000000000 : ℝ)^4703 ≤ (8480580221541/20000000000000 : ℝ)^3679 := by
    have hnat : (5111213073 : ℕ)^4703*20000000000000^3679 ≤ 8480580221541^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111213073 10000000000 8480580221541 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86117467/500000000 : ℝ), (5543561859/10000000000 : ℝ), (5111213073/10000000000 : ℝ)] ![(1319519804543/12500000000000 : ℝ), (1881637617539/4000000000000 : ℝ), (8480580221541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86117467/500000000 : ℝ)|^4703 ≤ (1319519804543/12500000000000 : ℝ)^3679
        have hw : |(-86117467/500000000 : ℝ)|=(86117467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5543561859/10000000000 : ℝ)|^4703 ≤ (1881637617539/4000000000000 : ℝ)^3679
        have hw : |(5543561859/10000000000 : ℝ)|=(5543561859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5111213073/10000000000 : ℝ)|^4703 ≤ (8480580221541/20000000000000 : ℝ)^3679
        have hw : |(5111213073/10000000000 : ℝ)|=(5111213073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s1_1 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376227929/10000000000 : ℝ)*x 0 + (-7613363/39062500 : ℝ)*x 1 + (2555606461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376227929/10000000000 : ℝ)^4703 ≤ (1809338237917/4000000000000 : ℝ)^3679 := by
    have hnat : (5376227929 : ℕ)^4703*4000000000000^3679 ≤ 1809338237917^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376227929 10000000000 1809338237917 4000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7613363/39062500 : ℝ)^4703 ≤ (2472728906853/20000000000000 : ℝ)^3679 := by
    have hnat : (7613363 : ℕ)^4703*20000000000000^3679 ≤ 2472728906853^3679*39062500^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7613363 39062500 2472728906853 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2555606461/5000000000 : ℝ)^4703 ≤ (42402899506327/100000000000000 : ℝ)^3679 := by
    have hnat : (2555606461 : ℕ)^4703*100000000000000^3679 ≤ 42402899506327^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555606461 5000000000 42402899506327 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376227929/10000000000 : ℝ), (-7613363/39062500 : ℝ), (2555606461/5000000000 : ℝ)] ![(1809338237917/4000000000000 : ℝ), (2472728906853/20000000000000 : ℝ), (42402899506327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376227929/10000000000 : ℝ)|^4703 ≤ (1809338237917/4000000000000 : ℝ)^3679
        have hw : |(5376227929/10000000000 : ℝ)|=(5376227929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7613363/39062500 : ℝ)|^4703 ≤ (2472728906853/20000000000000 : ℝ)^3679
        have hw : |(-7613363/39062500 : ℝ)|=(7613363/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2555606461/5000000000 : ℝ)|^4703 ≤ (42402899506327/100000000000000 : ℝ)^3679
        have hw : |(2555606461/5000000000 : ℝ)|=(2555606461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s1_2 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688113801/5000000000 : ℝ)*x 0 + (5111213197/10000000000 : ℝ)*x 1 + (-1949021001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688113801/5000000000 : ℝ)^4703 ≤ (45233452430903/100000000000000 : ℝ)^3679 := by
    have hnat : (2688113801 : ℕ)^4703*100000000000000^3679 ≤ 45233452430903^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688113801 5000000000 45233452430903 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5111213197/10000000000 : ℝ)^4703 ≤ (42402902422743/100000000000000 : ℝ)^3679 := by
    have hnat : (5111213197 : ℕ)^4703*100000000000000^3679 ≤ 42402902422743^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111213197 10000000000 42402902422743 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949021001/10000000000 : ℝ)^4703 ≤ (12363645126233/100000000000000 : ℝ)^3679 := by
    have hnat : (1949021001 : ℕ)^4703*100000000000000^3679 ≤ 12363645126233^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949021001 10000000000 12363645126233 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688113801/5000000000 : ℝ), (5111213197/10000000000 : ℝ), (-1949021001/10000000000 : ℝ)] ![(45233452430903/100000000000000 : ℝ), (42402902422743/100000000000000 : ℝ), (12363645126233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688113801/5000000000 : ℝ)|^4703 ≤ (45233452430903/100000000000000 : ℝ)^3679
        have hw : |(2688113801/5000000000 : ℝ)|=(2688113801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5111213197/10000000000 : ℝ)|^4703 ≤ (42402902422743/100000000000000 : ℝ)^3679
        have hw : |(5111213197/10000000000 : ℝ)|=(5111213197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1949021001/10000000000 : ℝ)|^4703 ≤ (12363645126233/100000000000000 : ℝ)^3679
        have hw : |(-1949021001/10000000000 : ℝ)|=(1949021001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s1_3 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2105638223/5000000000 : ℝ)*x 0 + (3715162637/10000000000 : ℝ)*x 1 + (4758032641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105638223/5000000000 : ℝ)^4703 ≤ (33103536126757/100000000000000 : ℝ)^3679 := by
    have hnat : (2105638223 : ℕ)^4703*100000000000000^3679 ≤ 33103536126757^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105638223 5000000000 33103536126757 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3715162637/10000000000 : ℝ)^4703 ≤ (28202458114579/100000000000000 : ℝ)^3679 := by
    have hnat : (3715162637 : ℕ)^4703*100000000000000^3679 ≤ 28202458114579^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3715162637 10000000000 28202458114579 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4758032641/10000000000 : ℝ)^4703 ≤ (2418375359461/6250000000000 : ℝ)^3679 := by
    have hnat : (4758032641 : ℕ)^4703*6250000000000^3679 ≤ 2418375359461^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4758032641 10000000000 2418375359461 6250000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105638223/5000000000 : ℝ), (3715162637/10000000000 : ℝ), (4758032641/10000000000 : ℝ)] ![(33103536126757/100000000000000 : ℝ), (28202458114579/100000000000000 : ℝ), (2418375359461/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105638223/5000000000 : ℝ)|^4703 ≤ (33103536126757/100000000000000 : ℝ)^3679
        have hw : |(2105638223/5000000000 : ℝ)|=(2105638223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3715162637/10000000000 : ℝ)|^4703 ≤ (28202458114579/100000000000000 : ℝ)^3679
        have hw : |(3715162637/10000000000 : ℝ)|=(3715162637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4758032641/10000000000 : ℝ)|^4703 ≤ (2418375359461/6250000000000 : ℝ)^3679
        have hw : |(4758032641/10000000000 : ℝ)|=(4758032641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s1_4 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215325517/1250000000 : ℝ)*x 0 + (1279012103/2500000000 : ℝ)*x 1 + (1384662329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215325517/1250000000 : ℝ)^4703 ≤ (10558154762029/100000000000000 : ℝ)^3679 := by
    have hnat : (215325517 : ℕ)^4703*100000000000000^3679 ≤ 10558154762029^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215325517 1250000000 10558154762029 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279012103/2500000000 : ℝ)^4703 ≤ (42454187348183/100000000000000 : ℝ)^3679 := by
    have hnat : (1279012103 : ℕ)^4703*100000000000000^3679 ≤ 42454187348183^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279012103 2500000000 42454187348183 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1384662329/2500000000 : ℝ)^4703 ≤ (1468364308719/3125000000000 : ℝ)^3679 := by
    have hnat : (1384662329 : ℕ)^4703*3125000000000^3679 ≤ 1468364308719^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384662329 2500000000 1468364308719 3125000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215325517/1250000000 : ℝ), (1279012103/2500000000 : ℝ), (1384662329/2500000000 : ℝ)] ![(10558154762029/100000000000000 : ℝ), (42454187348183/100000000000000 : ℝ), (1468364308719/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215325517/1250000000 : ℝ)|^4703 ≤ (10558154762029/100000000000000 : ℝ)^3679
        have hw : |(-215325517/1250000000 : ℝ)|=(215325517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1279012103/2500000000 : ℝ)|^4703 ≤ (42454187348183/100000000000000 : ℝ)^3679
        have hw : |(1279012103/2500000000 : ℝ)|=(1279012103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1384662329/2500000000 : ℝ)|^4703 ≤ (1468364308719/3125000000000 : ℝ)^3679
        have hw : |(1384662329/2500000000 : ℝ)|=(1384662329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s1_5 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261469761/10000000000 : ℝ)*x 0 + (-1521584543/10000000000 : ℝ)*x 1 + (553864957/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261469761/10000000000 : ℝ)^4703 ≤ (8800573888657/20000000000000 : ℝ)^3679 := by
    have hnat : (5261469761 : ℕ)^4703*20000000000000^3679 ≤ 8800573888657^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261469761 10000000000 8800573888657 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1521584543/10000000000 : ℝ)^4703 ≤ (9009469911467/100000000000000 : ℝ)^3679 := by
    have hnat : (1521584543 : ℕ)^4703*100000000000000^3679 ≤ 9009469911467^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521584543 10000000000 9009469911467 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553864957/1000000000 : ℝ)^4703 ≤ (4698766063361/10000000000000 : ℝ)^3679 := by
    have hnat : (553864957 : ℕ)^4703*10000000000000^3679 ≤ 4698766063361^3679*1000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553864957 1000000000 4698766063361 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261469761/10000000000 : ℝ), (-1521584543/10000000000 : ℝ), (553864957/1000000000 : ℝ)] ![(8800573888657/20000000000000 : ℝ), (9009469911467/100000000000000 : ℝ), (4698766063361/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261469761/10000000000 : ℝ)|^4703 ≤ (8800573888657/20000000000000 : ℝ)^3679
        have hw : |(5261469761/10000000000 : ℝ)|=(5261469761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1521584543/10000000000 : ℝ)|^4703 ≤ (9009469911467/100000000000000 : ℝ)^3679
        have hw : |(-1521584543/10000000000 : ℝ)|=(1521584543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553864957/1000000000 : ℝ)|^4703 ≤ (4698766063361/10000000000000 : ℝ)^3679
        have hw : |(553864957/1000000000 : ℝ)|=(553864957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s1_6 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657683659/1250000000 : ℝ)*x 0 + (2769324873/5000000000 : ℝ)*x 1 + (-1521584981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657683659/1250000000 : ℝ)^4703 ≤ (44002864215377/100000000000000 : ℝ)^3679 := by
    have hnat : (657683659 : ℕ)^4703*100000000000000^3679 ≤ 44002864215377^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657683659 1250000000 44002864215377 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2769324873/5000000000 : ℝ)^4703 ≤ (4698766254231/10000000000000 : ℝ)^3679 := by
    have hnat : (2769324873 : ℕ)^4703*10000000000000^3679 ≤ 4698766254231^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769324873 5000000000 4698766254231 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1521584981/10000000000 : ℝ)^4703 ≤ (2252368306691/25000000000000 : ℝ)^3679 := by
    have hnat : (1521584981 : ℕ)^4703*25000000000000^3679 ≤ 2252368306691^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521584981 10000000000 2252368306691 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657683659/1250000000 : ℝ), (2769324873/5000000000 : ℝ), (-1521584981/10000000000 : ℝ)] ![(44002864215377/100000000000000 : ℝ), (4698766254231/10000000000000 : ℝ), (2252368306691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657683659/1250000000 : ℝ)|^4703 ≤ (44002864215377/100000000000000 : ℝ)^3679
        have hw : |(657683659/1250000000 : ℝ)|=(657683659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2769324873/5000000000 : ℝ)|^4703 ≤ (4698766254231/10000000000000 : ℝ)^3679
        have hw : |(2769324873/5000000000 : ℝ)|=(2769324873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1521584981/10000000000 : ℝ)|^4703 ≤ (2252368306691/25000000000000 : ℝ)^3679
        have hw : |(-1521584981/10000000000 : ℝ)|=(1521584981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s1_7 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211890363/10000000000 : ℝ)*x 0 + (4746369951/10000000000 : ℝ)*x 1 + (931752879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211890363/10000000000 : ℝ)^4703 ≤ (33109705262089/100000000000000 : ℝ)^3679 := by
    have hnat : (4211890363 : ℕ)^4703*100000000000000^3679 ≤ 33109705262089^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211890363 10000000000 33109705262089 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4746369951/10000000000 : ℝ)^4703 ≤ (19286401575587/50000000000000 : ℝ)^3679 := by
    have hnat : (4746369951 : ℕ)^4703*50000000000000^3679 ≤ 19286401575587^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4746369951 10000000000 19286401575587 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931752879/2500000000 : ℝ)^4703 ≤ (14158745784353/50000000000000 : ℝ)^3679 := by
    have hnat : (931752879 : ℕ)^4703*50000000000000^3679 ≤ 14158745784353^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931752879 2500000000 14158745784353 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211890363/10000000000 : ℝ), (4746369951/10000000000 : ℝ), (931752879/2500000000 : ℝ)] ![(33109705262089/100000000000000 : ℝ), (19286401575587/50000000000000 : ℝ), (14158745784353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211890363/10000000000 : ℝ)|^4703 ≤ (33109705262089/100000000000000 : ℝ)^3679
        have hw : |(4211890363/10000000000 : ℝ)|=(4211890363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4746369951/10000000000 : ℝ)|^4703 ≤ (19286401575587/50000000000000 : ℝ)^3679
        have hw : |(4746369951/10000000000 : ℝ)|=(4746369951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(931752879/2500000000 : ℝ)|^4703 ≤ (14158745784353/50000000000000 : ℝ)^3679
        have hw : |(931752879/2500000000 : ℝ)|=(931752879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1596_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24569/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (116/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2217/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24569/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (116/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24569/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (116/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24569/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (116/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24569/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (116/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24569/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (116/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24569/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (116/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (116/3125 : ℝ) ^ (4699/1024 : ℝ) ≤ (2729737820973/10000000000000000000 : ℝ) := by
    have hpowers : (116/3125 : ℝ)^4699 ≤ (2729737820973/10000000000000000000 : ℝ)^1024 := by
      have hnat : (116 : ℕ)^4699*10000000000000000000^1024 ≤ 2729737820973^1024*3125^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116 3125 2729737820973 10000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (116/3125 : ℝ)) (X := (2729737820973/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24569/100000 : ℝ) ^ (4699/1024 : ℝ) ≤ (79714828424688081/50000000000000000000 : ℝ) := by
    have hpowers : (24569/100000 : ℝ)^4699 ≤ (79714828424688081/50000000000000000000 : ℝ)^1024 := by
      have hnat : (24569 : ℕ)^4699*50000000000000000000^1024 ≤ 79714828424688081^1024*100000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24569 100000 79714828424688081 50000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24569/100000 : ℝ)) (X := (79714828424688081/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000002729737820973/5000000000000000000 : ℝ) ≤ (5000000594860807/5000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (5000002729737820973/5000000000000000000 : ℝ)^1024 ≤ (5000000594860807/5000000000000000 : ℝ)^4699 := by
      have hnat : (5000002729737820973 : ℕ)^1024*5000000000000000^4699 ≤ 5000000594860807^4699*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000002729737820973 5000000000000000000 5000000594860807 5000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000594860807/5000000000000000 : ℝ)) (X := (5000002729737820973/5000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25039864238556896473/25000000000000000000 : ℝ) ≤ (200069454012837/200000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (25039864238556896473/25000000000000000000 : ℝ)^1024 ≤ (200069454012837/200000000000000 : ℝ)^4699 := by
      have hnat : (25039864238556896473 : ℕ)^1024*200000000000000^4699 ≤ 200069454012837^4699*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25039864238556896473 25000000000000000000 200069454012837 200000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200069454012837/200000000000000 : ℝ)) (X := (25039864238556896473/25000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25079714828424688081/25000000000000000000 : ℝ) ≤ (5003472105781043/5000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (25079714828424688081/25000000000000000000 : ℝ)^1024 ≤ (5003472105781043/5000000000000000 : ℝ)^4699 := by
      have hnat : (25079714828424688081 : ℕ)^1024*5000000000000000^4699 ≤ 5003472105781043^4699*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25079714828424688081 25000000000000000000 5003472105781043 5000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003472105781043/5000000000000000 : ℝ)) (X := (25079714828424688081/25000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2729737820973/10000000000000000000 : ℝ) ≤ ((104272126158475935567/104285000000000000000 : ℝ)+2*(867877730059/521425000000000 : ℝ)*(116/3125 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (104272126158475935567/104285000000000000000 : ℝ)+2*(867877730059/521425000000000 : ℝ)*(116/3125 : ℝ)=(5000000594860807/5000000000000000 : ℝ) by norm_num, show 1+2*(2729737820973/10000000000000000000 : ℝ)=(5000002729737820973/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(79714828424688081/50000000000000000000 : ℝ)+(2729737820973/10000000000000000000 : ℝ) ≤ ((104272126158475935567/104285000000000000000 : ℝ)+(867877730059/521425000000000 : ℝ)*((24569/100000 : ℝ)+(116/3125 : ℝ)))^(4699/1024 : ℝ) := by
    rw [show (104272126158475935567/104285000000000000000 : ℝ)+(867877730059/521425000000000 : ℝ)*((24569/100000 : ℝ)+(116/3125 : ℝ))=(200069454012837/200000000000000 : ℝ) by norm_num, show 1+(79714828424688081/50000000000000000000 : ℝ)+(2729737820973/10000000000000000000 : ℝ)=(25039864238556896473/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(79714828424688081/50000000000000000000 : ℝ) ≤ ((104272126158475935567/104285000000000000000 : ℝ)+2*(867877730059/521425000000000 : ℝ)*(24569/100000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (104272126158475935567/104285000000000000000 : ℝ)+2*(867877730059/521425000000000 : ℝ)*(24569/100000 : ℝ)=(5003472105781043/5000000000000000 : ℝ) by norm_num, show 1+2*(79714828424688081/50000000000000000000 : ℝ)=(25079714828424688081/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (104272126158475935567/104285000000000000000 : ℝ)*(X 1 0+X 2 0)+(867877730059/521425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (116/3125 : ℝ)) (hi := (24569/100000 : ℝ)) (c := (104272126158475935567/104285000000000000000 : ℝ)) (alpha := (867877730059/521425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (104272126158475935567/104285000000000000000 : ℝ)*(X 0 1+X 2 1)+(867877730059/521425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (116/3125 : ℝ)) (hi := (24569/100000 : ℝ)) (c := (104272126158475935567/104285000000000000000 : ℝ)) (alpha := (867877730059/521425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (104272126158475935567/104285000000000000000 : ℝ)*(X 0 2+X 1 2)+(867877730059/521425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (116/3125 : ℝ)) (hi := (24569/100000 : ℝ)) (c := (104272126158475935567/104285000000000000000 : ℝ)) (alpha := (867877730059/521425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-86117467/500000000 : ℝ)*X 0 0+(5543561859/10000000000 : ℝ)*X 0 1+(5111213073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376227929/10000000000 : ℝ)*X 1 0+(-7613363/39062500 : ℝ)*X 1 1+(2555606461/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688113801/5000000000 : ℝ)*X 2 0+(5111213197/10000000000 : ℝ)*X 2 1+(-1949021001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2105638223/5000000000 : ℝ)*X 0 0+(3715162637/10000000000 : ℝ)*X 0 1+(4758032641/10000000000 : ℝ)*X 0 2+(2105638223/5000000000 : ℝ)*X 1 0+(3715162637/10000000000 : ℝ)*X 1 1+(4758032641/10000000000 : ℝ)*X 1 2+(2105638223/5000000000 : ℝ)*X 2 0+(3715162637/10000000000 : ℝ)*X 2 1+(4758032641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-215325517/1250000000 : ℝ)*X 0 0+(1279012103/2500000000 : ℝ)*X 0 1+(1384662329/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5261469761/10000000000 : ℝ)*X 1 0+(-1521584543/10000000000 : ℝ)*X 1 1+(553864957/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((657683659/1250000000 : ℝ)*X 2 0+(2769324873/5000000000 : ℝ)*X 2 1+(-1521584981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211890363/10000000000 : ℝ)*X 0 0+(4746369951/10000000000 : ℝ)*X 0 1+(931752879/2500000000 : ℝ)*X 0 2+(4211890363/10000000000 : ℝ)*X 1 0+(4746369951/10000000000 : ℝ)*X 1 1+(931752879/2500000000 : ℝ)*X 1 2+(4211890363/10000000000 : ℝ)*X 2 0+(4746369951/10000000000 : ℝ)*X 2 1+(931752879/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1048604947897348303767869079/325890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5424091/20000000000000 : ℝ)*(base1) + (462610919/50000000000000 : ℝ)*(base19) + (15690797/2000000000000 : ℝ)*(base23) + (54771571/50000000000000 : ℝ)*(upper3) + (43954963/100000000000000 : ℝ)*(upper5) + (204491321312721/12500000000000 : ℝ)*(major0) + (204491321312721/12500000000000 : ℝ)*(major1) + (204491321312721/12500000000000 : ℝ)*(major2) + (578238879818371/25000000000000 : ℝ)*(sp0) + (1156480722464339/50000000000000 : ℝ)*(sp1) + (578240396402667/25000000000000 : ℝ)*(sp2) + (958895320791197/100000000000000 : ℝ)*(sp3) + (6877997487/100000000000000 : ℝ)*(sp4) + (1657843027/50000000000000 : ℝ)*(sp7) + (479449331798853/50000000000000 : ℝ)*(f.failure) + (2312962370150517/100000000000000 : ℝ)*(f.sum) + (5537857042571/3258906250000000000000000000 : ℝ)*base66 + (16597920853333060307/1303562500000000000000000000000000 : ℝ)*base67 + (13686509010610935307/1303562500000000000000000000000000 : ℝ)*base69 + (10320310492762372807/1303562500000000000000000000000000 : ℝ)*base71 + (187446106893433/104285000000000000000000000000 : ℝ)*base73 + (15437647228645685307/1303562500000000000000000000000000 : ℝ)*base75 + (3475811837461247807/1303562500000000000000000000000000 : ℝ)*base77 + (3199019770040189693/1303562500000000000000000000000000 : ℝ)*base80 + (32111115950443/104285000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (8484921/5000000000000000000000 : ℝ)*base89 + (8484921/5000000000000000000000 : ℝ)*base91 + (8484921/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56817285498242712469821102087/5214250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2074784613/100000000000000 : ℝ)*(base19) + (1839077953/100000000000000 : ℝ)*(base23) + (3166849/50000000000000 : ℝ)*(upper2) + (164096703/50000000000000 : ℝ)*(upper3) + (201551829/100000000000000 : ℝ)*(upper5) + (1673652978300271/100000000000000 : ℝ)*(major0) + (1673652978300271/100000000000000 : ℝ)*(major1) + (1673652978300271/100000000000000 : ℝ)*(major2) + (15383440731/100000000000000 : ℝ)*(sp1) + (2821569249/20000000000000 : ℝ)*(sp2) + (591573996875101/25000000000000 : ℝ)*(sp4) + (118313926463753/5000000000000 : ℝ)*(sp5) + (1183140020288103/50000000000000 : ℝ)*(sp6) + (981009605882119/100000000000000 : ℝ)*(sp7) + (981009605882119/100000000000000 : ℝ)*(f.failure) + (591573996875101/25000000000000 : ℝ)*(f.sum) + (23625376119851/104285000000000000000000000000 : ℝ)*base65 + (115105747996987938657/10428500000000000000000000000000000 : ℝ)*base67 + (84237998575234438657/10428500000000000000000000000000000 : ℝ)*base69 + (70219488618226438657/10428500000000000000000000000000000 : ℝ)*base71 + (658330794986971/104285000000000000000000000000 : ℝ)*base73 + (27666238082271438657/10428500000000000000000000000000000 : ℝ)*base75 + (21992267129780938657/10428500000000000000000000000000000 : ℝ)*base77 + (31543423775737438657/10428500000000000000000000000000000 : ℝ)*base79 + (239090614806151/104285000000000000000000000000 : ℝ)*base81 + (64512317/10000000000000000000000 : ℝ)*base90 + (64512317/10000000000000000000000 : ℝ)*base92 + (64512317/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1596_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24569/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (116/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2217/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1596_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1596_s2_0 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-869152781/5000000000 : ℝ)*x 0 + (5473020409/10000000000 : ℝ)*x 1 + (258566871/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869152781/5000000000 : ℝ)^4703 ≤ (10681333622347/100000000000000 : ℝ)^3679 := by
    have hnat : (869152781 : ℕ)^4703*100000000000000^3679 ≤ 10681333622347^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869152781 5000000000 10681333622347 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473020409/10000000000 : ℝ)^4703 ≤ (5784637087549/12500000000000 : ℝ)^3679 := by
    have hnat : (5473020409 : ℕ)^4703*12500000000000^3679 ≤ 5784637087549^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473020409 10000000000 5784637087549 12500000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258566871/500000000 : ℝ)^4703 ≤ (43041569668759/100000000000000 : ℝ)^3679 := by
    have hnat : (258566871 : ℕ)^4703*100000000000000^3679 ≤ 43041569668759^3679*500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258566871 500000000 43041569668759 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-869152781/5000000000 : ℝ), (5473020409/10000000000 : ℝ), (258566871/500000000 : ℝ)] ![(10681333622347/100000000000000 : ℝ), (5784637087549/12500000000000 : ℝ), (43041569668759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-869152781/5000000000 : ℝ)|^4703 ≤ (10681333622347/100000000000000 : ℝ)^3679
        have hw : |(-869152781/5000000000 : ℝ)|=(869152781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473020409/10000000000 : ℝ)|^4703 ≤ (5784637087549/12500000000000 : ℝ)^3679
        have hw : |(5473020409/10000000000 : ℝ)|=(5473020409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258566871/500000000 : ℝ)|^4703 ≤ (43041569668759/100000000000000 : ℝ)^3679
        have hw : |(258566871/500000000 : ℝ)|=(258566871/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s2_1 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267898191/500000000 : ℝ)*x 0 + (-1894259193/10000000000 : ℝ)*x 1 + (1292834301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267898191/500000000 : ℝ)^4703 ≤ (45037110771963/100000000000000 : ℝ)^3679 := by
    have hnat : (267898191 : ℕ)^4703*100000000000000^3679 ≤ 45037110771963^3679*500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267898191 500000000 45037110771963 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1894259193/10000000000 : ℝ)^4703 ≤ (1192132184347/10000000000000 : ℝ)^3679 := by
    have hnat : (1894259193 : ℕ)^4703*10000000000000^3679 ≤ 1192132184347^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894259193 10000000000 1192132184347 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292834301/2500000000 : ℝ)^4703 ≤ (21520783685289/50000000000000 : ℝ)^3679 := by
    have hnat : (1292834301 : ℕ)^4703*50000000000000^3679 ≤ 21520783685289^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292834301 2500000000 21520783685289 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267898191/500000000 : ℝ), (-1894259193/10000000000 : ℝ), (1292834301/2500000000 : ℝ)] ![(45037110771963/100000000000000 : ℝ), (1192132184347/10000000000000 : ℝ), (21520783685289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267898191/500000000 : ℝ)|^4703 ≤ (45037110771963/100000000000000 : ℝ)^3679
        have hw : |(267898191/500000000 : ℝ)|=(267898191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1894259193/10000000000 : ℝ)|^4703 ≤ (1192132184347/10000000000000 : ℝ)^3679
        have hw : |(-1894259193/10000000000 : ℝ)|=(1894259193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1292834301/2500000000 : ℝ)|^4703 ≤ (21520783685289/50000000000000 : ℝ)^3679
        have hw : |(1292834301/2500000000 : ℝ)|=(1292834301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s2_2 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339490863/2500000000 : ℝ)*x 0 + (5171337691/10000000000 : ℝ)*x 1 + (-1894259041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339490863/2500000000 : ℝ)^4703 ≤ (11259276704429/25000000000000 : ℝ)^3679 := by
    have hnat : (1339490863 : ℕ)^4703*25000000000000^3679 ≤ 11259276704429^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339490863 2500000000 11259276704429 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5171337691/10000000000 : ℝ)^4703 ≤ (344332580417/800000000000 : ℝ)^3679 := by
    have hnat : (5171337691 : ℕ)^4703*800000000000^3679 ≤ 344332580417^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171337691 10000000000 344332580417 800000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1894259041/10000000000 : ℝ)^4703 ≤ (5960660310309/50000000000000 : ℝ)^3679 := by
    have hnat : (1894259041 : ℕ)^4703*50000000000000^3679 ≤ 5960660310309^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894259041 10000000000 5960660310309 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339490863/2500000000 : ℝ), (5171337691/10000000000 : ℝ), (-1894259041/10000000000 : ℝ)] ![(11259276704429/25000000000000 : ℝ), (344332580417/800000000000 : ℝ), (5960660310309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339490863/2500000000 : ℝ)|^4703 ≤ (11259276704429/25000000000000 : ℝ)^3679
        have hw : |(1339490863/2500000000 : ℝ)|=(1339490863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5171337691/10000000000 : ℝ)|^4703 ≤ (344332580417/800000000000 : ℝ)^3679
        have hw : |(5171337691/10000000000 : ℝ)|=(5171337691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1894259041/10000000000 : ℝ)|^4703 ≤ (5960660310309/50000000000000 : ℝ)^3679
        have hw : |(-1894259041/10000000000 : ℝ)|=(1894259041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s2_3 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105575091/250000000 : ℝ)*x 0 + (483936119/1250000000 : ℝ)*x 1 + (4599179289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105575091/250000000 : ℝ)^4703 ≤ (33221423719577/100000000000000 : ℝ)^3679 := by
    have hnat : (105575091 : ℕ)^4703*100000000000000^3679 ≤ 33221423719577^3679*250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105575091 250000000 33221423719577 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483936119/1250000000 : ℝ)^4703 ≤ (29728256132067/100000000000000 : ℝ)^3679 := by
    have hnat : (483936119 : ℕ)^4703*100000000000000^3679 ≤ 29728256132067^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483936119 1250000000 29728256132067 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4599179289/10000000000 : ℝ)^4703 ≤ (37050320133177/100000000000000 : ℝ)^3679 := by
    have hnat : (4599179289 : ℕ)^4703*100000000000000^3679 ≤ 37050320133177^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4599179289 10000000000 37050320133177 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105575091/250000000 : ℝ), (483936119/1250000000 : ℝ), (4599179289/10000000000 : ℝ)] ![(33221423719577/100000000000000 : ℝ), (29728256132067/100000000000000 : ℝ), (37050320133177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105575091/250000000 : ℝ)|^4703 ≤ (33221423719577/100000000000000 : ℝ)^3679
        have hw : |(105575091/250000000 : ℝ)|=(105575091/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(483936119/1250000000 : ℝ)|^4703 ≤ (29728256132067/100000000000000 : ℝ)^3679
        have hw : |(483936119/1250000000 : ℝ)|=(483936119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4599179289/10000000000 : ℝ)|^4703 ≤ (37050320133177/100000000000000 : ℝ)^3679
        have hw : |(4599179289/10000000000 : ℝ)|=(4599179289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s2_4 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1738391903/10000000000 : ℝ)*x 0 + (129342491/250000000 : ℝ)*x 1 + (5470632137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1738391903/10000000000 : ℝ)^4703 ≤ (10682011833031/100000000000000 : ℝ)^3679 := by
    have hnat : (1738391903 : ℕ)^4703*100000000000000^3679 ≤ 10682011833031^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738391903 10000000000 10682011833031 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129342491/250000000 : ℝ)^4703 ≤ (10766676159573/25000000000000 : ℝ)^3679 := by
    have hnat : (129342491 : ℕ)^4703*25000000000000^3679 ≤ 10766676159573^3679*250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129342491 250000000 10766676159573 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470632137/10000000000 : ℝ)^4703 ≤ (11562820878207/25000000000000 : ℝ)^3679 := by
    have hnat : (5470632137 : ℕ)^4703*25000000000000^3679 ≤ 11562820878207^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470632137 10000000000 11562820878207 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1738391903/10000000000 : ℝ), (129342491/250000000 : ℝ), (5470632137/10000000000 : ℝ)] ![(10682011833031/100000000000000 : ℝ), (10766676159573/25000000000000 : ℝ), (11562820878207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1738391903/10000000000 : ℝ)|^4703 ≤ (10682011833031/100000000000000 : ℝ)^3679
        have hw : |(-1738391903/10000000000 : ℝ)|=(1738391903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129342491/250000000 : ℝ)|^4703 ≤ (10766676159573/25000000000000 : ℝ)^3679
        have hw : |(129342491/250000000 : ℝ)|=(129342491/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470632137/10000000000 : ℝ)|^4703 ≤ (11562820878207/25000000000000 : ℝ)^3679
        have hw : |(5470632137/10000000000 : ℝ)|=(5470632137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s2_5 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055608663/2000000000 : ℝ)*x 0 + (-63798577/400000000 : ℝ)*x 1 + (5470632233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055608663/2000000000 : ℝ)^4703 ≤ (22090067622087/50000000000000 : ℝ)^3679 := by
    have hnat : (1055608663 : ℕ)^4703*50000000000000^3679 ≤ 22090067622087^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055608663 2000000000 22090067622087 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63798577/400000000 : ℝ)^4703 ≤ (4784290097677/50000000000000 : ℝ)^3679 := by
    have hnat : (63798577 : ℕ)^4703*50000000000000^3679 ≤ 4784290097677^3679*400000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63798577 400000000 4784290097677 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470632233/10000000000 : ℝ)^4703 ≤ (46251284550363/100000000000000 : ℝ)^3679 := by
    have hnat : (5470632233 : ℕ)^4703*100000000000000^3679 ≤ 46251284550363^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470632233 10000000000 46251284550363 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055608663/2000000000 : ℝ), (-63798577/400000000 : ℝ), (5470632233/10000000000 : ℝ)] ![(22090067622087/50000000000000 : ℝ), (4784290097677/50000000000000 : ℝ), (46251284550363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055608663/2000000000 : ℝ)|^4703 ≤ (22090067622087/50000000000000 : ℝ)^3679
        have hw : |(1055608663/2000000000 : ℝ)|=(1055608663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-63798577/400000000 : ℝ)|^4703 ≤ (4784290097677/50000000000000 : ℝ)^3679
        have hw : |(-63798577/400000000 : ℝ)|=(63798577/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470632233/10000000000 : ℝ)|^4703 ≤ (46251284550363/100000000000000 : ℝ)^3679
        have hw : |(5470632233/10000000000 : ℝ)|=(5470632233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s2_6 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278043441/10000000000 : ℝ)*x 0 + (5470632007/10000000000 : ℝ)*x 1 + (-199370571/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278043441/10000000000 : ℝ)^4703 ≤ (22090068296211/50000000000000 : ℝ)^3679 := by
    have hnat : (5278043441 : ℕ)^4703*50000000000000^3679 ≤ 22090068296211^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278043441 10000000000 22090068296211 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470632007/10000000000 : ℝ)^4703 ≤ (46251282107833/100000000000000 : ℝ)^3679 := by
    have hnat : (5470632007 : ℕ)^4703*100000000000000^3679 ≤ 46251282107833^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470632007 10000000000 46251282107833 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199370571/1250000000 : ℝ)^4703 ≤ (2392145323007/25000000000000 : ℝ)^3679 := by
    have hnat : (199370571 : ℕ)^4703*25000000000000^3679 ≤ 2392145323007^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199370571 1250000000 2392145323007 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278043441/10000000000 : ℝ), (5470632007/10000000000 : ℝ), (-199370571/1250000000 : ℝ)] ![(22090068296211/50000000000000 : ℝ), (46251282107833/100000000000000 : ℝ), (2392145323007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278043441/10000000000 : ℝ)|^4703 ≤ (22090068296211/50000000000000 : ℝ)^3679
        have hw : |(5278043441/10000000000 : ℝ)|=(5278043441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470632007/10000000000 : ℝ)|^4703 ≤ (46251282107833/100000000000000 : ℝ)^3679
        have hw : |(5470632007/10000000000 : ℝ)|=(5470632007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199370571/1250000000 : ℝ)|^4703 ≤ (2392145323007/25000000000000 : ℝ)^3679
        have hw : |(-199370571/1250000000 : ℝ)|=(199370571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s2_7 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4124231/9765625 : ℝ)*x 0 + (2296740961/5000000000 : ℝ)*x 1 + (3877249861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4124231/9765625 : ℝ)^4703 ≤ (16611762276749/50000000000000 : ℝ)^3679 := by
    have hnat : (4124231 : ℕ)^4703*50000000000000^3679 ≤ 16611762276749^3679*9765625^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124231 9765625 16611762276749 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296740961/5000000000 : ℝ)^4703 ≤ (369916582351/1000000000000 : ℝ)^3679 := by
    have hnat : (2296740961 : ℕ)^4703*1000000000000^3679 ≤ 369916582351^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296740961 5000000000 369916582351 1000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3877249861/10000000000 : ℝ)^4703 ≤ (29784817188331/100000000000000 : ℝ)^3679 := by
    have hnat : (3877249861 : ℕ)^4703*100000000000000^3679 ≤ 29784817188331^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3877249861 10000000000 29784817188331 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4124231/9765625 : ℝ), (2296740961/5000000000 : ℝ), (3877249861/10000000000 : ℝ)] ![(16611762276749/50000000000000 : ℝ), (369916582351/1000000000000 : ℝ), (29784817188331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4124231/9765625 : ℝ)|^4703 ≤ (16611762276749/50000000000000 : ℝ)^3679
        have hw : |(4124231/9765625 : ℝ)|=(4124231/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2296740961/5000000000 : ℝ)|^4703 ≤ (369916582351/1000000000000 : ℝ)^3679
        have hw : |(2296740961/5000000000 : ℝ)|=(2296740961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3877249861/10000000000 : ℝ)|^4703 ≤ (29784817188331/100000000000000 : ℝ)^3679
        have hw : |(3877249861/10000000000 : ℝ)|=(3877249861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1596_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10167/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16557/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2217/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2217/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2217/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2217/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2217/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2217/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2217/25000 : ℝ) ^ (4699/1024 : ℝ) ≤ (92809370108473/6250000000000000000 : ℝ) := by
    have hpowers : (2217/25000 : ℝ)^4699 ≤ (92809370108473/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2217 : ℕ)^4699*6250000000000000000^1024 ≤ 92809370108473^1024*25000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2217 25000 92809370108473 6250000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2217/25000 : ℝ)) (X := (92809370108473/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18023/100000 : ℝ) ^ (4699/1024 : ℝ) ≤ (9616772154997271/25000000000000000000 : ℝ) := by
    have hpowers : (18023/100000 : ℝ)^4699 ≤ (9616772154997271/25000000000000000000 : ℝ)^1024 := by
      have hnat : (18023 : ℕ)^4699*25000000000000000000^1024 ≤ 9616772154997271^1024*100000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18023 100000 9616772154997271 25000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18023/100000 : ℝ)) (X := (9616772154997271/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125092809370108473/3125000000000000000 : ℝ) ≤ (10000064718921507/10000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (3125092809370108473/3125000000000000000 : ℝ)^1024 ≤ (10000064718921507/10000000000000000 : ℝ)^4699 := by
      have hnat : (3125092809370108473 : ℕ)^1024*10000000000000000^4699 ≤ 10000064718921507^4699*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125092809370108473 3125000000000000000 10000064718921507 10000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000064718921507/10000000000000000 : ℝ)) (X := (3125092809370108473/3125000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009988009635431163/25000000000000000000 : ℝ) ≤ (5000435246834731/5000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (25009988009635431163/25000000000000000000 : ℝ)^1024 ≤ (5000435246834731/5000000000000000 : ℝ)^4699 := by
      have hnat : (25009988009635431163 : ℕ)^1024*5000000000000000^4699 ≤ 5000435246834731^4699*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009988009635431163 25000000000000000000 5000435246834731 5000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000435246834731/5000000000000000 : ℝ)) (X := (25009988009635431163/25000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509616772154997271/12500000000000000000 : ℝ) ≤ (10001676268417417/10000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (12509616772154997271/12500000000000000000 : ℝ)^1024 ≤ (10001676268417417/10000000000000000 : ℝ)^4699 := by
      have hnat : (12509616772154997271 : ℕ)^1024*10000000000000000^4699 ≤ 10001676268417417^4699*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509616772154997271 12500000000000000000 10001676268417417 10000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001676268417417/10000000000000000 : ℝ)) (X := (12509616772154997271/12500000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(92809370108473/6250000000000000000 : ℝ) ≤ ((18307260256159333341/18310000000000000000 : ℝ)+2*(161154949591/183100000000000 : ℝ)*(2217/25000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (18307260256159333341/18310000000000000000 : ℝ)+2*(161154949591/183100000000000 : ℝ)*(2217/25000 : ℝ)=(10000064718921507/10000000000000000 : ℝ) by norm_num, show 1+2*(92809370108473/6250000000000000000 : ℝ)=(3125092809370108473/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9616772154997271/25000000000000000000 : ℝ)+(92809370108473/6250000000000000000 : ℝ) ≤ ((18307260256159333341/18310000000000000000 : ℝ)+(161154949591/183100000000000 : ℝ)*((18023/100000 : ℝ)+(2217/25000 : ℝ)))^(4699/1024 : ℝ) := by
    rw [show (18307260256159333341/18310000000000000000 : ℝ)+(161154949591/183100000000000 : ℝ)*((18023/100000 : ℝ)+(2217/25000 : ℝ))=(5000435246834731/5000000000000000 : ℝ) by norm_num, show 1+(9616772154997271/25000000000000000000 : ℝ)+(92809370108473/6250000000000000000 : ℝ)=(25009988009635431163/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9616772154997271/25000000000000000000 : ℝ) ≤ ((18307260256159333341/18310000000000000000 : ℝ)+2*(161154949591/183100000000000 : ℝ)*(18023/100000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (18307260256159333341/18310000000000000000 : ℝ)+2*(161154949591/183100000000000 : ℝ)*(18023/100000 : ℝ)=(10001676268417417/10000000000000000 : ℝ) by norm_num, show 1+2*(9616772154997271/25000000000000000000 : ℝ)=(12509616772154997271/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18307260256159333341/18310000000000000000 : ℝ)*(X 1 0+X 2 0)+(161154949591/183100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (2217/25000 : ℝ)) (hi := (18023/100000 : ℝ)) (c := (18307260256159333341/18310000000000000000 : ℝ)) (alpha := (161154949591/183100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18307260256159333341/18310000000000000000 : ℝ)*(X 0 1+X 2 1)+(161154949591/183100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (2217/25000 : ℝ)) (hi := (18023/100000 : ℝ)) (c := (18307260256159333341/18310000000000000000 : ℝ)) (alpha := (161154949591/183100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18307260256159333341/18310000000000000000 : ℝ)*(X 0 2+X 1 2)+(161154949591/183100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (2217/25000 : ℝ)) (hi := (18023/100000 : ℝ)) (c := (18307260256159333341/18310000000000000000 : ℝ)) (alpha := (161154949591/183100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-869152781/5000000000 : ℝ)*X 0 0+(5473020409/10000000000 : ℝ)*X 0 1+(258566871/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267898191/500000000 : ℝ)*X 1 0+(-1894259193/10000000000 : ℝ)*X 1 1+(1292834301/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339490863/2500000000 : ℝ)*X 2 0+(5171337691/10000000000 : ℝ)*X 2 1+(-1894259041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((105575091/250000000 : ℝ)*X 0 0+(483936119/1250000000 : ℝ)*X 0 1+(4599179289/10000000000 : ℝ)*X 0 2+(105575091/250000000 : ℝ)*X 1 0+(483936119/1250000000 : ℝ)*X 1 1+(4599179289/10000000000 : ℝ)*X 1 2+(105575091/250000000 : ℝ)*X 2 0+(483936119/1250000000 : ℝ)*X 2 1+(4599179289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1738391903/10000000000 : ℝ)*X 0 0+(129342491/250000000 : ℝ)*X 0 1+(5470632137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055608663/2000000000 : ℝ)*X 1 0+(-63798577/400000000 : ℝ)*X 1 1+(5470632233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278043441/10000000000 : ℝ)*X 2 0+(5470632007/10000000000 : ℝ)*X 2 1+(-199370571/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4124231/9765625 : ℝ)*X 0 0+(2296740961/5000000000 : ℝ)*X 0 1+(3877249861/10000000000 : ℝ)*X 0 2+(4124231/9765625 : ℝ)*X 1 0+(2296740961/5000000000 : ℝ)*X 1 1+(3877249861/10000000000 : ℝ)*X 1 2+(4124231/9765625 : ℝ)*X 2 0+(2296740961/5000000000 : ℝ)*X 2 1+(3877249861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1409459475192905764314522189/457750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (467992857/100000000000000 : ℝ)*(base19) + (223814023/100000000000000 : ℝ)*(base23) + (26398711/50000000000000 : ℝ)*(upper3) + (4423783/50000000000000 : ℝ)*(upper4) + (28217957/25000000000000 : ℝ)*(upper5) + (1172239325455557/50000000000000 : ℝ)*(major0) + (1172239325455557/50000000000000 : ℝ)*(major1) + (1172239325455557/50000000000000 : ℝ)*(major2) + (132589622715807/4000000000000 : ℝ)*(sp0) + (3314743493950811/100000000000000 : ℝ)*(sp1) + (828685934532411/25000000000000 : ℝ)*(sp2) + (343553112922237/25000000000000 : ℝ)*(sp3) + (848512123/25000000000000 : ℝ)*(sp4) + (196388207/25000000000000 : ℝ)*(sp7) + (54968529489671/4000000000000 : ℝ)*(f.failure) + (828685990485917/25000000000000 : ℝ)*(f.sum) + (19908314354039/2288750000000000000000000000 : ℝ)*base66 + (1435716030474025937/915500000000000000000000000000000 : ℝ)*base67 + (5585820882210525937/915500000000000000000000000000000 : ℝ)*base69 + (704041659003474063/915500000000000000000000000000000 : ℝ)*base72 + (42752347816921/9155000000000000000000000000 : ℝ)*base74 + (2030260079840525937/915500000000000000000000000000000 : ℝ)*base75 + (1866578827242525937/915500000000000000000000000000000 : ℝ)*base77 + (5623743423135474063/915500000000000000000000000000000 : ℝ)*base80 + (2353947315797/4577500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5166653/400000000000000000000 : ℝ)*base90 + (5166653/400000000000000000000 : ℝ)*base92 + (5166653/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4576828008179509240934344467/457750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (983879281/100000000000000 : ℝ)*(base19) + (263090161/20000000000000 : ℝ)*(base23) + (45046237/25000000000000 : ℝ)*(upper3) + (1503447/1250000000000 : ℝ)*(lower4) + (6038111/4000000000000 : ℝ)*(upper5) + (2381981283239371/100000000000000 : ℝ)*(major0) + (2381981283239371/100000000000000 : ℝ)*(major1) + (2381981283239371/100000000000000 : ℝ)*(major2) + (99494043/1000000000000 : ℝ)*(sp1) + (5743957067/50000000000000 : ℝ)*(sp2) + (3367766874785933/100000000000000 : ℝ)*(sp4) + (210484746343897/6250000000000 : ℝ)*(sp5) + (1683877035710497/50000000000000 : ℝ)*(sp6) + (349048839602101/25000000000000 : ℝ)*(sp7) + (349048839602101/25000000000000 : ℝ)*(f.failure) + (3367766874785933/100000000000000 : ℝ)*(f.sum) + (12601079283163/4577500000000000000000000000 : ℝ)*base65 + (5706225497762268511/1831000000000000000000000000000000 : ℝ)*base67 + (8786915950604731489/1831000000000000000000000000000000 : ℝ)*base70 + (8809796043874268511/1831000000000000000000000000000000 : ℝ)*base71 + (20224912167879/9155000000000000000000000000 : ℝ)*base74 + (3190093766150268511/1831000000000000000000000000000000 : ℝ)*base75 + (3985425898972268511/1831000000000000000000000000000000 : ℝ)*base77 + (7107278441770268511/1831000000000000000000000000000000 : ℝ)*base79 + (23551754667229/9155000000000000000000000000 : ℝ)*base82 + (16365143/2500000000000000000000 : ℝ)*base90 + (16365143/2500000000000000000000 : ℝ)*base92 + (16365143/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1596_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1596_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1596_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1596_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1596_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1596_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1596_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

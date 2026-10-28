-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1255_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:25:31.599653+00:00
-- url     : https://prove2.me/submissions/13239770-f27d-483d-a2d4-58d5a8fb7945

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
theorem support_rectangle_w1255_box_0 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1990699739/10000000000 : ℝ)*x 0 + (2687323209/5000000000 : ℝ)*x 1 + (5374646289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990699739/10000000000 : ℝ)^33 ≤ (1187647619397/10000000000000 : ℝ)^25 := by
    have hnat : (1990699739 : ℕ)^33*10000000000000^25 ≤ 1187647619397^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990699739 10000000000 1187647619397 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687323209/5000000000 : ℝ)^33 ≤ (44061762591349/100000000000000 : ℝ)^25 := by
    have hnat : (2687323209 : ℕ)^33*100000000000000^25 ≤ 44061762591349^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687323209 5000000000 44061762591349 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374646289/10000000000 : ℝ)^33 ≤ (44061761195381/100000000000000 : ℝ)^25 := by
    have hnat : (5374646289 : ℕ)^33*100000000000000^25 ≤ 44061761195381^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374646289 10000000000 44061761195381 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1990699739/10000000000 : ℝ), (2687323209/5000000000 : ℝ), (5374646289/10000000000 : ℝ)] ![(1187647619397/10000000000000 : ℝ), (44061762591349/100000000000000 : ℝ), (44061761195381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1990699739/10000000000 : ℝ)|^33 ≤ (1187647619397/10000000000000 : ℝ)^25
        have hw : |(-1990699739/10000000000 : ℝ)|=(1990699739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687323209/5000000000 : ℝ)|^33 ≤ (44061762591349/100000000000000 : ℝ)^25
        have hw : |(2687323209/5000000000 : ℝ)|=(2687323209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374646289/10000000000 : ℝ)|^33 ≤ (44061761195381/100000000000000 : ℝ)^25
        have hw : |(5374646289/10000000000 : ℝ)|=(5374646289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_1 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5296884279/10000000000 : ℝ)*x 0 + (-2096419429/10000000000 : ℝ)*x 1 + (2687323237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296884279/10000000000 : ℝ)^33 ≤ (4322221707959/10000000000000 : ℝ)^25 := by
    have hnat : (5296884279 : ℕ)^33*10000000000000^25 ≤ 4322221707959^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296884279 10000000000 4322221707959 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096419429/10000000000 : ℝ)^33 ≤ (3179004926517/25000000000000 : ℝ)^25 := by
    have hnat : (2096419429 : ℕ)^33*25000000000000^25 ≤ 3179004926517^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096419429 10000000000 3179004926517 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687323237/5000000000 : ℝ)^33 ≤ (44061763197351/100000000000000 : ℝ)^25 := by
    have hnat : (2687323237 : ℕ)^33*100000000000000^25 ≤ 44061763197351^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687323237 5000000000 44061763197351 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296884279/10000000000 : ℝ), (-2096419429/10000000000 : ℝ), (2687323237/5000000000 : ℝ)] ![(4322221707959/10000000000000 : ℝ), (3179004926517/25000000000000 : ℝ), (44061763197351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296884279/10000000000 : ℝ)|^33 ≤ (4322221707959/10000000000000 : ℝ)^25
        have hw : |(5296884279/10000000000 : ℝ)|=(5296884279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2096419429/10000000000 : ℝ)|^33 ≤ (3179004926517/25000000000000 : ℝ)^25
        have hw : |(-2096419429/10000000000 : ℝ)|=(2096419429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687323237/5000000000 : ℝ)|^33 ≤ (44061763197351/100000000000000 : ℝ)^25
        have hw : |(2687323237/5000000000 : ℝ)|=(2687323237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_2 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1324221031/2500000000 : ℝ)*x 0 + (5374646421/10000000000 : ℝ)*x 1 + (-209641971/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324221031/2500000000 : ℝ)^33 ≤ (10805553852517/25000000000000 : ℝ)^25 := by
    have hnat : (1324221031 : ℕ)^33*25000000000000^25 ≤ 10805553852517^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324221031 2500000000 10805553852517 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374646421/10000000000 : ℝ)^33 ≤ (22030881311907/50000000000000 : ℝ)^25 := by
    have hnat : (5374646421 : ℕ)^33*50000000000000^25 ≤ 22030881311907^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374646421 10000000000 22030881311907 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209641971/1000000000 : ℝ)^33 ≤ (3179005488979/25000000000000 : ℝ)^25 := by
    have hnat : (209641971 : ℕ)^33*25000000000000^25 ≤ 3179005488979^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209641971 1000000000 3179005488979 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324221031/2500000000 : ℝ), (5374646421/10000000000 : ℝ), (-209641971/1000000000 : ℝ)] ![(10805553852517/25000000000000 : ℝ), (22030881311907/50000000000000 : ℝ), (3179005488979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324221031/2500000000 : ℝ)|^33 ≤ (10805553852517/25000000000000 : ℝ)^25
        have hw : |(1324221031/2500000000 : ℝ)|=(1324221031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374646421/10000000000 : ℝ)|^33 ≤ (22030881311907/50000000000000 : ℝ)^25
        have hw : |(5374646421/10000000000 : ℝ)|=(5374646421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209641971/1000000000 : ℝ)|^33 ≤ (3179005488979/25000000000000 : ℝ)^25
        have hw : |(-209641971/1000000000 : ℝ)|=(209641971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_3 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4455396843/10000000000 : ℝ)*x 0 + (1074457009/2500000000 : ℝ)*x 1 + (537228527/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4455396843/10000000000 : ℝ)^33 ≤ (34397750215499/100000000000000 : ℝ)^25 := by
    have hnat : (4455396843 : ℕ)^33*100000000000000^25 ≤ 34397750215499^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455396843 10000000000 34397750215499 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074457009/2500000000 : ℝ)^33 ≤ (16400561987229/50000000000000 : ℝ)^25 := by
    have hnat : (1074457009 : ℕ)^33*50000000000000^25 ≤ 16400561987229^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074457009 2500000000 16400561987229 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537228527/1250000000 : ℝ)^33 ≤ (32801125787827/100000000000000 : ℝ)^25 := by
    have hnat : (537228527 : ℕ)^33*100000000000000^25 ≤ 32801125787827^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537228527 1250000000 32801125787827 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4455396843/10000000000 : ℝ), (1074457009/2500000000 : ℝ), (537228527/1250000000 : ℝ)] ![(34397750215499/100000000000000 : ℝ), (16400561987229/50000000000000 : ℝ), (32801125787827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4455396843/10000000000 : ℝ)|^33 ≤ (34397750215499/100000000000000 : ℝ)^25
        have hw : |(4455396843/10000000000 : ℝ)|=(4455396843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074457009/2500000000 : ℝ)|^33 ≤ (16400561987229/50000000000000 : ℝ)^25
        have hw : |(1074457009/2500000000 : ℝ)|=(1074457009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537228527/1250000000 : ℝ)|^33 ≤ (32801125787827/100000000000000 : ℝ)^25
        have hw : |(537228527/1250000000 : ℝ)|=(537228527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_4 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-139916567/625000000 : ℝ)*x 0 + (1056483279/2000000000 : ℝ)*x 1 + (5282416399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139916567/625000000 : ℝ)^33 ≤ (1386709985541/10000000000000 : ℝ)^25 := by
    have hnat : (139916567 : ℕ)^33*10000000000000^25 ≤ 1386709985541^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139916567 625000000 1386709985541 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056483279/2000000000 : ℝ)^33 ≤ (43066450046299/100000000000000 : ℝ)^25 := by
    have hnat : (1056483279 : ℕ)^33*100000000000000^25 ≤ 43066450046299^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056483279 2000000000 43066450046299 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282416399/10000000000 : ℝ)^33 ≤ (21533225044673/50000000000000 : ℝ)^25 := by
    have hnat : (5282416399 : ℕ)^33*50000000000000^25 ≤ 21533225044673^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282416399 10000000000 21533225044673 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-139916567/625000000 : ℝ), (1056483279/2000000000 : ℝ), (5282416399/10000000000 : ℝ)] ![(1386709985541/10000000000000 : ℝ), (43066450046299/100000000000000 : ℝ), (21533225044673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-139916567/625000000 : ℝ)|^33 ≤ (1386709985541/10000000000000 : ℝ)^25
        have hw : |(-139916567/625000000 : ℝ)|=(139916567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056483279/2000000000 : ℝ)|^33 ≤ (43066450046299/100000000000000 : ℝ)^25
        have hw : |(1056483279/2000000000 : ℝ)|=(1056483279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282416399/10000000000 : ℝ)|^33 ≤ (21533225044673/50000000000000 : ℝ)^25
        have hw : |(5282416399/10000000000 : ℝ)|=(5282416399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_5 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2680940599/5000000000 : ℝ)*x 0 + (-1066509539/5000000000 : ℝ)*x 1 + (5282416411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680940599/5000000000 : ℝ)^33 ≤ (43923676783559/100000000000000 : ℝ)^25 := by
    have hnat : (2680940599 : ℕ)^33*100000000000000^25 ≤ 43923676783559^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680940599 5000000000 43923676783559 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066509539/5000000000 : ℝ)^33 ≤ (2601974597167/20000000000000 : ℝ)^25 := by
    have hnat : (1066509539 : ℕ)^33*20000000000000^25 ≤ 2601974597167^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066509539 5000000000 2601974597167 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282416411/10000000000 : ℝ)^33 ≤ (21533225109243/50000000000000 : ℝ)^25 := by
    have hnat : (5282416411 : ℕ)^33*50000000000000^25 ≤ 21533225109243^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282416411 10000000000 21533225109243 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680940599/5000000000 : ℝ), (-1066509539/5000000000 : ℝ), (5282416411/10000000000 : ℝ)] ![(43923676783559/100000000000000 : ℝ), (2601974597167/20000000000000 : ℝ), (21533225109243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680940599/5000000000 : ℝ)|^33 ≤ (43923676783559/100000000000000 : ℝ)^25
        have hw : |(2680940599/5000000000 : ℝ)|=(2680940599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066509539/5000000000 : ℝ)|^33 ≤ (2601974597167/20000000000000 : ℝ)^25
        have hw : |(-1066509539/5000000000 : ℝ)|=(1066509539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282416411/10000000000 : ℝ)|^33 ≤ (21533225109243/50000000000000 : ℝ)^25
        have hw : |(5282416411/10000000000 : ℝ)|=(5282416411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_6 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5361881227/10000000000 : ℝ)*x 0 + (660302049/1250000000 : ℝ)*x 1 + (-266627383/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361881227/10000000000 : ℝ)^33 ≤ (21961838548571/50000000000000 : ℝ)^25 := by
    have hnat : (5361881227 : ℕ)^33*50000000000000^25 ≤ 21961838548571^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361881227 10000000000 21961838548571 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660302049/1250000000 : ℝ)^33 ≤ (21533225007007/50000000000000 : ℝ)^25 := by
    have hnat : (660302049 : ℕ)^33*50000000000000^25 ≤ 21533225007007^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660302049 1250000000 21533225007007 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266627383/1250000000 : ℝ)^33 ≤ (81311705457/625000000000 : ℝ)^25 := by
    have hnat : (266627383 : ℕ)^33*625000000000^25 ≤ 81311705457^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266627383 1250000000 81311705457 625000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361881227/10000000000 : ℝ), (660302049/1250000000 : ℝ), (-266627383/1250000000 : ℝ)] ![(21961838548571/50000000000000 : ℝ), (21533225007007/50000000000000 : ℝ), (81311705457/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361881227/10000000000 : ℝ)|^33 ≤ (21961838548571/50000000000000 : ℝ)^25
        have hw : |(5361881227/10000000000 : ℝ)|=(5361881227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660302049/1250000000 : ℝ)|^33 ≤ (21533225007007/50000000000000 : ℝ)^25
        have hw : |(660302049/1250000000 : ℝ)|=(660302049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266627383/1250000000 : ℝ)|^33 ≤ (81311705457/625000000000 : ℝ)^25
        have hw : |(-266627383/1250000000 : ℝ)|=(266627383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_7 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4242185589/10000000000 : ℝ)*x 0 + (440441369/1000000000 : ℝ)*x 1 + (4404413791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242185589/10000000000 : ℝ)^33 ≤ (6448346298553/20000000000000 : ℝ)^25 := by
    have hnat : (4242185589 : ℕ)^33*20000000000000^25 ≤ 6448346298553^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242185589 10000000000 6448346298553 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440441369/1000000000 : ℝ)^33 ≤ (33879133726663/100000000000000 : ℝ)^25 := by
    have hnat : (440441369 : ℕ)^33*100000000000000^25 ≤ 33879133726663^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440441369 1000000000 33879133726663 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4404413791/10000000000 : ℝ)^33 ≤ (8469783688043/25000000000000 : ℝ)^25 := by
    have hnat : (4404413791 : ℕ)^33*25000000000000^25 ≤ 8469783688043^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404413791 10000000000 8469783688043 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242185589/10000000000 : ℝ), (440441369/1000000000 : ℝ), (4404413791/10000000000 : ℝ)] ![(6448346298553/20000000000000 : ℝ), (33879133726663/100000000000000 : ℝ), (8469783688043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242185589/10000000000 : ℝ)|^33 ≤ (6448346298553/20000000000000 : ℝ)^25
        have hw : |(4242185589/10000000000 : ℝ)|=(4242185589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440441369/1000000000 : ℝ)|^33 ≤ (33879133726663/100000000000000 : ℝ)^25
        have hw : |(440441369/1000000000 : ℝ)|=(440441369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4404413791/10000000000 : ℝ)|^33 ≤ (8469783688043/25000000000000 : ℝ)^25
        have hw : |(4404413791/10000000000 : ℝ)|=(4404413791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_8 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2186691071/10000000000 : ℝ)*x 0 + (521948171/1000000000 : ℝ)*x 1 + (5384259533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186691071/10000000000 : ℝ)^33 ≤ (13443718486059/100000000000000 : ℝ)^25 := by
    have hnat : (2186691071 : ℕ)^33*100000000000000^25 ≤ 13443718486059^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186691071 10000000000 13443718486059 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521948171/1000000000 : ℝ)^33 ≤ (42390461206819/100000000000000 : ℝ)^25 := by
    have hnat : (521948171 : ℕ)^33*100000000000000^25 ≤ 42390461206819^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521948171 1000000000 42390461206819 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384259533/10000000000 : ℝ)^33 ≤ (11041455074689/25000000000000 : ℝ)^25 := by
    have hnat : (5384259533 : ℕ)^33*25000000000000^25 ≤ 11041455074689^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384259533 10000000000 11041455074689 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2186691071/10000000000 : ℝ), (521948171/1000000000 : ℝ), (5384259533/10000000000 : ℝ)] ![(13443718486059/100000000000000 : ℝ), (42390461206819/100000000000000 : ℝ), (11041455074689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2186691071/10000000000 : ℝ)|^33 ≤ (13443718486059/100000000000000 : ℝ)^25
        have hw : |(-2186691071/10000000000 : ℝ)|=(2186691071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521948171/1000000000 : ℝ)|^33 ≤ (42390461206819/100000000000000 : ℝ)^25
        have hw : |(521948171/1000000000 : ℝ)|=(521948171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384259533/10000000000 : ℝ)|^33 ≤ (11041455074689/25000000000000 : ℝ)^25
        have hw : |(5384259533/10000000000 : ℝ)|=(5384259533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_9 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5290106907/10000000000 : ℝ)*x 0 + (-2092538051/10000000000 : ℝ)*x 1 + (2692129541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290106907/10000000000 : ℝ)^33 ≤ (431492322049/1000000000000 : ℝ)^25 := by
    have hnat : (5290106907 : ℕ)^33*1000000000000^25 ≤ 431492322049^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290106907 10000000000 431492322049 1000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092538051/10000000000 : ℝ)^33 ≤ (6342476179697/50000000000000 : ℝ)^25 := by
    have hnat : (2092538051 : ℕ)^33*50000000000000^25 ≤ 6342476179697^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092538051 10000000000 6342476179697 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692129541/5000000000 : ℝ)^33 ≤ (22082907707743/50000000000000 : ℝ)^25 := by
    have hnat : (2692129541 : ℕ)^33*50000000000000^25 ≤ 22082907707743^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692129541 5000000000 22082907707743 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290106907/10000000000 : ℝ), (-2092538051/10000000000 : ℝ), (2692129541/5000000000 : ℝ)] ![(431492322049/1000000000000 : ℝ), (6342476179697/50000000000000 : ℝ), (22082907707743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290106907/10000000000 : ℝ)|^33 ≤ (431492322049/1000000000000 : ℝ)^25
        have hw : |(5290106907/10000000000 : ℝ)|=(5290106907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2092538051/10000000000 : ℝ)|^33 ≤ (6342476179697/50000000000000 : ℝ)^25
        have hw : |(-2092538051/10000000000 : ℝ)|=(2092538051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692129541/5000000000 : ℝ)|^33 ≤ (22082907707743/50000000000000 : ℝ)^25
        have hw : |(2692129541/5000000000 : ℝ)|=(2692129541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_10 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1322526631/2500000000 : ℝ)*x 0 + (5384259911/10000000000 : ℝ)*x 1 + (-418507489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322526631/2500000000 : ℝ)^33 ≤ (8629845616251/20000000000000 : ℝ)^25 := by
    have hnat : (1322526631 : ℕ)^33*20000000000000^25 ≤ 8629845616251^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322526631 2500000000 8629845616251 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384259911/10000000000 : ℝ)^33 ≤ (5520728048951/12500000000000 : ℝ)^25 := by
    have hnat : (5384259911 : ℕ)^33*12500000000000^25 ≤ 5520728048951^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384259911 10000000000 5520728048951 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418507489/2000000000 : ℝ)^33 ≤ (3171236877571/25000000000000 : ℝ)^25 := by
    have hnat : (418507489 : ℕ)^33*25000000000000^25 ≤ 3171236877571^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418507489 2000000000 3171236877571 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322526631/2500000000 : ℝ), (5384259911/10000000000 : ℝ), (-418507489/2000000000 : ℝ)] ![(8629845616251/20000000000000 : ℝ), (5520728048951/12500000000000 : ℝ), (3171236877571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322526631/2500000000 : ℝ)|^33 ≤ (8629845616251/20000000000000 : ℝ)^25
        have hw : |(1322526631/2500000000 : ℝ)|=(1322526631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384259911/10000000000 : ℝ)|^33 ≤ (5520728048951/12500000000000 : ℝ)^25
        have hw : |(5384259911/10000000000 : ℝ)|=(5384259911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418507489/2000000000 : ℝ)|^33 ≤ (3171236877571/25000000000000 : ℝ)^25
        have hw : |(-418507489/2000000000 : ℝ)|=(418507489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_11 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2238674171/5000000000 : ℝ)*x 0 + (1071677959/2500000000 : ℝ)*x 1 + (4286711837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238674171/5000000000 : ℝ)^33 ≤ (34621634496287/100000000000000 : ℝ)^25 := by
    have hnat : (2238674171 : ℕ)^33*100000000000000^25 ≤ 34621634496287^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238674171 5000000000 34621634496287 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071677959/2500000000 : ℝ)^33 ≤ (32689182736579/100000000000000 : ℝ)^25 := by
    have hnat : (1071677959 : ℕ)^33*100000000000000^25 ≤ 32689182736579^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071677959 2500000000 32689182736579 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4286711837/10000000000 : ℝ)^33 ≤ (6537836549329/20000000000000 : ℝ)^25 := by
    have hnat : (4286711837 : ℕ)^33*20000000000000^25 ≤ 6537836549329^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286711837 10000000000 6537836549329 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2238674171/5000000000 : ℝ), (1071677959/2500000000 : ℝ), (4286711837/10000000000 : ℝ)] ![(34621634496287/100000000000000 : ℝ), (32689182736579/100000000000000 : ℝ), (6537836549329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2238674171/5000000000 : ℝ)|^33 ≤ (34621634496287/100000000000000 : ℝ)^25
        have hw : |(2238674171/5000000000 : ℝ)|=(2238674171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1071677959/2500000000 : ℝ)|^33 ≤ (32689182736579/100000000000000 : ℝ)^25
        have hw : |(1071677959/2500000000 : ℝ)|=(1071677959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4286711837/10000000000 : ℝ)|^33 ≤ (6537836549329/20000000000000 : ℝ)^25
        have hw : |(4286711837/10000000000 : ℝ)|=(4286711837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_12 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1021463161/5000000000 : ℝ)*x 0 + (5436380813/10000000000 : ℝ)*x 1 + (659291559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021463161/5000000000 : ℝ)^33 ≤ (6144740881311/50000000000000 : ℝ)^25 := by
    have hnat : (1021463161 : ℕ)^33*50000000000000^25 ≤ 6144740881311^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021463161 5000000000 6144740881311 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436380813/10000000000 : ℝ)^33 ≤ (11182760877367/25000000000000 : ℝ)^25 := by
    have hnat : (5436380813 : ℕ)^33*25000000000000^25 ≤ 11182760877367^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436380813 10000000000 11182760877367 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659291559/1250000000 : ℝ)^33 ≤ (21489737351419/50000000000000 : ℝ)^25 := by
    have hnat : (659291559 : ℕ)^33*50000000000000^25 ≤ 21489737351419^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659291559 1250000000 21489737351419 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1021463161/5000000000 : ℝ), (5436380813/10000000000 : ℝ), (659291559/1250000000 : ℝ)] ![(6144740881311/50000000000000 : ℝ), (11182760877367/25000000000000 : ℝ), (21489737351419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1021463161/5000000000 : ℝ)|^33 ≤ (6144740881311/50000000000000 : ℝ)^25
        have hw : |(-1021463161/5000000000 : ℝ)|=(1021463161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436380813/10000000000 : ℝ)|^33 ≤ (11182760877367/25000000000000 : ℝ)^25
        have hw : |(5436380813/10000000000 : ℝ)|=(5436380813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659291559/1250000000 : ℝ)|^33 ≤ (21489737351419/50000000000000 : ℝ)^25
        have hw : |(659291559/1250000000 : ℝ)|=(659291559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_13 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (214703079/400000000 : ℝ)*x 0 + (-2136170899/10000000000 : ℝ)*x 1 + (52743319/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214703079/400000000 : ℝ)^33 ≤ (43985276994429/100000000000000 : ℝ)^25 := by
    have hnat : (214703079 : ℕ)^33*100000000000000^25 ≤ 43985276994429^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214703079 400000000 43985276994429 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136170899/10000000000 : ℝ)^33 ≤ (13035254435473/100000000000000 : ℝ)^25 := by
    have hnat : (2136170899 : ℕ)^33*100000000000000^25 ≤ 13035254435473^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136170899 10000000000 13035254435473 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52743319/100000000 : ℝ)^33 ≤ (42979468550169/100000000000000 : ℝ)^25 := by
    have hnat : (52743319 : ℕ)^33*100000000000000^25 ≤ 42979468550169^25*100000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52743319 100000000 42979468550169 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214703079/400000000 : ℝ), (-2136170899/10000000000 : ℝ), (52743319/100000000 : ℝ)] ![(43985276994429/100000000000000 : ℝ), (13035254435473/100000000000000 : ℝ), (42979468550169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214703079/400000000 : ℝ)|^33 ≤ (43985276994429/100000000000000 : ℝ)^25
        have hw : |(214703079/400000000 : ℝ)|=(214703079/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136170899/10000000000 : ℝ)|^33 ≤ (13035254435473/100000000000000 : ℝ)^25
        have hw : |(-2136170899/10000000000 : ℝ)|=(2136170899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52743319/100000000 : ℝ)|^33 ≤ (42979468550169/100000000000000 : ℝ)^25
        have hw : |(52743319/100000000 : ℝ)|=(52743319/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_14 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5367576647/10000000000 : ℝ)*x 0 + (329645751/625000000 : ℝ)*x 1 + (-427234237/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367576647/10000000000 : ℝ)^33 ≤ (10996318361621/25000000000000 : ℝ)^25 := by
    have hnat : (5367576647 : ℕ)^33*25000000000000^25 ≤ 10996318361621^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367576647 10000000000 10996318361621 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329645751/625000000 : ℝ)^33 ≤ (42979469797913/100000000000000 : ℝ)^25 := by
    have hnat : (329645751 : ℕ)^33*100000000000000^25 ≤ 42979469797913^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329645751 625000000 42979469797913 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427234237/2000000000 : ℝ)^33 ≤ (325881418479/2500000000000 : ℝ)^25 := by
    have hnat : (427234237 : ℕ)^33*2500000000000^25 ≤ 325881418479^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427234237 2000000000 325881418479 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367576647/10000000000 : ℝ), (329645751/625000000 : ℝ), (-427234237/2000000000 : ℝ)] ![(10996318361621/25000000000000 : ℝ), (42979469797913/100000000000000 : ℝ), (325881418479/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367576647/10000000000 : ℝ)|^33 ≤ (10996318361621/25000000000000 : ℝ)^25
        have hw : |(5367576647/10000000000 : ℝ)|=(5367576647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329645751/625000000 : ℝ)|^33 ≤ (42979469797913/100000000000000 : ℝ)^25
        have hw : |(329645751/625000000 : ℝ)|=(329645751/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427234237/2000000000 : ℝ)|^33 ≤ (325881418479/2500000000000 : ℝ)^25
        have hw : |(-427234237/2000000000 : ℝ)|=(427234237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_box_15 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2111632689/5000000000 : ℝ)*x 0 + (4413750833/10000000000 : ℝ)*x 1 + (4413751319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111632689/5000000000 : ℝ)^33 ≤ (4006506615671/12500000000000 : ℝ)^25 := by
    have hnat : (2111632689 : ℕ)^33*12500000000000^25 ≤ 4006506615671^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111632689 5000000000 4006506615671 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4413750833/10000000000 : ℝ)^33 ≤ (16986985531569/50000000000000 : ℝ)^25 := by
    have hnat : (4413750833 : ℕ)^33*50000000000000^25 ≤ 16986985531569^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413750833 10000000000 16986985531569 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4413751319/10000000000 : ℝ)^33 ≤ (33973976001111/100000000000000 : ℝ)^25 := by
    have hnat : (4413751319 : ℕ)^33*100000000000000^25 ≤ 33973976001111^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413751319 10000000000 33973976001111 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2111632689/5000000000 : ℝ), (4413750833/10000000000 : ℝ), (4413751319/10000000000 : ℝ)] ![(4006506615671/12500000000000 : ℝ), (16986985531569/50000000000000 : ℝ), (33973976001111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2111632689/5000000000 : ℝ)|^33 ≤ (4006506615671/12500000000000 : ℝ)^25
        have hw : |(2111632689/5000000000 : ℝ)|=(2111632689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4413750833/10000000000 : ℝ)|^33 ≤ (16986985531569/50000000000000 : ℝ)^25
        have hw : |(4413750833/10000000000 : ℝ)|=(4413750833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4413751319/10000000000 : ℝ)|^33 ≤ (33973976001111/100000000000000 : ℝ)^25
        have hw : |(4413751319/10000000000 : ℝ)|=(4413751319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1255_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62249/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14847/25000 : ℝ) ∧ (80147/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41687/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2299/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2299/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2299/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2299/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2299/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2299/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2299/20000 : ℝ) ^ (8447/2048 : ℝ) ≤ (13337003348926991/100000000000000000000 : ℝ) := by
    have hpowers : (2299/20000 : ℝ)^8447 ≤ (13337003348926991/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2299 : ℕ)^8447*100000000000000000000^2048 ≤ 13337003348926991^2048*20000^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2299 20000 13337003348926991 100000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2299/20000 : ℝ)) (X := (13337003348926991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14111/100000 : ℝ) ^ (8447/2048 : ℝ) ≤ (31069992356417793/100000000000000000000 : ℝ) := by
    have hpowers : (14111/100000 : ℝ)^8447 ≤ (31069992356417793/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14111 : ℕ)^8447*100000000000000000000^2048 ≤ 31069992356417793^2048*100000^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14111 100000 31069992356417793 100000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14111/100000 : ℝ)) (X := (31069992356417793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013337003348926991/50000000000000000000 : ℝ) ≤ (10000646653809081/10000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (50013337003348926991/50000000000000000000 : ℝ)^2048 ≤ (10000646653809081/10000000000000000 : ℝ)^8447 := by
      have hnat : (50013337003348926991 : ℕ)^2048*10000000000000000^8447 ≤ 10000646653809081^8447*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013337003348926991 50000000000000000000 10000646653809081 10000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000646653809081/10000000000000000 : ℝ)) (X := (50013337003348926991/50000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252775437231584049/6250000000000000000 : ℝ) ≤ (1000107647962553/1000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (6252775437231584049/6250000000000000000 : ℝ)^2048 ≤ (1000107647962553/1000000000000000 : ℝ)^8447 := by
      have hnat : (6252775437231584049 : ℕ)^2048*1000000000000000^8447 ≤ 1000107647962553^8447*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252775437231584049 6250000000000000000 1000107647962553 1000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000107647962553/1000000000000000 : ℝ)) (X := (6252775437231584049/6250000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031069992356417793/50000000000000000000 : ℝ) ≤ (10001506305441979/10000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (50031069992356417793/50000000000000000000 : ℝ)^2048 ≤ (10001506305441979/10000000000000000 : ℝ)^8447 := by
      have hnat : (50031069992356417793 : ℕ)^2048*10000000000000000^8447 ≤ 10001506305441979^8447*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031069992356417793 50000000000000000000 10001506305441979 10000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001506305441979/10000000000000000 : ℝ)) (X := (50031069992356417793/50000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13337003348926991/100000000000000000000 : ℝ) ≤ ((13075904975422196693/13080000000000000000 : ℝ)+2*(429825816449/261600000000000 : ℝ)*(2299/20000 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (13075904975422196693/13080000000000000000 : ℝ)+2*(429825816449/261600000000000 : ℝ)*(2299/20000 : ℝ)=(10000646653809081/10000000000000000 : ℝ) by norm_num, show 1+2*(13337003348926991/100000000000000000000 : ℝ)=(50013337003348926991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31069992356417793/100000000000000000000 : ℝ)+(13337003348926991/100000000000000000000 : ℝ) ≤ ((13075904975422196693/13080000000000000000 : ℝ)+(429825816449/261600000000000 : ℝ)*((14111/100000 : ℝ)+(2299/20000 : ℝ)))^(8447/2048 : ℝ) := by
    rw [show (13075904975422196693/13080000000000000000 : ℝ)+(429825816449/261600000000000 : ℝ)*((14111/100000 : ℝ)+(2299/20000 : ℝ))=(1000107647962553/1000000000000000 : ℝ) by norm_num, show 1+(31069992356417793/100000000000000000000 : ℝ)+(13337003348926991/100000000000000000000 : ℝ)=(6252775437231584049/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31069992356417793/100000000000000000000 : ℝ) ≤ ((13075904975422196693/13080000000000000000 : ℝ)+2*(429825816449/261600000000000 : ℝ)*(14111/100000 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (13075904975422196693/13080000000000000000 : ℝ)+2*(429825816449/261600000000000 : ℝ)*(14111/100000 : ℝ)=(10001506305441979/10000000000000000 : ℝ) by norm_num, show 1+2*(31069992356417793/100000000000000000000 : ℝ)=(50031069992356417793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13075904975422196693/13080000000000000000 : ℝ)*(X 1 0+X 2 0)+(429825816449/261600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (13075904975422196693/13080000000000000000 : ℝ)) (alpha := (429825816449/261600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13075904975422196693/13080000000000000000 : ℝ)*(X 0 1+X 2 1)+(429825816449/261600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (13075904975422196693/13080000000000000000 : ℝ)) (alpha := (429825816449/261600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13075904975422196693/13080000000000000000 : ℝ)*(X 0 2+X 1 2)+(429825816449/261600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (13075904975422196693/13080000000000000000 : ℝ)) (alpha := (429825816449/261600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1990699739/10000000000 : ℝ)*X 0 0+(2687323209/5000000000 : ℝ)*X 0 1+(5374646289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296884279/10000000000 : ℝ)*X 1 0+(-2096419429/10000000000 : ℝ)*X 1 1+(2687323237/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1324221031/2500000000 : ℝ)*X 2 0+(5374646421/10000000000 : ℝ)*X 2 1+(-209641971/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4455396843/10000000000 : ℝ)*X 0 0+(1074457009/2500000000 : ℝ)*X 0 1+(537228527/1250000000 : ℝ)*X 0 2+(4455396843/10000000000 : ℝ)*X 1 0+(1074457009/2500000000 : ℝ)*X 1 1+(537228527/1250000000 : ℝ)*X 1 2+(4455396843/10000000000 : ℝ)*X 2 0+(1074457009/2500000000 : ℝ)*X 2 1+(537228527/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-139916567/625000000 : ℝ)*X 0 0+(1056483279/2000000000 : ℝ)*X 0 1+(5282416399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2680940599/5000000000 : ℝ)*X 1 0+(-1066509539/5000000000 : ℝ)*X 1 1+(5282416411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5361881227/10000000000 : ℝ)*X 2 0+(660302049/1250000000 : ℝ)*X 2 1+(-266627383/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242185589/10000000000 : ℝ)*X 0 0+(440441369/1000000000 : ℝ)*X 0 1+(4404413791/10000000000 : ℝ)*X 0 2+(4242185589/10000000000 : ℝ)*X 1 0+(440441369/1000000000 : ℝ)*X 1 1+(4404413791/10000000000 : ℝ)*X 1 2+(4242185589/10000000000 : ℝ)*X 2 0+(440441369/1000000000 : ℝ)*X 2 1+(4404413791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2186691071/10000000000 : ℝ)*X 0 0+(521948171/1000000000 : ℝ)*X 0 1+(5384259533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5290106907/10000000000 : ℝ)*X 1 0+(-2092538051/10000000000 : ℝ)*X 1 1+(2692129541/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322526631/2500000000 : ℝ)*X 2 0+(5384259911/10000000000 : ℝ)*X 2 1+(-418507489/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2238674171/5000000000 : ℝ)*X 0 0+(1071677959/2500000000 : ℝ)*X 0 1+(4286711837/10000000000 : ℝ)*X 0 2+(2238674171/5000000000 : ℝ)*X 1 0+(1071677959/2500000000 : ℝ)*X 1 1+(4286711837/10000000000 : ℝ)*X 1 2+(2238674171/5000000000 : ℝ)*X 2 0+(1071677959/2500000000 : ℝ)*X 2 1+(4286711837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1021463161/5000000000 : ℝ)*X 0 0+(5436380813/10000000000 : ℝ)*X 0 1+(659291559/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((214703079/400000000 : ℝ)*X 1 0+(-2136170899/10000000000 : ℝ)*X 1 1+(52743319/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367576647/10000000000 : ℝ)*X 2 0+(329645751/625000000 : ℝ)*X 2 1+(-427234237/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2111632689/5000000000 : ℝ)*X 0 0+(4413750833/10000000000 : ℝ)*X 0 1+(4413751319/10000000000 : ℝ)*X 0 2+(2111632689/5000000000 : ℝ)*X 1 0+(4413750833/10000000000 : ℝ)*X 1 1+(4413751319/10000000000 : ℝ)*X 1 2+(2111632689/5000000000 : ℝ)*X 2 0+(4413750833/10000000000 : ℝ)*X 2 1+(4413751319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62249/100000 : ℝ) ≤ (-33924460075331894781991829759031/54500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (332943/800000000000 : ℝ)*(upper0) + (31515499/100000000000000 : ℝ)*(upper1) + (32572001/100000000000000 : ℝ)*(upper3) + (65580573/100000000000000 : ℝ)*(upper5) + (2006897181080733/50000000000000 : ℝ)*(major0) + (2006897181080733/50000000000000 : ℝ)*(major1) + (2006897181080733/50000000000000 : ℝ)*(major2) + (1205152749/50000000000000 : ℝ)*(sp2) + (2381058791/50000000000000 : ℝ)*(sp3) + (2701083763883729/50000000000000 : ℝ)*(sp4) + (5402168060556951/100000000000000 : ℝ)*(sp5) + (5402165650251453/100000000000000 : ℝ)*(sp6) + (529232961378647/20000000000000 : ℝ)*(sp7) + (266394747/50000000000000 : ℝ)*(sp8) + (20673199757897/781250000000 : ℝ)*(f.failure) + (5402168060556951/100000000000000 : ℝ)*(f.sum) + (7584099341341/2180000000000000000000000000 : ℝ)*base66 + (7793393555437844677/218000000000000000000000000000000 : ℝ)*base68 + (3155036694760155323/218000000000000000000000000000000 : ℝ)*base69 + (250734511403844677/218000000000000000000000000000000 : ℝ)*base72 + (22541201275281/2180000000000000000000000000 : ℝ)*base74 + (5480604459345844677/218000000000000000000000000000000 : ℝ)*base76 + (41711595533844677/218000000000000000000000000000000 : ℝ)*base78 + (6810543080749844677/218000000000000000000000000000000 : ℝ)*base80 + (21875488355461/2180000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5527/2441406250000000000 : ℝ)*base90 + (5527/2441406250000000000 : ℝ)*base92 + (5527/2441406250000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (14847/25000 : ℝ) ≤ (64735433959204047819079060458339/109000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9025483/10000000000000 : ℝ)*(lower1) + (1255009/1250000000000 : ℝ)*(upper2) + (186021967/100000000000000 : ℝ)*(lower5) + (4079807648364177/100000000000000 : ℝ)*(major0) + (4079807648364177/100000000000000 : ℝ)*(major1) + (4079807648364177/100000000000000 : ℝ)*(major2) + (5450116133755819/100000000000000 : ℝ)*(sp0) + (545011390741231/10000000000000 : ℝ)*(sp1) + (1362529089341757/25000000000000 : ℝ)*(sp2) + (537937408417231/20000000000000 : ℝ)*(sp3) + (14548629897/100000000000000 : ℝ)*(sp5) + (12098675179/100000000000000 : ℝ)*(sp6) + (3029805119/100000000000000 : ℝ)*(sp11) + (3080571597/25000000000000 : ℝ)*(sp12) + (1344845035945637/50000000000000 : ℝ)*(f.failure) + (5450128456042207/100000000000000 : ℝ)*(f.sum) + (4573402428469/4360000000000000000000000000 : ℝ)*base66 + (4054761133654238887/436000000000000000000000000000000 : ℝ)*base67 + (4095296027494238887/436000000000000000000000000000000 : ℝ)*base69 + (2587877236130238887/436000000000000000000000000000000 : ℝ)*base71 + (2407180271611/4360000000000000000000000000 : ℝ)*base73 + (6645356355414238887/436000000000000000000000000000000 : ℝ)*base75 + (512159939793761113/436000000000000000000000000000000 : ℝ)*base78 + (5115348063534238887/436000000000000000000000000000000 : ℝ)*base79 + (18489804845571/4360000000000000000000000000 : ℝ)*base81 + (8787311/1250000000000000000000 : ℝ)*base90 + (8787311/1250000000000000000000 : ℝ)*base92 + (8787311/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80147/100000 : ℝ) ≤ (43681543300367639261236765974461/54500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68087707/20000000000000 : ℝ)*(lower3) + (14898383/10000000000000 : ℝ)*(upper4) + (4771281/2500000000000 : ℝ)*(lower5) + (2273210382683777/50000000000000 : ℝ)*(major0) + (2273210382683777/50000000000000 : ℝ)*(major1) + (2273210382683777/50000000000000 : ℝ)*(major2) + (22213862543/100000000000000 : ℝ)*(sp0) + (45819962993/50000000000000 : ℝ)*(sp1) + (654401402871/100000000000000 : ℝ)*(sp2) + (51826040087/20000000000000 : ℝ)*(sp3) + (3034394607257937/50000000000000 : ℝ)*(sp8) + (379294986778277/6250000000000 : ℝ)*(sp9) + (3034078513487773/50000000000000 : ℝ)*(sp10) + (187315901994461/6250000000000 : ℝ)*(sp11) + (299731356211181/10000000000000 : ℝ)*(f.failure) + (6068811428378417/100000000000000 : ℝ)*(f.sum) + (22987421150233/6540000000000000000000000000 : ℝ)*base65 + (451601953010733513/218000000000000000000000000000000 : ℝ)*base68 + (2605634649968733513/218000000000000000000000000000000 : ℝ)*base70 + (376993568700733513/218000000000000000000000000000000 : ℝ)*base72 + (33297456444073/6540000000000000000000000000 : ℝ)*base73 + (1808077512110733513/218000000000000000000000000000000 : ℝ)*base76 + (215996909879266487/218000000000000000000000000000000 : ℝ)*base77 + (97880730104733513/218000000000000000000000000000000 : ℝ)*base80 + (5187528821807/6540000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1168743/250000000000000000000 : ℝ)*base90 + (1168743/250000000000000000000 : ℝ)*base92 + (1168743/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-41687/50000 : ℝ) ≤ (-181750137464198443780908845636601/218000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10375119/25000000000000 : ℝ)*(upper3) + (34581791/12500000000000 : ℝ)*(lower4) + (26462529/50000000000000 : ℝ)*(upper5) + (4582004021919243/100000000000000 : ℝ)*(major0) + (4582004021919243/100000000000000 : ℝ)*(major1) + (4582004021919243/100000000000000 : ℝ)*(major2) + (17800477027/100000000000000 : ℝ)*(sp4) + (505748515139/100000000000000 : ℝ)*(sp5) + (159034693189/25000000000000 : ℝ)*(sp6) + (60866443929/25000000000000 : ℝ)*(sp7) + (1234201657947073/20000000000000 : ℝ)*(sp12) + (6170520341697253/100000000000000 : ℝ)*(sp13) + (1542597487859909/25000000000000 : ℝ)*(sp14) + (3020529028747041/100000000000000 : ℝ)*(sp15) + (3020772494522757/100000000000000 : ℝ)*(f.failure) + (771378261276549/12500000000000 : ℝ)*(f.sum) + (6797214891911/4360000000000000000000000000 : ℝ)*base66 + (250752825470328867/436000000000000000000000000000000 : ℝ)*base68 + (3897822143330328867/436000000000000000000000000000000 : ℝ)*base70 + (156029586753671133/436000000000000000000000000000000 : ℝ)*base71 + (9972216427929/4360000000000000000000000000 : ℝ)*base73 + (1029804889666328867/436000000000000000000000000000000 : ℝ)*base76 + (2949383091301671133/436000000000000000000000000000000 : ℝ)*base77 + (740988224918328867/436000000000000000000000000000000 : ℝ)*base80 + (33619772015391/4360000000000000000000000000 : ℝ)*base82 + (5077329/2500000000000000000000 : ℝ)*base89 + (5077329/2500000000000000000000 : ℝ)*base91 + (5077329/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1255_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14847/25000 : ℝ) else (80147/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41687/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1255_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1255_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14847/25000 : ℝ) else (80147/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41687/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1255_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14847/25000 : ℝ) else (80147/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41687/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1255_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

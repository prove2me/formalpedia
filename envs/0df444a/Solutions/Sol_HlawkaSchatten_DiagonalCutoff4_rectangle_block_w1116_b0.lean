-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1116_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:07:19.833381+00:00
-- url     : https://prove2.me/submissions/ccb3a5f2-16ab-4f41-a274-60a97902446f

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
theorem support_rectangle_w1116_s0_0 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1900067023/10000000000 : ℝ)*x 0 + (94693109/156250000 : ℝ)*x 1 + (955435053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1900067023/10000000000 : ℝ)^8309 ≤ (11037002367689/100000000000000 : ℝ)^6261 := by
    have hnat : (1900067023 : ℕ)^8309*100000000000000^6261 ≤ 11037002367689^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900067023 10000000000 11037002367689 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94693109/156250000 : ℝ)^8309 ≤ (6430764985019/12500000000000 : ℝ)^6261 := by
    have hnat : (94693109 : ℕ)^8309*12500000000000^6261 ≤ 6430764985019^6261*156250000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94693109 156250000 6430764985019 12500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955435053/2000000000 : ℝ)^8309 ≤ (7503375545913/20000000000000 : ℝ)^6261 := by
    have hnat : (955435053 : ℕ)^8309*20000000000000^6261 ≤ 7503375545913^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955435053 2000000000 7503375545913 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1900067023/10000000000 : ℝ), (94693109/156250000 : ℝ), (955435053/2000000000 : ℝ)] ![(11037002367689/100000000000000 : ℝ), (6430764985019/12500000000000 : ℝ), (7503375545913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1900067023/10000000000 : ℝ)|^8309 ≤ (11037002367689/100000000000000 : ℝ)^6261
        have hw : |(-1900067023/10000000000 : ℝ)|=(1900067023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(94693109/156250000 : ℝ)|^8309 ≤ (6430764985019/12500000000000 : ℝ)^6261
        have hw : |(94693109/156250000 : ℝ)|=(94693109/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955435053/2000000000 : ℝ)|^8309 ≤ (7503375545913/20000000000000 : ℝ)^6261
        have hw : |(955435053/2000000000 : ℝ)|=(955435053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s0_1 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34489113/62500000 : ℝ)*x 0 + (-52744289/200000000 : ℝ)*x 1 + (477717531/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34489113/62500000 : ℝ)^8309 ≤ (1135754180331/2500000000000 : ℝ)^6261 := by
    have hnat : (34489113 : ℕ)^8309*2500000000000^6261 ≤ 1135754180331^6261*62500000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34489113 62500000 1135754180331 2500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52744289/200000000 : ℝ)^8309 ≤ (852647728929/5000000000000 : ℝ)^6261 := by
    have hnat : (52744289 : ℕ)^8309*5000000000000^6261 ≤ 852647728929^6261*200000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52744289 200000000 852647728929 5000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477717531/1000000000 : ℝ)^8309 ≤ (18758439099283/50000000000000 : ℝ)^6261 := by
    have hnat : (477717531 : ℕ)^8309*50000000000000^6261 ≤ 18758439099283^6261*1000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477717531 1000000000 18758439099283 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34489113/62500000 : ℝ), (-52744289/200000000 : ℝ), (477717531/1000000000 : ℝ)] ![(1135754180331/2500000000000 : ℝ), (852647728929/5000000000000 : ℝ), (18758439099283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34489113/62500000 : ℝ)|^8309 ≤ (1135754180331/2500000000000 : ℝ)^6261
        have hw : |(34489113/62500000 : ℝ)|=(34489113/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52744289/200000000 : ℝ)|^8309 ≤ (852647728929/5000000000000 : ℝ)^6261
        have hw : |(-52744289/200000000 : ℝ)|=(52744289/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477717531/1000000000 : ℝ)|^8309 ≤ (18758439099283/50000000000000 : ℝ)^6261
        have hw : |(477717531/1000000000 : ℝ)|=(477717531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s0_2 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5518258237/10000000000 : ℝ)*x 0 + (4777175163/10000000000 : ℝ)*x 1 + (-2637214429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518258237/10000000000 : ℝ)^8309 ≤ (45430168928567/100000000000000 : ℝ)^6261 := by
    have hnat : (5518258237 : ℕ)^8309*100000000000000^6261 ≤ 45430168928567^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518258237 10000000000 45430168928567 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4777175163/10000000000 : ℝ)^8309 ≤ (18758438333249/50000000000000 : ℝ)^6261 := by
    have hnat : (4777175163 : ℕ)^8309*50000000000000^6261 ≤ 18758438333249^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4777175163 10000000000 18758438333249 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637214429/10000000000 : ℝ)^8309 ≤ (1705295439837/10000000000000 : ℝ)^6261 := by
    have hnat : (2637214429 : ℕ)^8309*10000000000000^6261 ≤ 1705295439837^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637214429 10000000000 1705295439837 10000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518258237/10000000000 : ℝ), (4777175163/10000000000 : ℝ), (-2637214429/10000000000 : ℝ)] ![(45430168928567/100000000000000 : ℝ), (18758438333249/50000000000000 : ℝ), (1705295439837/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518258237/10000000000 : ℝ)|^8309 ≤ (45430168928567/100000000000000 : ℝ)^6261
        have hw : |(5518258237/10000000000 : ℝ)|=(5518258237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4777175163/10000000000 : ℝ)|^8309 ≤ (18758438333249/50000000000000 : ℝ)^6261
        have hw : |(4777175163/10000000000 : ℝ)|=(4777175163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2637214429/10000000000 : ℝ)|^8309 ≤ (1705295439837/10000000000000 : ℝ)^6261
        have hw : |(-2637214429/10000000000 : ℝ)|=(2637214429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s0_3 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (840620401/2000000000 : ℝ)*x 0 + (3122313799/10000000000 : ℝ)*x 1 + (283108123/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840620401/2000000000 : ℝ)^8309 ≤ (31654687963699/100000000000000 : ℝ)^6261 := by
    have hnat : (840620401 : ℕ)^8309*100000000000000^6261 ≤ 31654687963699^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840620401 2000000000 31654687963699 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122313799/10000000000 : ℝ)^8309 ≤ (21336228582229/100000000000000 : ℝ)^6261 := by
    have hnat : (3122313799 : ℕ)^8309*100000000000000^6261 ≤ 21336228582229^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122313799 10000000000 21336228582229 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283108123/500000000 : ℝ)^8309 ≤ (47009083443667/100000000000000 : ℝ)^6261 := by
    have hnat : (283108123 : ℕ)^8309*100000000000000^6261 ≤ 47009083443667^6261*500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283108123 500000000 47009083443667 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840620401/2000000000 : ℝ), (3122313799/10000000000 : ℝ), (283108123/500000000 : ℝ)] ![(31654687963699/100000000000000 : ℝ), (21336228582229/100000000000000 : ℝ), (47009083443667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840620401/2000000000 : ℝ)|^8309 ≤ (31654687963699/100000000000000 : ℝ)^6261
        have hw : |(840620401/2000000000 : ℝ)|=(840620401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122313799/10000000000 : ℝ)|^8309 ≤ (21336228582229/100000000000000 : ℝ)^6261
        have hw : |(3122313799/10000000000 : ℝ)|=(3122313799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283108123/500000000 : ℝ)|^8309 ≤ (47009083443667/100000000000000 : ℝ)^6261
        have hw : |(283108123/500000000 : ℝ)|=(283108123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s0_4 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-952645379/5000000000 : ℝ)*x 0 + (4810290523/10000000000 : ℝ)*x 1 + (6026080681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952645379/5000000000 : ℝ)^8309 ≤ (11077289237127/100000000000000 : ℝ)^6261 := by
    have hnat : (952645379 : ℕ)^8309*100000000000000^6261 ≤ 11077289237127^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952645379 5000000000 11077289237127 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4810290523/10000000000 : ℝ)^8309 ≤ (1514496127347/4000000000000 : ℝ)^6261 := by
    have hnat : (4810290523 : ℕ)^8309*4000000000000^6261 ≤ 1514496127347^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810290523 10000000000 1514496127347 4000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6026080681/10000000000 : ℝ)^8309 ≤ (51060307561253/100000000000000 : ℝ)^6261 := by
    have hnat : (6026080681 : ℕ)^8309*100000000000000^6261 ≤ 51060307561253^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6026080681 10000000000 51060307561253 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952645379/5000000000 : ℝ), (4810290523/10000000000 : ℝ), (6026080681/10000000000 : ℝ)] ![(11077289237127/100000000000000 : ℝ), (1514496127347/4000000000000 : ℝ), (51060307561253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952645379/5000000000 : ℝ)|^8309 ≤ (11077289237127/100000000000000 : ℝ)^6261
        have hw : |(-952645379/5000000000 : ℝ)|=(952645379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4810290523/10000000000 : ℝ)|^8309 ≤ (1514496127347/4000000000000 : ℝ)^6261
        have hw : |(4810290523/10000000000 : ℝ)|=(4810290523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6026080681/10000000000 : ℝ)|^8309 ≤ (51060307561253/100000000000000 : ℝ)^6261
        have hw : |(6026080681/10000000000 : ℝ)|=(6026080681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s0_5 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (161553629/312500000 : ℝ)*x 0 + (-347077457/2500000000 : ℝ)*x 1 + (6026083549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161553629/312500000 : ℝ)^8309 ≤ (20831014731651/50000000000000 : ℝ)^6261 := by
    have hnat : (161553629 : ℕ)^8309*50000000000000^6261 ≤ 20831014731651^6261*312500000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161553629 312500000 20831014731651 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347077457/2500000000 : ℝ)^8309 ≤ (909703839413/12500000000000 : ℝ)^6261 := by
    have hnat : (347077457 : ℕ)^8309*12500000000000^6261 ≤ 909703839413^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347077457 2500000000 909703839413 12500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6026083549/10000000000 : ℝ)^8309 ≤ (12765084952869/25000000000000 : ℝ)^6261 := by
    have hnat : (6026083549 : ℕ)^8309*25000000000000^6261 ≤ 12765084952869^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6026083549 10000000000 12765084952869 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161553629/312500000 : ℝ), (-347077457/2500000000 : ℝ), (6026083549/10000000000 : ℝ)] ![(20831014731651/50000000000000 : ℝ), (909703839413/12500000000000 : ℝ), (12765084952869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161553629/312500000 : ℝ)|^8309 ≤ (20831014731651/50000000000000 : ℝ)^6261
        have hw : |(161553629/312500000 : ℝ)|=(161553629/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-347077457/2500000000 : ℝ)|^8309 ≤ (909703839413/12500000000000 : ℝ)^6261
        have hw : |(-347077457/2500000000 : ℝ)|=(347077457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6026083549/10000000000 : ℝ)|^8309 ≤ (12765084952869/25000000000000 : ℝ)^6261
        have hw : |(6026083549/10000000000 : ℝ)|=(6026083549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s0_6 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2584859887/5000000000 : ℝ)*x 0 + (6026081141/10000000000 : ℝ)*x 1 + (-277661623/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584859887/5000000000 : ℝ)^8309 ≤ (41662068457097/100000000000000 : ℝ)^6261 := by
    have hnat : (2584859887 : ℕ)^8309*100000000000000^6261 ≤ 41662068457097^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584859887 5000000000 41662068457097 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6026081141/10000000000 : ℝ)^8309 ≤ (25530156366941/50000000000000 : ℝ)^6261 := by
    have hnat : (6026081141 : ℕ)^8309*50000000000000^6261 ≤ 25530156366941^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6026081141 10000000000 25530156366941 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277661623/2000000000 : ℝ)^8309 ≤ (7277618798331/100000000000000 : ℝ)^6261 := by
    have hnat : (277661623 : ℕ)^8309*100000000000000^6261 ≤ 7277618798331^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277661623 2000000000 7277618798331 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584859887/5000000000 : ℝ), (6026081141/10000000000 : ℝ), (-277661623/2000000000 : ℝ)] ![(41662068457097/100000000000000 : ℝ), (25530156366941/50000000000000 : ℝ), (7277618798331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584859887/5000000000 : ℝ)|^8309 ≤ (41662068457097/100000000000000 : ℝ)^6261
        have hw : |(2584859887/5000000000 : ℝ)|=(2584859887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6026081141/10000000000 : ℝ)|^8309 ≤ (25530156366941/50000000000000 : ℝ)^6261
        have hw : |(6026081141/10000000000 : ℝ)|=(6026081141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277661623/2000000000 : ℝ)|^8309 ≤ (7277618798331/100000000000000 : ℝ)^6261
        have hw : |(-277661623/2000000000 : ℝ)|=(277661623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s0_7 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (421343799/1000000000 : ℝ)*x 0 + (559661949/1000000000 : ℝ)*x 1 + (3190158101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421343799/1000000000 : ℝ)^8309 ≤ (254064282943/800000000000 : ℝ)^6261 := by
    have hnat : (421343799 : ℕ)^8309*800000000000^6261 ≤ 254064282943^6261*1000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421343799 1000000000 254064282943 800000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559661949/1000000000 : ℝ)^8309 ≤ (46288298861801/100000000000000 : ℝ)^6261 := by
    have hnat : (559661949 : ℕ)^8309*100000000000000^6261 ≤ 46288298861801^6261*1000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559661949 1000000000 46288298861801 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3190158101/10000000000 : ℝ)^8309 ≤ (21953665755263/100000000000000 : ℝ)^6261 := by
    have hnat : (3190158101 : ℕ)^8309*100000000000000^6261 ≤ 21953665755263^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3190158101 10000000000 21953665755263 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421343799/1000000000 : ℝ), (559661949/1000000000 : ℝ), (3190158101/10000000000 : ℝ)] ![(254064282943/800000000000 : ℝ), (46288298861801/100000000000000 : ℝ), (21953665755263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421343799/1000000000 : ℝ)|^8309 ≤ (254064282943/800000000000 : ℝ)^6261
        have hw : |(421343799/1000000000 : ℝ)|=(421343799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559661949/1000000000 : ℝ)|^8309 ≤ (46288298861801/100000000000000 : ℝ)^6261
        have hw : |(559661949/1000000000 : ℝ)|=(559661949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3190158101/10000000000 : ℝ)|^8309 ≤ (21953665755263/100000000000000 : ℝ)^6261
        have hw : |(3190158101/10000000000 : ℝ)|=(3190158101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1116_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (153/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5583/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2077/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2077 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2077*1^512 ≤ 0^512*1^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2077/512 : ℝ) ≤ (607631672520513717/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2077 ≤ (607631672520513717/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2077*25000000000000000000^512 ≤ 607631672520513717^512*5^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 607631672520513717 25000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (607631672520513717/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2077 := by
      have hnat : (1 : ℕ)^512*1^2077 ≤ 1^2077*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25607631672520513717/25000000000000000000 : ℝ) ≤ (10059373797605557/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (25607631672520513717/25000000000000000000 : ℝ)^512 ≤ (10059373797605557/10000000000000000 : ℝ)^2077 := by
      have hnat : (25607631672520513717 : ℕ)^512*10000000000000000^2077 ≤ 10059373797605557^2077*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25607631672520513717 25000000000000000000 10059373797605557 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059373797605557/10000000000000000 : ℝ)) (X := (25607631672520513717/25000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13107631672520513717/12500000000000000000 : ℝ) ≤ (5059373797605557/5000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (13107631672520513717/12500000000000000000 : ℝ)^512 ≤ (5059373797605557/5000000000000000 : ℝ)^2077 := by
      have hnat : (13107631672520513717 : ℕ)^512*5000000000000000^2077 ≤ 5059373797605557^2077*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13107631672520513717 12500000000000000000 5059373797605557 5000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059373797605557/5000000000000000 : ℝ)) (X := (13107631672520513717/12500000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59373797605557/4000000000000000 : ℝ)*(0 : ℝ))^(2077/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(59373797605557/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(607631672520513717/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59373797605557/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2077/512 : ℝ) := by
    rw [show (1 : ℝ)+(59373797605557/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059373797605557/10000000000000000 : ℝ) by norm_num, show 1+(607631672520513717/25000000000000000000 : ℝ)+(0 : ℝ)=(25607631672520513717/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(607631672520513717/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59373797605557/4000000000000000 : ℝ)*(2/5 : ℝ))^(2077/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(59373797605557/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059373797605557/5000000000000000 : ℝ) by norm_num, show 1+2*(607631672520513717/25000000000000000000 : ℝ)=(13107631672520513717/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59373797605557/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59373797605557/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59373797605557/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59373797605557/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59373797605557/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59373797605557/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1900067023/10000000000 : ℝ)*X 0 0+(94693109/156250000 : ℝ)*X 0 1+(955435053/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((34489113/62500000 : ℝ)*X 1 0+(-52744289/200000000 : ℝ)*X 1 1+(477717531/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5518258237/10000000000 : ℝ)*X 2 0+(4777175163/10000000000 : ℝ)*X 2 1+(-2637214429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840620401/2000000000 : ℝ)*X 0 0+(3122313799/10000000000 : ℝ)*X 0 1+(283108123/500000000 : ℝ)*X 0 2+(840620401/2000000000 : ℝ)*X 1 0+(3122313799/10000000000 : ℝ)*X 1 1+(283108123/500000000 : ℝ)*X 1 2+(840620401/2000000000 : ℝ)*X 2 0+(3122313799/10000000000 : ℝ)*X 2 1+(283108123/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-952645379/5000000000 : ℝ)*X 0 0+(4810290523/10000000000 : ℝ)*X 0 1+(6026080681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((161553629/312500000 : ℝ)*X 1 0+(-347077457/2500000000 : ℝ)*X 1 1+(6026083549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2584859887/5000000000 : ℝ)*X 2 0+(6026081141/10000000000 : ℝ)*X 2 1+(-277661623/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((421343799/1000000000 : ℝ)*X 0 0+(559661949/1000000000 : ℝ)*X 0 1+(3190158101/10000000000 : ℝ)*X 0 2+(421343799/1000000000 : ℝ)*X 1 0+(559661949/1000000000 : ℝ)*X 1 1+(3190158101/10000000000 : ℝ)*X 1 2+(421343799/1000000000 : ℝ)*X 2 0+(559661949/1000000000 : ℝ)*X 2 1+(3190158101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43861292150952459455631/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49244197/100000000000000 : ℝ)*(base1) + (67825207/6250000000000 : ℝ)*(base19) + (1027717537/100000000000000 : ℝ)*(base23) + (622329/781250000000 : ℝ)*(base24) + (252846779/100000000000000 : ℝ)*(upper3) + (117304500629761/20000000000000 : ℝ)*(major0) + (117304500629761/20000000000000 : ℝ)*(major1) + (117304500629761/20000000000000 : ℝ)*(major2) + (194828804676077/25000000000000 : ℝ)*(sp0) + (779316437661593/100000000000000 : ℝ)*(sp1) + (779316415489257/100000000000000 : ℝ)*(sp2) + (393725360909013/100000000000000 : ℝ)*(sp3) + (1176702397/50000000000000 : ℝ)*(sp4) + (963537591/50000000000000 : ℝ)*(sp7) + (49215917153549/12500000000000 : ℝ)*(f.failure) + (389658761432453/50000000000000 : ℝ)*(f.sum) + (49855879178123/40000000000000000000000000000 : ℝ)*base66 + (131819901778123/80000000000000000000000000000 : ℝ)*base68 + (212765842498123/80000000000000000000000000000 : ℝ)*base70 + (5999838381877/80000000000000000000000000000 : ℝ)*base71 + (95949575498123/40000000000000000000000000000 : ℝ)*base74 + (27862757821877/80000000000000000000000000000 : ℝ)*base75 + (389787239138123/80000000000000000000000000000 : ℝ)*base78 + (419426943458123/80000000000000000000000000000 : ℝ)*base80 + (49648111178123/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1071183/125000000000000000000 : ℝ)*base89 + (1071183/125000000000000000000 : ℝ)*base91 + (1071183/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (434704618732351559571207/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29054587/50000000000000 : ℝ)*(base19) + (1244887609/100000000000000 : ℝ)*(base23) + (571681243/100000000000000 : ℝ)*(base39) + (129165977/100000000000000 : ℝ)*(base45) + (64910433/50000000000000 : ℝ)*(upper3) + (50509219/20000000000000 : ℝ)*(upper5) + (619027082581817/100000000000000 : ℝ)*(major0) + (619027082581817/100000000000000 : ℝ)*(major1) + (619026510900573/100000000000000 : ℝ)*(major2) + (381421871/50000000000000 : ℝ)*(sp2) + (102813259552391/12500000000000 : ℝ)*(sp4) + (411253009154977/50000000000000 : ℝ)*(sp5) + (822504640369021/100000000000000 : ℝ)*(sp6) + (415547372161717/100000000000000 : ℝ)*(sp7) + (415547372161717/100000000000000 : ℝ)*(f.failure) + (205626662025093/25000000000000 : ℝ)*(f.sum) + (24060067675877/40000000000000000000000000000 : ℝ)*base66 + (749991789684161/400000000000000000000000000000 : ℝ)*base67 + (886218087642931/400000000000000000000000000000 : ℝ)*base70 + (1014080322484161/400000000000000000000000000000 : ℝ)*base71 + (71541132155877/40000000000000000000000000000 : ℝ)*base74 + (759290318842931/400000000000000000000000000000 : ℝ)*base76 + (746474971157069/400000000000000000000000000000 : ℝ)*base77 + (399425251557069/400000000000000000000000000000 : ℝ)*base79 + (1067695990442931/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1702761/1000000000000000000000 : ℝ)*base90 + (1702761/1000000000000000000000 : ℝ)*base92 + (8297239/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1116_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (153/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5583/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1116_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1116_s1_0 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526652303/2500000000 : ℝ)*x 0 + (5708513291/10000000000 : ℝ)*x 1 + (999356253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526652303/2500000000 : ℝ)^8309 ≤ (6328421490313/50000000000000 : ℝ)^6261 := by
    have hnat : (526652303 : ℕ)^8309*50000000000000^6261 ≤ 6328421490313^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526652303 2500000000 6328421490313 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5708513291/10000000000 : ℝ)^8309 ≤ (47520461444041/100000000000000 : ℝ)^6261 := by
    have hnat : (5708513291 : ℕ)^8309*100000000000000^6261 ≤ 47520461444041^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5708513291 10000000000 47520461444041 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999356253/2000000000 : ℝ)^8309 ≤ (39822695565031/100000000000000 : ℝ)^6261 := by
    have hnat : (999356253 : ℕ)^8309*100000000000000^6261 ≤ 39822695565031^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999356253 2000000000 39822695565031 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526652303/2500000000 : ℝ), (5708513291/10000000000 : ℝ), (999356253/2000000000 : ℝ)] ![(6328421490313/50000000000000 : ℝ), (47520461444041/100000000000000 : ℝ), (39822695565031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526652303/2500000000 : ℝ)|^8309 ≤ (6328421490313/50000000000000 : ℝ)^6261
        have hw : |(-526652303/2500000000 : ℝ)|=(526652303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5708513291/10000000000 : ℝ)|^8309 ≤ (47520461444041/100000000000000 : ℝ)^6261
        have hw : |(5708513291/10000000000 : ℝ)|=(5708513291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(999356253/2000000000 : ℝ)|^8309 ≤ (39822695565031/100000000000000 : ℝ)^6261
        have hw : |(999356253/2000000000 : ℝ)|=(999356253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s1_1 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5420552261/10000000000 : ℝ)*x 0 + (-2491211989/10000000000 : ℝ)*x 1 + (1249195283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420552261/10000000000 : ℝ)^8309 ≤ (8873154213471/20000000000000 : ℝ)^6261 := by
    have hnat : (5420552261 : ℕ)^8309*20000000000000^6261 ≤ 8873154213471^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420552261 10000000000 8873154213471 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2491211989/10000000000 : ℝ)^8309 ≤ (3162306952069/20000000000000 : ℝ)^6261 := by
    have hnat : (2491211989 : ℕ)^8309*20000000000000^6261 ≤ 3162306952069^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491211989 10000000000 3162306952069 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249195283/2500000000 : ℝ)^8309 ≤ (7964538831669/20000000000000 : ℝ)^6261 := by
    have hnat : (1249195283 : ℕ)^8309*20000000000000^6261 ≤ 7964538831669^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249195283 2500000000 7964538831669 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420552261/10000000000 : ℝ), (-2491211989/10000000000 : ℝ), (1249195283/2500000000 : ℝ)] ![(8873154213471/20000000000000 : ℝ), (3162306952069/20000000000000 : ℝ), (7964538831669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420552261/10000000000 : ℝ)|^8309 ≤ (8873154213471/20000000000000 : ℝ)^6261
        have hw : |(5420552261/10000000000 : ℝ)|=(5420552261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2491211989/10000000000 : ℝ)|^8309 ≤ (3162306952069/20000000000000 : ℝ)^6261
        have hw : |(-2491211989/10000000000 : ℝ)|=(2491211989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1249195283/2500000000 : ℝ)|^8309 ≤ (7964538831669/20000000000000 : ℝ)^6261
        have hw : |(1249195283/2500000000 : ℝ)|=(1249195283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s1_2 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5420553677/10000000000 : ℝ)*x 0 + (999355963/2000000000 : ℝ)*x 1 + (-2491211817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420553677/10000000000 : ℝ)^8309 ≤ (44365786447939/100000000000000 : ℝ)^6261 := by
    have hnat : (5420553677 : ℕ)^8309*100000000000000^6261 ≤ 44365786447939^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420553677 10000000000 44365786447939 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999355963/2000000000 : ℝ)^8309 ≤ (19911340114493/50000000000000 : ℝ)^6261 := by
    have hnat : (999355963 : ℕ)^8309*50000000000000^6261 ≤ 19911340114493^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999355963 2000000000 19911340114493 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2491211817/10000000000 : ℝ)^8309 ≤ (15811533311583/100000000000000 : ℝ)^6261 := by
    have hnat : (2491211817 : ℕ)^8309*100000000000000^6261 ≤ 15811533311583^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491211817 10000000000 15811533311583 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420553677/10000000000 : ℝ), (999355963/2000000000 : ℝ), (-2491211817/10000000000 : ℝ)] ![(44365786447939/100000000000000 : ℝ), (19911340114493/50000000000000 : ℝ), (15811533311583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420553677/10000000000 : ℝ)|^8309 ≤ (44365786447939/100000000000000 : ℝ)^6261
        have hw : |(5420553677/10000000000 : ℝ)|=(5420553677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999355963/2000000000 : ℝ)|^8309 ≤ (19911340114493/50000000000000 : ℝ)^6261
        have hw : |(999355963/2000000000 : ℝ)|=(999355963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2491211817/10000000000 : ℝ)|^8309 ≤ (15811533311583/100000000000000 : ℝ)^6261
        have hw : |(-2491211817/10000000000 : ℝ)|=(2491211817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s1_3 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (172785299/400000000 : ℝ)*x 0 + (183606619/500000000 : ℝ)*x 1 + (5080885647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172785299/400000000 : ℝ)^8309 ≤ (32824632972087/100000000000000 : ℝ)^6261 := by
    have hnat : (172785299 : ℕ)^8309*100000000000000^6261 ≤ 32824632972087^6261*400000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172785299 400000000 32824632972087 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183606619/500000000 : ℝ)^8309 ≤ (26460694897499/100000000000000 : ℝ)^6261 := by
    have hnat : (183606619 : ℕ)^8309*100000000000000^6261 ≤ 26460694897499^6261*500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183606619 500000000 26460694897499 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080885647/10000000000 : ℝ)^8309 ≤ (1017866802773/2500000000000 : ℝ)^6261 := by
    have hnat : (5080885647 : ℕ)^8309*2500000000000^6261 ≤ 1017866802773^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080885647 10000000000 1017866802773 2500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172785299/400000000 : ℝ), (183606619/500000000 : ℝ), (5080885647/10000000000 : ℝ)] ![(32824632972087/100000000000000 : ℝ), (26460694897499/100000000000000 : ℝ), (1017866802773/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172785299/400000000 : ℝ)|^8309 ≤ (32824632972087/100000000000000 : ℝ)^6261
        have hw : |(172785299/400000000 : ℝ)|=(172785299/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183606619/500000000 : ℝ)|^8309 ≤ (26460694897499/100000000000000 : ℝ)^6261
        have hw : |(183606619/500000000 : ℝ)|=(183606619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080885647/10000000000 : ℝ)|^8309 ≤ (1017866802773/2500000000000 : ℝ)^6261
        have hw : |(5080885647/10000000000 : ℝ)|=(5080885647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s1_4 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107452351/10000000000 : ℝ)*x 0 + (5006596293/10000000000 : ℝ)*x 1 + (2849251077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107452351/10000000000 : ℝ)^8309 ≤ (2532713230061/20000000000000 : ℝ)^6261 := by
    have hnat : (2107452351 : ℕ)^8309*20000000000000^6261 ≤ 2532713230061^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107452351 10000000000 2532713230061 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5006596293/10000000000 : ℝ)^8309 ≤ (9981634588943/25000000000000 : ℝ)^6261 := by
    have hnat : (5006596293 : ℕ)^8309*25000000000000^6261 ≤ 9981634588943^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006596293 10000000000 9981634588943 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2849251077/5000000000 : ℝ)^8309 ≤ (5926236934931/12500000000000 : ℝ)^6261 := by
    have hnat : (2849251077 : ℕ)^8309*12500000000000^6261 ≤ 5926236934931^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2849251077 5000000000 5926236934931 12500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107452351/10000000000 : ℝ), (5006596293/10000000000 : ℝ), (2849251077/5000000000 : ℝ)] ![(2532713230061/20000000000000 : ℝ), (9981634588943/25000000000000 : ℝ), (5926236934931/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107452351/10000000000 : ℝ)|^8309 ≤ (2532713230061/20000000000000 : ℝ)^6261
        have hw : |(-2107452351/10000000000 : ℝ)|=(2107452351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5006596293/10000000000 : ℝ)|^8309 ≤ (9981634588943/25000000000000 : ℝ)^6261
        have hw : |(5006596293/10000000000 : ℝ)|=(5006596293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2849251077/5000000000 : ℝ)|^8309 ≤ (5926236934931/12500000000000 : ℝ)^6261
        have hw : |(2849251077/5000000000 : ℝ)|=(2849251077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s1_5 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5238316543/10000000000 : ℝ)*x 0 + (-447372649/2500000000 : ℝ)*x 1 + (712312743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238316543/10000000000 : ℝ)^8309 ≤ (5299661885553/12500000000000 : ℝ)^6261 := by
    have hnat : (5238316543 : ℕ)^8309*12500000000000^6261 ≤ 5299661885553^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238316543 10000000000 5299661885553 12500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447372649/2500000000 : ℝ)^8309 ≤ (10192811748691/100000000000000 : ℝ)^6261 := by
    have hnat : (447372649 : ℕ)^8309*100000000000000^6261 ≤ 10192811748691^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447372649 2500000000 10192811748691 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (712312743/1250000000 : ℝ)^8309 ≤ (11852473290203/25000000000000 : ℝ)^6261 := by
    have hnat : (712312743 : ℕ)^8309*25000000000000^6261 ≤ 11852473290203^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712312743 1250000000 11852473290203 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238316543/10000000000 : ℝ), (-447372649/2500000000 : ℝ), (712312743/1250000000 : ℝ)] ![(5299661885553/12500000000000 : ℝ), (10192811748691/100000000000000 : ℝ), (11852473290203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238316543/10000000000 : ℝ)|^8309 ≤ (5299661885553/12500000000000 : ℝ)^6261
        have hw : |(5238316543/10000000000 : ℝ)|=(5238316543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447372649/2500000000 : ℝ)|^8309 ≤ (10192811748691/100000000000000 : ℝ)^6261
        have hw : |(-447372649/2500000000 : ℝ)|=(447372649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(712312743/1250000000 : ℝ)|^8309 ≤ (11852473290203/25000000000000 : ℝ)^6261
        have hw : |(712312743/1250000000 : ℝ)|=(712312743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s1_6 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2619158287/5000000000 : ℝ)*x 0 + (5698502093/10000000000 : ℝ)*x 1 + (-1789490333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619158287/5000000000 : ℝ)^8309 ≤ (211986477087/500000000000 : ℝ)^6261 := by
    have hnat : (2619158287 : ℕ)^8309*500000000000^6261 ≤ 211986477087^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619158287 5000000000 211986477087 500000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5698502093/10000000000 : ℝ)^8309 ≤ (2370494740297/5000000000000 : ℝ)^6261 := by
    have hnat : (5698502093 : ℕ)^8309*5000000000000^6261 ≤ 2370494740297^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5698502093 10000000000 2370494740297 5000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1789490333/10000000000 : ℝ)^8309 ≤ (203856195213/2000000000000 : ℝ)^6261 := by
    have hnat : (1789490333 : ℕ)^8309*2000000000000^6261 ≤ 203856195213^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789490333 10000000000 203856195213 2000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619158287/5000000000 : ℝ), (5698502093/10000000000 : ℝ), (-1789490333/10000000000 : ℝ)] ![(211986477087/500000000000 : ℝ), (2370494740297/5000000000000 : ℝ), (203856195213/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619158287/5000000000 : ℝ)|^8309 ≤ (211986477087/500000000000 : ℝ)^6261
        have hw : |(2619158287/5000000000 : ℝ)|=(2619158287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5698502093/10000000000 : ℝ)|^8309 ≤ (2370494740297/5000000000000 : ℝ)^6261
        have hw : |(5698502093/10000000000 : ℝ)|=(5698502093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1789490333/10000000000 : ℝ)|^8309 ≤ (203856195213/2000000000000 : ℝ)^6261
        have hw : |(-1789490333/10000000000 : ℝ)|=(1789490333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s1_7 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2160649693/5000000000 : ℝ)*x 0 + (5061459181/10000000000 : ℝ)*x 1 + (1845973423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160649693/5000000000 : ℝ)^8309 ≤ (3284144414269/10000000000000 : ℝ)^6261 := by
    have hnat : (2160649693 : ℕ)^8309*10000000000000^6261 ≤ 3284144414269^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160649693 5000000000 3284144414269 10000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5061459181/10000000000 : ℝ)^8309 ≤ (40508210894403/100000000000000 : ℝ)^6261 := by
    have hnat : (5061459181 : ℕ)^8309*100000000000000^6261 ≤ 40508210894403^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5061459181 10000000000 40508210894403 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1845973423/5000000000 : ℝ)^8309 ≤ (13325172478279/50000000000000 : ℝ)^6261 := by
    have hnat : (1845973423 : ℕ)^8309*50000000000000^6261 ≤ 13325172478279^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845973423 5000000000 13325172478279 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160649693/5000000000 : ℝ), (5061459181/10000000000 : ℝ), (1845973423/5000000000 : ℝ)] ![(3284144414269/10000000000000 : ℝ), (40508210894403/100000000000000 : ℝ), (13325172478279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160649693/5000000000 : ℝ)|^8309 ≤ (3284144414269/10000000000000 : ℝ)^6261
        have hw : |(2160649693/5000000000 : ℝ)|=(2160649693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5061459181/10000000000 : ℝ)|^8309 ≤ (40508210894403/100000000000000 : ℝ)^6261
        have hw : |(5061459181/10000000000 : ℝ)|=(5061459181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1845973423/5000000000 : ℝ)|^8309 ≤ (13325172478279/50000000000000 : ℝ)^6261
        have hw : |(1845973423/5000000000 : ℝ)|=(1845973423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1116_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5583/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (153/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5503/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5139/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5583/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (153/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5583/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (153/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5583/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (153/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5583/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (153/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5583/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (153/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5583/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (153/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (153/50000 : ℝ) ^ (2077/512 : ℝ) ≤ (3158241969/50000000000000000000 : ℝ) := by
    have hpowers : (153/50000 : ℝ)^2077 ≤ (3158241969/50000000000000000000 : ℝ)^512 := by
      have hnat : (153 : ℕ)^2077*50000000000000000000^512 ≤ 3158241969^512*50000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        153 50000 3158241969 50000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (153/50000 : ℝ)) (X := (3158241969/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hpowhi : (5583/20000 : ℝ) ^ (2077/512 : ℝ) ≤ (564888099932295249/100000000000000000000 : ℝ) := by
    have hpowers : (5583/20000 : ℝ)^2077 ≤ (564888099932295249/100000000000000000000 : ℝ)^512 := by
      have hnat : (5583 : ℕ)^2077*100000000000000000000^512 ≤ 564888099932295249^512*20000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5583 20000 564888099932295249 100000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5583/20000 : ℝ)) (X := (564888099932295249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000003158241969/25000000000000000000 : ℝ) ≤ (2000000000062283/2000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (25000000003158241969/25000000000000000000 : ℝ)^512 ≤ (2000000000062283/2000000000000000 : ℝ)^2077 := by
      have hnat : (25000000003158241969 : ℕ)^512*2000000000000000^2077 ≤ 2000000000062283^2077*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000003158241969 25000000000000000000 2000000000062283 2000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000062283/2000000000000000 : ℝ)) (X := (25000000003158241969/25000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100564888106248779187/100000000000000000000 : ℝ) ≤ (10013895484550529/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (100564888106248779187/100000000000000000000 : ℝ)^512 ≤ (10013895484550529/10000000000000000 : ℝ)^2077 := by
      have hnat : (100564888106248779187 : ℕ)^512*10000000000000000^2077 ≤ 10013895484550529^2077*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100564888106248779187 100000000000000000000 10013895484550529 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013895484550529/10000000000000000 : ℝ)) (X := (100564888106248779187/100000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50564888099932295249/50000000000000000000 : ℝ) ≤ (10027790968789643/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (50564888099932295249/50000000000000000000 : ℝ)^512 ≤ (10027790968789643/10000000000000000 : ℝ)^2077 := by
      have hnat : (50564888099932295249 : ℕ)^512*10000000000000000^2077 ≤ 10027790968789643^2077*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50564888099932295249 50000000000000000000 10027790968789643 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027790968789643/10000000000000000 : ℝ)) (X := (50564888099932295249/50000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3158241969/50000000000000000000 : ℝ) ≤ ((92027165324081172989/92030000000000000000 : ℝ)+2*(6947742119557/1380450000000000 : ℝ)*(153/50000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (92027165324081172989/92030000000000000000 : ℝ)+2*(6947742119557/1380450000000000 : ℝ)*(153/50000 : ℝ)=(2000000000062283/2000000000000000 : ℝ) by norm_num, show 1+2*(3158241969/50000000000000000000 : ℝ)=(25000000003158241969/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(564888099932295249/100000000000000000000 : ℝ)+(3158241969/50000000000000000000 : ℝ) ≤ ((92027165324081172989/92030000000000000000 : ℝ)+(6947742119557/1380450000000000 : ℝ)*((5583/20000 : ℝ)+(153/50000 : ℝ)))^(2077/512 : ℝ) := by
    rw [show (92027165324081172989/92030000000000000000 : ℝ)+(6947742119557/1380450000000000 : ℝ)*((5583/20000 : ℝ)+(153/50000 : ℝ))=(10013895484550529/10000000000000000 : ℝ) by norm_num, show 1+(564888099932295249/100000000000000000000 : ℝ)+(3158241969/50000000000000000000 : ℝ)=(100564888106248779187/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(564888099932295249/100000000000000000000 : ℝ) ≤ ((92027165324081172989/92030000000000000000 : ℝ)+2*(6947742119557/1380450000000000 : ℝ)*(5583/20000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (92027165324081172989/92030000000000000000 : ℝ)+2*(6947742119557/1380450000000000 : ℝ)*(5583/20000 : ℝ)=(10027790968789643/10000000000000000 : ℝ) by norm_num, show 1+2*(564888099932295249/100000000000000000000 : ℝ)=(50564888099932295249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92027165324081172989/92030000000000000000 : ℝ)*(X 1 0+X 2 0)+(6947742119557/1380450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (153/50000 : ℝ)) (hi := (5583/20000 : ℝ)) (c := (92027165324081172989/92030000000000000000 : ℝ)) (alpha := (6947742119557/1380450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92027165324081172989/92030000000000000000 : ℝ)*(X 0 1+X 2 1)+(6947742119557/1380450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (153/50000 : ℝ)) (hi := (5583/20000 : ℝ)) (c := (92027165324081172989/92030000000000000000 : ℝ)) (alpha := (6947742119557/1380450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92027165324081172989/92030000000000000000 : ℝ)*(X 0 2+X 1 2)+(6947742119557/1380450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (153/50000 : ℝ)) (hi := (5583/20000 : ℝ)) (c := (92027165324081172989/92030000000000000000 : ℝ)) (alpha := (6947742119557/1380450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526652303/2500000000 : ℝ)*X 0 0+(5708513291/10000000000 : ℝ)*X 0 1+(999356253/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5420552261/10000000000 : ℝ)*X 1 0+(-2491211989/10000000000 : ℝ)*X 1 1+(1249195283/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5420553677/10000000000 : ℝ)*X 2 0+(999355963/2000000000 : ℝ)*X 2 1+(-2491211817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172785299/400000000 : ℝ)*X 0 0+(183606619/500000000 : ℝ)*X 0 1+(5080885647/10000000000 : ℝ)*X 0 2+(172785299/400000000 : ℝ)*X 1 0+(183606619/500000000 : ℝ)*X 1 1+(5080885647/10000000000 : ℝ)*X 1 2+(172785299/400000000 : ℝ)*X 2 0+(183606619/500000000 : ℝ)*X 2 1+(5080885647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2107452351/10000000000 : ℝ)*X 0 0+(5006596293/10000000000 : ℝ)*X 0 1+(2849251077/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5238316543/10000000000 : ℝ)*X 1 0+(-447372649/2500000000 : ℝ)*X 1 1+(712312743/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2619158287/5000000000 : ℝ)*X 2 0+(5698502093/10000000000 : ℝ)*X 2 1+(-1789490333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160649693/5000000000 : ℝ)*X 0 0+(5061459181/10000000000 : ℝ)*X 0 1+(1845973423/5000000000 : ℝ)*X 0 2+(2160649693/5000000000 : ℝ)*X 1 0+(5061459181/10000000000 : ℝ)*X 1 1+(1845973423/5000000000 : ℝ)*X 1 2+(2160649693/5000000000 : ℝ)*X 2 0+(5061459181/10000000000 : ℝ)*X 2 1+(1845973423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (166392088923757566005027/46015000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16294419/6250000000000 : ℝ)*(base1) + (103036643/20000000000000 : ℝ)*(base19) + (22207037/2500000000000 : ℝ)*(base23) + (3277289/50000000000000 : ℝ)*(base24) + (80261793/100000000000000 : ℝ)*(upper5) + (1057436528313197/100000000000000 : ℝ)*(major0) + (1057436528313197/100000000000000 : ℝ)*(major1) + (1057436528313197/100000000000000 : ℝ)*(major2) + (702511769503179/50000000000000 : ℝ)*(sp0) + (1405024313574531/100000000000000 : ℝ)*(sp1) + (1405024309334687/100000000000000 : ℝ)*(sp2) + (354923735605133/50000000000000 : ℝ)*(sp3) + (481468773/25000000000000 : ℝ)*(sp4) + (375413/100000000000 : ℝ)*(sp5) + (709847731920971/100000000000000 : ℝ)*(f.failure) + (702512602085373/50000000000000 : ℝ)*(f.sum) + (5371100577487/2156953125000000000000000000 : ℝ)*base65 + (64156209091405707499/27609000000000000000000000000000000 : ℝ)*base67 + (46678241953528292501/27609000000000000000000000000000000 : ℝ)*base70 + (57228436020337292501/27609000000000000000000000000000000 : ℝ)*base72 + (582742809108013/138045000000000000000000000000 : ℝ)*base73 + (96710997154414292501/27609000000000000000000000000000000 : ℝ)*base76 + (6819736424290707499/27609000000000000000000000000000000 : ℝ)*base77 + (5729911568866707499/27609000000000000000000000000000000 : ℝ)*base79 + (134738196298577/138045000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5303657/1000000000000000000000 : ℝ)*base89 + (5303657/1000000000000000000000 : ℝ)*base91 + (5303657/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5946117807023184971545095081/1150375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2543677/4000000000000 : ℝ)*(base1) + (290186039/25000000000000 : ℝ)*(base19) + (118746487/10000000000000 : ℝ)*(base23) + (111431861/100000000000000 : ℝ)*(upper3) + (28737049/25000000000000 : ℝ)*(upper5) + (543867634811457/50000000000000 : ℝ)*(major0) + (543867634811457/50000000000000 : ℝ)*(major1) + (543867634811457/50000000000000 : ℝ)*(major2) + (572295247/12500000000000 : ℝ)*(sp1) + (2550273459/50000000000000 : ℝ)*(sp2) + (722641711596021/50000000000000 : ℝ)*(sp4) + (289055524098797/20000000000000 : ℝ)*(sp5) + (180659633948541/12500000000000 : ℝ)*(sp6) + (730186943758721/100000000000000 : ℝ)*(sp7) + (730187007350647/100000000000000 : ℝ)*(f.failure) + (361320839900029/25000000000000 : ℝ)*(f.sum) + (697561503049/359492187500000000000000000 : ℝ)*base65 + (21889860718142234973/4601500000000000000000000000000000 : ℝ)*base67 + (29424657632001734973/4601500000000000000000000000000000 : ℝ)*base69 + (26707175255507234973/4601500000000000000000000000000000 : ℝ)*base71 + (58125703928077/46015000000000000000000000000 : ℝ)*base73 + (16651014084204265027/4601500000000000000000000000000000 : ℝ)*base76 + (45101468271056734973/4601500000000000000000000000000000 : ℝ)*base77 + (42316239629790234973/4601500000000000000000000000000000 : ℝ)*base79 + (5840244396423/11503750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (593549/1000000000000000000000 : ℝ)*base89 + (593549/1000000000000000000000 : ℝ)*base91 + (593549/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1116_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5583/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (153/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5503/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5139/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1116_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1116_s2_0 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2161250389/10000000000 : ℝ)*x 0 + (2757912759/5000000000 : ℝ)*x 1 + (5154750507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161250389/10000000000 : ℝ)^8309 ≤ (654717973579/5000000000000 : ℝ)^6261 := by
    have hnat : (2161250389 : ℕ)^8309*5000000000000^6261 ≤ 654717973579^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161250389 10000000000 654717973579 5000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757912759/5000000000 : ℝ)^8309 ≤ (22701795901261/50000000000000 : ℝ)^6261 := by
    have hnat : (2757912759 : ℕ)^8309*50000000000000^6261 ≤ 22701795901261^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757912759 5000000000 22701795901261 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5154750507/10000000000 : ℝ)^8309 ≤ (20751024358361/50000000000000 : ℝ)^6261 := by
    have hnat : (5154750507 : ℕ)^8309*50000000000000^6261 ≤ 20751024358361^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5154750507 10000000000 20751024358361 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2161250389/10000000000 : ℝ), (2757912759/5000000000 : ℝ), (5154750507/10000000000 : ℝ)] ![(654717973579/5000000000000 : ℝ), (22701795901261/50000000000000 : ℝ), (20751024358361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2161250389/10000000000 : ℝ)|^8309 ≤ (654717973579/5000000000000 : ℝ)^6261
        have hw : |(-2161250389/10000000000 : ℝ)|=(2161250389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757912759/5000000000 : ℝ)|^8309 ≤ (22701795901261/50000000000000 : ℝ)^6261
        have hw : |(2757912759/5000000000 : ℝ)|=(2757912759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5154750507/10000000000 : ℝ)|^8309 ≤ (20751024358361/50000000000000 : ℝ)^6261
        have hw : |(5154750507/10000000000 : ℝ)|=(5154750507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s2_1 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2687494643/5000000000 : ℝ)*x 0 + (-293645867/1250000000 : ℝ)*x 1 + (1030950377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687494643/5000000000 : ℝ)^8309 ≤ (21935773985867/50000000000000 : ℝ)^6261 := by
    have hnat : (2687494643 : ℕ)^8309*50000000000000^6261 ≤ 21935773985867^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687494643 5000000000 21935773985867 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293645867/1250000000 : ℝ)^8309 ≤ (3656597142003/25000000000000 : ℝ)^6261 := by
    have hnat : (293645867 : ℕ)^8309*25000000000000^6261 ≤ 3656597142003^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293645867 1250000000 3656597142003 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030950377/2000000000 : ℝ)^8309 ≤ (8300412688079/20000000000000 : ℝ)^6261 := by
    have hnat : (1030950377 : ℕ)^8309*20000000000000^6261 ≤ 8300412688079^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030950377 2000000000 8300412688079 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687494643/5000000000 : ℝ), (-293645867/1250000000 : ℝ), (1030950377/2000000000 : ℝ)] ![(21935773985867/50000000000000 : ℝ), (3656597142003/25000000000000 : ℝ), (8300412688079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687494643/5000000000 : ℝ)|^8309 ≤ (21935773985867/50000000000000 : ℝ)^6261
        have hw : |(2687494643/5000000000 : ℝ)|=(2687494643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-293645867/1250000000 : ℝ)|^8309 ≤ (3656597142003/25000000000000 : ℝ)^6261
        have hw : |(-293645867/1250000000 : ℝ)|=(293645867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030950377/2000000000 : ℝ)|^8309 ≤ (8300412688079/20000000000000 : ℝ)^6261
        have hw : |(1030950377/2000000000 : ℝ)|=(1030950377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s2_2 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374989219/10000000000 : ℝ)*x 0 + (1030950389/2000000000 : ℝ)*x 1 + (-2349166947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374989219/10000000000 : ℝ)^8309 ≤ (43871547245987/100000000000000 : ℝ)^6261 := by
    have hnat : (5374989219 : ℕ)^8309*100000000000000^6261 ≤ 43871547245987^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374989219 10000000000 43871547245987 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030950389/2000000000 : ℝ)^8309 ≤ (10375516020371/25000000000000 : ℝ)^6261 := by
    have hnat : (1030950389 : ℕ)^8309*25000000000000^6261 ≤ 10375516020371^6261*2000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030950389 2000000000 10375516020371 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2349166947/10000000000 : ℝ)^8309 ≤ (14626388658903/100000000000000 : ℝ)^6261 := by
    have hnat : (2349166947 : ℕ)^8309*100000000000000^6261 ≤ 14626388658903^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2349166947 10000000000 14626388658903 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374989219/10000000000 : ℝ), (1030950389/2000000000 : ℝ), (-2349166947/10000000000 : ℝ)] ![(43871547245987/100000000000000 : ℝ), (10375516020371/25000000000000 : ℝ), (14626388658903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374989219/10000000000 : ℝ)|^8309 ≤ (43871547245987/100000000000000 : ℝ)^6261
        have hw : |(5374989219/10000000000 : ℝ)|=(5374989219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030950389/2000000000 : ℝ)|^8309 ≤ (10375516020371/25000000000000 : ℝ)^6261
        have hw : |(1030950389/2000000000 : ℝ)|=(1030950389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2349166947/10000000000 : ℝ)|^8309 ≤ (14626388658903/100000000000000 : ℝ)^6261
        have hw : |(-2349166947/10000000000 : ℝ)|=(2349166947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s2_3 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357051407/10000000000 : ℝ)*x 0 + (4014318063/10000000000 : ℝ)*x 1 + (4729002627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357051407/10000000000 : ℝ)^8309 ≤ (33202521055459/100000000000000 : ℝ)^6261 := by
    have hnat : (4357051407 : ℕ)^8309*100000000000000^6261 ≤ 33202521055459^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357051407 10000000000 33202521055459 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4014318063/10000000000 : ℝ)^8309 ≤ (2978183750031/10000000000000 : ℝ)^6261 := by
    have hnat : (4014318063 : ℕ)^8309*10000000000000^6261 ≤ 2978183750031^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014318063 10000000000 2978183750031 10000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4729002627/10000000000 : ℝ)^8309 ≤ (37015641426437/100000000000000 : ℝ)^6261 := by
    have hnat : (4729002627 : ℕ)^8309*100000000000000^6261 ≤ 37015641426437^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4729002627 10000000000 37015641426437 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357051407/10000000000 : ℝ), (4014318063/10000000000 : ℝ), (4729002627/10000000000 : ℝ)] ![(33202521055459/100000000000000 : ℝ), (2978183750031/10000000000000 : ℝ), (37015641426437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357051407/10000000000 : ℝ)|^8309 ≤ (33202521055459/100000000000000 : ℝ)^6261
        have hw : |(4357051407/10000000000 : ℝ)|=(4357051407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4014318063/10000000000 : ℝ)|^8309 ≤ (2978183750031/10000000000000 : ℝ)^6261
        have hw : |(4014318063/10000000000 : ℝ)|=(4014318063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4729002627/10000000000 : ℝ)|^8309 ≤ (37015641426437/100000000000000 : ℝ)^6261
        have hw : |(4729002627/10000000000 : ℝ)|=(4729002627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s2_4 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-54034003/250000000 : ℝ)*x 0 + (5157286467/10000000000 : ℝ)*x 1 + (275663197/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54034003/250000000 : ℝ)^8309 ≤ (13095241773397/100000000000000 : ℝ)^6261 := by
    have hnat : (54034003 : ℕ)^8309*100000000000000^6261 ≤ 13095241773397^6261*250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54034003 250000000 13095241773397 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5157286467/10000000000 : ℝ)^8309 ≤ (10382286789007/25000000000000 : ℝ)^6261 := by
    have hnat : (5157286467 : ℕ)^8309*25000000000000^6261 ≤ 10382286789007^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157286467 10000000000 10382286789007 25000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275663197/500000000 : ℝ)^8309 ≤ (45375611053283/100000000000000 : ℝ)^6261 := by
    have hnat : (275663197 : ℕ)^8309*100000000000000^6261 ≤ 45375611053283^6261*500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275663197 500000000 45375611053283 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54034003/250000000 : ℝ), (5157286467/10000000000 : ℝ), (275663197/500000000 : ℝ)] ![(13095241773397/100000000000000 : ℝ), (10382286789007/25000000000000 : ℝ), (45375611053283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54034003/250000000 : ℝ)|^8309 ≤ (13095241773397/100000000000000 : ℝ)^6261
        have hw : |(-54034003/250000000 : ℝ)|=(54034003/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5157286467/10000000000 : ℝ)|^8309 ≤ (10382286789007/25000000000000 : ℝ)^6261
        have hw : |(5157286467/10000000000 : ℝ)|=(5157286467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275663197/500000000 : ℝ)|^8309 ≤ (45375611053283/100000000000000 : ℝ)^6261
        have hw : |(275663197/500000000 : ℝ)|=(275663197/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s2_5 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5283534983/10000000000 : ℝ)*x 0 + (-248831777/1250000000 : ℝ)*x 1 + (2756632011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283534983/10000000000 : ℝ)^8309 ≤ (42883678294729/100000000000000 : ℝ)^6261 := by
    have hnat : (5283534983 : ℕ)^8309*100000000000000^6261 ≤ 42883678294729^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283534983 10000000000 42883678294729 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248831777/1250000000 : ℝ)^8309 ≤ (5870354872937/50000000000000 : ℝ)^6261 := by
    have hnat : (248831777 : ℕ)^8309*50000000000000^6261 ≤ 5870354872937^6261*1250000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248831777 1250000000 5870354872937 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2756632011/5000000000 : ℝ)^8309 ≤ (45375611948921/100000000000000 : ℝ)^6261 := by
    have hnat : (2756632011 : ℕ)^8309*100000000000000^6261 ≤ 45375611948921^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756632011 5000000000 45375611948921 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283534983/10000000000 : ℝ), (-248831777/1250000000 : ℝ), (2756632011/5000000000 : ℝ)] ![(42883678294729/100000000000000 : ℝ), (5870354872937/50000000000000 : ℝ), (45375611948921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283534983/10000000000 : ℝ)|^8309 ≤ (42883678294729/100000000000000 : ℝ)^6261
        have hw : |(5283534983/10000000000 : ℝ)|=(5283534983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248831777/1250000000 : ℝ)|^8309 ≤ (5870354872937/50000000000000 : ℝ)^6261
        have hw : |(-248831777/1250000000 : ℝ)|=(248831777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2756632011/5000000000 : ℝ)|^8309 ≤ (45375611948921/100000000000000 : ℝ)^6261
        have hw : |(2756632011/5000000000 : ℝ)|=(2756632011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s2_6 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20638809/39062500 : ℝ)*x 0 + (220530559/400000000 : ℝ)*x 1 + (-995327057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20638809/39062500 : ℝ)^8309 ≤ (42883679598069/100000000000000 : ℝ)^6261 := by
    have hnat : (20638809 : ℕ)^8309*100000000000000^6261 ≤ 42883679598069^6261*39062500^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20638809 39062500 42883679598069 100000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220530559/400000000 : ℝ)^8309 ≤ (2835975714723/6250000000000 : ℝ)^6261 := by
    have hnat : (220530559 : ℕ)^8309*6250000000000^6261 ≤ 2835975714723^6261*400000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220530559 400000000 2835975714723 6250000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995327057/5000000000 : ℝ)^8309 ≤ (2348141789501/20000000000000 : ℝ)^6261 := by
    have hnat : (995327057 : ℕ)^8309*20000000000000^6261 ≤ 2348141789501^6261*5000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995327057 5000000000 2348141789501 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20638809/39062500 : ℝ), (220530559/400000000 : ℝ), (-995327057/5000000000 : ℝ)] ![(42883679598069/100000000000000 : ℝ), (2835975714723/6250000000000 : ℝ), (2348141789501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20638809/39062500 : ℝ)|^8309 ≤ (42883679598069/100000000000000 : ℝ)^6261
        have hw : |(20638809/39062500 : ℝ)|=(20638809/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220530559/400000000 : ℝ)|^8309 ≤ (2835975714723/6250000000000 : ℝ)^6261
        have hw : |(220530559/400000000 : ℝ)|=(220530559/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-995327057/5000000000 : ℝ)|^8309 ≤ (2348141789501/20000000000000 : ℝ)^6261
        have hw : |(-995327057/5000000000 : ℝ)|=(995327057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1116_s2_7 (p : ℝ) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357270017/10000000000 : ℝ)*x 0 + (4723984503/10000000000 : ℝ)*x 1 + (1004846489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357270017/10000000000 : ℝ)^8309 ≤ (6640946378793/20000000000000 : ℝ)^6261 := by
    have hnat : (4357270017 : ℕ)^8309*20000000000000^6261 ≤ 6640946378793^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357270017 10000000000 6640946378793 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4723984503/10000000000 : ℝ)^8309 ≤ (7392704708577/20000000000000 : ℝ)^6261 := by
    have hnat : (4723984503 : ℕ)^8309*20000000000000^6261 ≤ 7392704708577^6261*10000000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4723984503 10000000000 7392704708577 20000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004846489/2500000000 : ℝ)^8309 ≤ (14915872271699/50000000000000 : ℝ)^6261 := by
    have hnat : (1004846489 : ℕ)^8309*50000000000000^6261 ≤ 14915872271699^6261*2500000000^8309 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004846489 2500000000 14915872271699 50000000000000 8309 6261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8309/2048 : ℝ)) 8309 6261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357270017/10000000000 : ℝ), (4723984503/10000000000 : ℝ), (1004846489/2500000000 : ℝ)] ![(6640946378793/20000000000000 : ℝ), (7392704708577/20000000000000 : ℝ), (14915872271699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357270017/10000000000 : ℝ)|^8309 ≤ (6640946378793/20000000000000 : ℝ)^6261
        have hw : |(4357270017/10000000000 : ℝ)|=(4357270017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4723984503/10000000000 : ℝ)|^8309 ≤ (7392704708577/20000000000000 : ℝ)^6261
        have hw : |(4723984503/10000000000 : ℝ)|=(4723984503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004846489/2500000000 : ℝ)|^8309 ≤ (14915872271699/50000000000000 : ℝ)^6261
        have hw : |(1004846489/2500000000 : ℝ)|=(1004846489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1116_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5139/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8951/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16581/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5139/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5139/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5503/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5139/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5139/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5503/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5139/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5139/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5503/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5503/100000 : ℝ) ^ (2077/512 : ℝ) ≤ (389076342688169/50000000000000000000 : ℝ) := by
    have hpowers : (5503/100000 : ℝ)^2077 ≤ (389076342688169/50000000000000000000 : ℝ)^512 := by
      have hnat : (5503 : ℕ)^2077*50000000000000000000^512 ≤ 389076342688169^512*100000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5503 100000 389076342688169 50000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5503/100000 : ℝ)) (X := (389076342688169/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hpowhi : (5139/25000 : ℝ) ^ (2077/512 : ℝ) ≤ (81622304770150461/50000000000000000000 : ℝ) := by
    have hpowers : (5139/25000 : ℝ)^2077 ≤ (81622304770150461/50000000000000000000 : ℝ)^512 := by
      have hnat : (5139 : ℕ)^2077*50000000000000000000^512 ≤ 81622304770150461^512*25000^2077 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5139 25000 81622304770150461 50000000000000000000 2077 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5139/25000 : ℝ)) (X := (81622304770150461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000389076342688169/25000000000000000000 : ℝ) ≤ (10000038364163593/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (25000389076342688169/25000000000000000000 : ℝ)^512 ≤ (10000038364163593/10000000000000000 : ℝ)^2077 := by
      have hnat : (25000389076342688169 : ℕ)^512*10000000000000000^2077 ≤ 10000038364163593^2077*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000389076342688169 25000000000000000000 10000038364163593 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000038364163593/10000000000000000 : ℝ)) (X := (25000389076342688169/25000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5008201138111283863/5000000000000000000 : ℝ) ≤ (10004040818916297/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (5008201138111283863/5000000000000000000 : ℝ)^512 ≤ (10004040818916297/10000000000000000 : ℝ)^2077 := by
      have hnat : (5008201138111283863 : ℕ)^512*10000000000000000^2077 ≤ 10004040818916297^2077*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5008201138111283863 5000000000000000000 10004040818916297 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004040818916297/10000000000000000 : ℝ)) (X := (5008201138111283863/5000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25081622304770150461/25000000000000000000 : ℝ) ≤ (10008043273669001/10000000000000000 : ℝ) ^ (2077/512 : ℝ) := by
    have hpowers : (25081622304770150461/25000000000000000000 : ℝ)^512 ≤ (10008043273669001/10000000000000000 : ℝ)^2077 := by
      have hnat : (25081622304770150461 : ℕ)^512*10000000000000000^2077 ≤ 10008043273669001^2077*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25081622304770150461 25000000000000000000 10008043273669001 10000000000000000 512 2077 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008043273669001/10000000000000000 : ℝ)) (X := (25081622304770150461/25000000000000000000 : ℝ)) (by norm_num) 2077 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(389076342688169/50000000000000000000 : ℝ) ≤ ((30097305295749261041/30106000000000000000 : ℝ)+2*(62538355511/23520312500000 : ℝ)*(5503/100000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (30097305295749261041/30106000000000000000 : ℝ)+2*(62538355511/23520312500000 : ℝ)*(5503/100000 : ℝ)=(10000038364163593/10000000000000000 : ℝ) by norm_num, show 1+2*(389076342688169/50000000000000000000 : ℝ)=(25000389076342688169/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(81622304770150461/50000000000000000000 : ℝ)+(389076342688169/50000000000000000000 : ℝ) ≤ ((30097305295749261041/30106000000000000000 : ℝ)+(62538355511/23520312500000 : ℝ)*((5139/25000 : ℝ)+(5503/100000 : ℝ)))^(2077/512 : ℝ) := by
    rw [show (30097305295749261041/30106000000000000000 : ℝ)+(62538355511/23520312500000 : ℝ)*((5139/25000 : ℝ)+(5503/100000 : ℝ))=(10004040818916297/10000000000000000 : ℝ) by norm_num, show 1+(81622304770150461/50000000000000000000 : ℝ)+(389076342688169/50000000000000000000 : ℝ)=(5008201138111283863/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(81622304770150461/50000000000000000000 : ℝ) ≤ ((30097305295749261041/30106000000000000000 : ℝ)+2*(62538355511/23520312500000 : ℝ)*(5139/25000 : ℝ))^(2077/512 : ℝ) := by
    rw [show (30097305295749261041/30106000000000000000 : ℝ)+2*(62538355511/23520312500000 : ℝ)*(5139/25000 : ℝ)=(10008043273669001/10000000000000000 : ℝ) by norm_num, show 1+2*(81622304770150461/50000000000000000000 : ℝ)=(25081622304770150461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30097305295749261041/30106000000000000000 : ℝ)*(X 1 0+X 2 0)+(62538355511/23520312500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (5503/100000 : ℝ)) (hi := (5139/25000 : ℝ)) (c := (30097305295749261041/30106000000000000000 : ℝ)) (alpha := (62538355511/23520312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30097305295749261041/30106000000000000000 : ℝ)*(X 0 1+X 2 1)+(62538355511/23520312500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (5503/100000 : ℝ)) (hi := (5139/25000 : ℝ)) (c := (30097305295749261041/30106000000000000000 : ℝ)) (alpha := (62538355511/23520312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30097305295749261041/30106000000000000000 : ℝ)*(X 0 2+X 1 2)+(62538355511/23520312500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2077/512 : ℝ)) (lo := (5503/100000 : ℝ)) (hi := (5139/25000 : ℝ)) (c := (30097305295749261041/30106000000000000000 : ℝ)) (alpha := (62538355511/23520312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2161250389/10000000000 : ℝ)*X 0 0+(2757912759/5000000000 : ℝ)*X 0 1+(5154750507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687494643/5000000000 : ℝ)*X 1 0+(-293645867/1250000000 : ℝ)*X 1 1+(1030950377/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374989219/10000000000 : ℝ)*X 2 0+(1030950389/2000000000 : ℝ)*X 2 1+(-2349166947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357051407/10000000000 : ℝ)*X 0 0+(4014318063/10000000000 : ℝ)*X 0 1+(4729002627/10000000000 : ℝ)*X 0 2+(4357051407/10000000000 : ℝ)*X 1 0+(4014318063/10000000000 : ℝ)*X 1 1+(4729002627/10000000000 : ℝ)*X 1 2+(4357051407/10000000000 : ℝ)*X 2 0+(4014318063/10000000000 : ℝ)*X 2 1+(4729002627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-54034003/250000000 : ℝ)*X 0 0+(5157286467/10000000000 : ℝ)*X 0 1+(275663197/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5283534983/10000000000 : ℝ)*X 1 0+(-248831777/1250000000 : ℝ)*X 1 1+(2756632011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20638809/39062500 : ℝ)*X 2 0+(220530559/400000000 : ℝ)*X 2 1+(-995327057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357270017/10000000000 : ℝ)*X 0 0+(4723984503/10000000000 : ℝ)*X 0 1+(1004846489/2500000000 : ℝ)*X 0 2+(4357270017/10000000000 : ℝ)*X 1 0+(4723984503/10000000000 : ℝ)*X 1 1+(1004846489/2500000000 : ℝ)*X 1 2+(4357270017/10000000000 : ℝ)*X 2 0+(4723984503/10000000000 : ℝ)*X 2 1+(1004846489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1116_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5399180756561586858664961781/752650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (344418117/50000000000000 : ℝ)*(base19) + (50633729/12500000000000 : ℝ)*(base23) + (1287019/20000000000000 : ℝ)*(upper2) + (205231461/100000000000000 : ℝ)*(upper3) + (1096901/781250000000 : ℝ)*(upper4) + (1042191586745047/50000000000000 : ℝ)*(major0) + (1042191586745047/50000000000000 : ℝ)*(major1) + (1042191586745047/50000000000000 : ℝ)*(major2) + (2769524001129947/100000000000000 : ℝ)*(sp0) + (2769537542420303/100000000000000 : ℝ)*(sp1) + (173096114136669/6250000000000 : ℝ)*(sp2) + (1399222296208027/100000000000000 : ℝ)*(sp3) + (1423012659/10000000000000 : ℝ)*(sp4) + (5580396917/100000000000000 : ℝ)*(sp7) + (87451742287809/6250000000000 : ℝ)*(f.failure) + (2769538231256537/100000000000000 : ℝ)*(f.sum) + (290896426130499/75265000000000000000000000000 : ℝ)*base66 + (8046317728489826073/1505300000000000000000000000000000 : ℝ)*base68 + (6628277383384426073/1505300000000000000000000000000000 : ℝ)*base70 + (4949326731107773927/1505300000000000000000000000000000 : ℝ)*base71 + (3261979276999/4704062500000000000000000000 : ℝ)*base74 + (8431963106542226073/1505300000000000000000000000000000 : ℝ)*base76 + (3824460420362373927/1505300000000000000000000000000000 : ℝ)*base77 + (1387915513771026073/1505300000000000000000000000000000 : ℝ)*base80 + (79538795912469/75265000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (82603/62500000000000000000 : ℝ)*base89 + (82603/62500000000000000000 : ℝ)*base91 + (82603/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5638856539266041710795545879/1505300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191433423/25000000000000 : ℝ)*(base19) + (918135541/100000000000000 : ℝ)*(base23) + (23208183/20000000000000 : ℝ)*(upper3) + (6649223/25000000000000 : ℝ)*(lower4) + (7646883/12500000000000 : ℝ)*(upper5) + (2114207073412627/100000000000000 : ℝ)*(major0) + (2114207073412627/100000000000000 : ℝ)*(major1) + (2114207073412627/100000000000000 : ℝ)*(major2) + (436803087/6250000000000 : ℝ)*(sp1) + (9168564959/100000000000000 : ℝ)*(sp2) + (351145703340221/12500000000000 : ℝ)*(sp4) + (561831574427737/20000000000000 : ℝ)*(sp5) + (702288885005317/25000000000000 : ℝ)*(sp6) + (1419248395236751/100000000000000 : ℝ)*(sp7) + (1419248395236751/100000000000000 : ℝ)*(f.failure) + (351145703340221/12500000000000 : ℝ)*(f.sum) + (176595350722447/75265000000000000000000000000 : ℝ)*base66 + (27187181262061324707/3010600000000000000000000000000000 : ℝ)*base67 + (18894990947511124707/3010600000000000000000000000000000 : ℝ)*base69 + (14644331486883675293/3010600000000000000000000000000000 : ℝ)*base72 + (494744494384943/75265000000000000000000000000 : ℝ)*base73 + (16240364082630875293/3010600000000000000000000000000000 : ℝ)*base76 + (21428565038400724707/3010600000000000000000000000000000 : ℝ)*base77 + (11587450584931924707/3010600000000000000000000000000000 : ℝ)*base79 + (25878064677193/75265000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4191083/1000000000000000000000 : ℝ)*base90 + (4191083/1000000000000000000000 : ℝ)*base92 + (4191083/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1116_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5139/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5503/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1116_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1116_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1116_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1116_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1116_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2077/512 : ℝ) ≤ p) (hpb : p ≤ (8309/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14896667/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16581/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1116_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

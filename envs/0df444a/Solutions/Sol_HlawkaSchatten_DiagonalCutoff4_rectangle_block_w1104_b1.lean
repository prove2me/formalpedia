-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1104_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:02:27.679994+00:00
-- url     : https://prove2.me/submissions/2ee96ded-a54e-4912-aab3-4a6b48fc80d8

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
theorem support_rectangle_w1104_s3_0 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090472271/5000000000 : ℝ)*x 0 + (271661421/500000000 : ℝ)*x 1 + (5228369573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090472271/5000000000 : ℝ)^8297 ≤ (6620137607151/50000000000000 : ℝ)^6249 := by
    have hnat : (1090472271 : ℕ)^8297*50000000000000^6249 ≤ 6620137607151^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090472271 5000000000 6620137607151 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271661421/500000000 : ℝ)^8297 ≤ (44486461661731/100000000000000 : ℝ)^6249 := by
    have hnat : (271661421 : ℕ)^8297*100000000000000^6249 ≤ 44486461661731^6249*500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271661421 500000000 44486461661731 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228369573/10000000000 : ℝ)^8297 ≤ (42273263106253/100000000000000 : ℝ)^6249 := by
    have hnat : (5228369573 : ℕ)^8297*100000000000000^6249 ≤ 42273263106253^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228369573 10000000000 42273263106253 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090472271/5000000000 : ℝ), (271661421/500000000 : ℝ), (5228369573/10000000000 : ℝ)] ![(6620137607151/50000000000000 : ℝ), (44486461661731/100000000000000 : ℝ), (42273263106253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090472271/5000000000 : ℝ)|^8297 ≤ (6620137607151/50000000000000 : ℝ)^6249
        have hw : |(-1090472271/5000000000 : ℝ)|=(1090472271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271661421/500000000 : ℝ)|^8297 ≤ (44486461661731/100000000000000 : ℝ)^6249
        have hw : |(271661421/500000000 : ℝ)|=(271661421/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228369573/10000000000 : ℝ)|^8297 ≤ (42273263106253/100000000000000 : ℝ)^6249
        have hw : |(5228369573/10000000000 : ℝ)|=(5228369573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s3_1 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338681749/2500000000 : ℝ)*x 0 + (-2285751669/10000000000 : ℝ)*x 1 + (5228369699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338681749/2500000000 : ℝ)^8297 ≤ (43635078243967/100000000000000 : ℝ)^6249 := by
    have hnat : (1338681749 : ℕ)^8297*100000000000000^6249 ≤ 43635078243967^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338681749 2500000000 43635078243967 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2285751669/10000000000 : ℝ)^8297 ≤ (2818331457439/20000000000000 : ℝ)^6249 := by
    have hnat : (2285751669 : ℕ)^8297*20000000000000^6249 ≤ 2818331457439^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285751669 10000000000 2818331457439 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228369699/10000000000 : ℝ)^8297 ≤ (5284158057361/12500000000000 : ℝ)^6249 := by
    have hnat : (5228369699 : ℕ)^8297*12500000000000^6249 ≤ 5284158057361^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228369699 10000000000 5284158057361 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338681749/2500000000 : ℝ), (-2285751669/10000000000 : ℝ), (5228369699/10000000000 : ℝ)] ![(43635078243967/100000000000000 : ℝ), (2818331457439/20000000000000 : ℝ), (5284158057361/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338681749/2500000000 : ℝ)|^8297 ≤ (43635078243967/100000000000000 : ℝ)^6249
        have hw : |(1338681749/2500000000 : ℝ)|=(1338681749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2285751669/10000000000 : ℝ)|^8297 ≤ (2818331457439/20000000000000 : ℝ)^6249
        have hw : |(-2285751669/10000000000 : ℝ)|=(2285751669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228369699/10000000000 : ℝ)|^8297 ≤ (5284158057361/12500000000000 : ℝ)^6249
        have hw : |(5228369699/10000000000 : ℝ)|=(5228369699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s3_2 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070945427/2000000000 : ℝ)*x 0 + (1045673959/2000000000 : ℝ)*x 1 + (-2285751359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070945427/2000000000 : ℝ)^8297 ≤ (43635079747883/100000000000000 : ℝ)^6249 := by
    have hnat : (1070945427 : ℕ)^8297*100000000000000^6249 ≤ 43635079747883^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070945427 2000000000 43635079747883 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045673959/2000000000 : ℝ)^8297 ≤ (42273265489467/100000000000000 : ℝ)^6249 := by
    have hnat : (1045673959 : ℕ)^8297*100000000000000^6249 ≤ 42273265489467^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045673959 2000000000 42273265489467 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285751359/10000000000 : ℝ)^8297 ≤ (140916547497/1000000000000 : ℝ)^6249 := by
    have hnat : (2285751359 : ℕ)^8297*1000000000000^6249 ≤ 140916547497^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285751359 10000000000 140916547497 1000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070945427/2000000000 : ℝ), (1045673959/2000000000 : ℝ), (-2285751359/10000000000 : ℝ)] ![(43635079747883/100000000000000 : ℝ), (42273265489467/100000000000000 : ℝ), (140916547497/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070945427/2000000000 : ℝ)|^8297 ≤ (43635079747883/100000000000000 : ℝ)^6249
        have hw : |(1070945427/2000000000 : ℝ)|=(1070945427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045673959/2000000000 : ℝ)|^8297 ≤ (42273265489467/100000000000000 : ℝ)^6249
        have hw : |(1045673959/2000000000 : ℝ)|=(1045673959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2285751359/10000000000 : ℝ)|^8297 ≤ (140916547497/1000000000000 : ℝ)^6249
        have hw : |(-2285751359/10000000000 : ℝ)|=(2285751359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s3_3 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183769599/5000000000 : ℝ)*x 0 + (2084985919/5000000000 : ℝ)*x 1 + (4574496687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183769599/5000000000 : ℝ)^8297 ≤ (33291299266429/100000000000000 : ℝ)^6249 := by
    have hnat : (2183769599 : ℕ)^8297*100000000000000^6249 ≤ 33291299266429^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183769599 5000000000 33291299266429 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084985919/5000000000 : ℝ)^8297 ≤ (31306781647083/100000000000000 : ℝ)^6249 := by
    have hnat : (2084985919 : ℕ)^8297*100000000000000^6249 ≤ 31306781647083^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084985919 5000000000 31306781647083 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4574496687/10000000000 : ℝ)^8297 ≤ (35401919075819/100000000000000 : ℝ)^6249 := by
    have hnat : (4574496687 : ℕ)^8297*100000000000000^6249 ≤ 35401919075819^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574496687 10000000000 35401919075819 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183769599/5000000000 : ℝ), (2084985919/5000000000 : ℝ), (4574496687/10000000000 : ℝ)] ![(33291299266429/100000000000000 : ℝ), (31306781647083/100000000000000 : ℝ), (35401919075819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183769599/5000000000 : ℝ)|^8297 ≤ (33291299266429/100000000000000 : ℝ)^6249
        have hw : |(2183769599/5000000000 : ℝ)|=(2183769599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084985919/5000000000 : ℝ)|^8297 ≤ (31306781647083/100000000000000 : ℝ)^6249
        have hw : |(2084985919/5000000000 : ℝ)|=(2084985919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4574496687/10000000000 : ℝ)|^8297 ≤ (35401919075819/100000000000000 : ℝ)^6249
        have hw : |(4574496687/10000000000 : ℝ)|=(4574496687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s3_4 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-436192907/2000000000 : ℝ)*x 0 + (1307296613/2500000000 : ℝ)*x 1 + (2716203451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436192907/2000000000 : ℝ)^8297 ≤ (6620218184241/50000000000000 : ℝ)^6249 := by
    have hnat : (436192907 : ℕ)^8297*50000000000000^6249 ≤ 6620218184241^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436192907 2000000000 6620218184241 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307296613/2500000000 : ℝ)^8297 ≤ (2114101634429/5000000000000 : ℝ)^6249 := by
    have hnat : (1307296613 : ℕ)^8297*5000000000000^6249 ≤ 2114101634429^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307296613 2500000000 2114101634429 5000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716203451/5000000000 : ℝ)^8297 ≤ (44477530935247/100000000000000 : ℝ)^6249 := by
    have hnat : (2716203451 : ℕ)^8297*100000000000000^6249 ≤ 44477530935247^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716203451 5000000000 44477530935247 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436192907/2000000000 : ℝ), (1307296613/2500000000 : ℝ), (2716203451/5000000000 : ℝ)] ![(6620218184241/50000000000000 : ℝ), (2114101634429/5000000000000 : ℝ), (44477530935247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436192907/2000000000 : ℝ)|^8297 ≤ (6620218184241/50000000000000 : ℝ)^6249
        have hw : |(-436192907/2000000000 : ℝ)|=(436192907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307296613/2500000000 : ℝ)|^8297 ≤ (2114101634429/5000000000000 : ℝ)^6249
        have hw : |(1307296613/2500000000 : ℝ)|=(1307296613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716203451/5000000000 : ℝ)|^8297 ≤ (44477530935247/100000000000000 : ℝ)^6249
        have hw : |(2716203451/5000000000 : ℝ)|=(2716203451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s3_5 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2651486549/5000000000 : ℝ)*x 0 + (-52042857/250000000 : ℝ)*x 1 + (2716203559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651486549/5000000000 : ℝ)^8297 ≤ (21538006698493/50000000000000 : ℝ)^6249 := by
    have hnat : (2651486549 : ℕ)^8297*50000000000000^6249 ≤ 21538006698493^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651486549 5000000000 21538006698493 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52042857/250000000 : ℝ)^8297 ≤ (2489290662197/20000000000000 : ℝ)^6249 := by
    have hnat : (52042857 : ℕ)^8297*20000000000000^6249 ≤ 2489290662197^6249*250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52042857 250000000 2489290662197 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716203559/5000000000 : ℝ)^8297 ≤ (22238766641663/50000000000000 : ℝ)^6249 := by
    have hnat : (2716203559 : ℕ)^8297*50000000000000^6249 ≤ 22238766641663^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716203559 5000000000 22238766641663 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651486549/5000000000 : ℝ), (-52042857/250000000 : ℝ), (2716203559/5000000000 : ℝ)] ![(21538006698493/50000000000000 : ℝ), (2489290662197/20000000000000 : ℝ), (22238766641663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651486549/5000000000 : ℝ)|^8297 ≤ (21538006698493/50000000000000 : ℝ)^6249
        have hw : |(2651486549/5000000000 : ℝ)|=(2651486549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52042857/250000000 : ℝ)|^8297 ≤ (2489290662197/20000000000000 : ℝ)^6249
        have hw : |(-52042857/250000000 : ℝ)|=(52042857/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716203559/5000000000 : ℝ)|^8297 ≤ (22238766641663/50000000000000 : ℝ)^6249
        have hw : |(2716203559/5000000000 : ℝ)|=(2716203559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s3_6 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212118927/400000000 : ℝ)*x 0 + (5432406919/10000000000 : ℝ)*x 1 + (-130107153/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212118927/400000000 : ℝ)^8297 ≤ (43076014227443/100000000000000 : ℝ)^6249 := by
    have hnat : (212118927 : ℕ)^8297*100000000000000^6249 ≤ 43076014227443^6249*400000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212118927 400000000 43076014227443 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432406919/10000000000 : ℝ)^8297 ≤ (44477531120049/100000000000000 : ℝ)^6249 := by
    have hnat : (5432406919 : ℕ)^8297*100000000000000^6249 ≤ 44477531120049^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432406919 10000000000 44477531120049 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130107153/625000000 : ℝ)^8297 ≤ (6223227322321/50000000000000 : ℝ)^6249 := by
    have hnat : (130107153 : ℕ)^8297*50000000000000^6249 ≤ 6223227322321^6249*625000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130107153 625000000 6223227322321 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212118927/400000000 : ℝ), (5432406919/10000000000 : ℝ), (-130107153/625000000 : ℝ)] ![(43076014227443/100000000000000 : ℝ), (44477531120049/100000000000000 : ℝ), (6223227322321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212118927/400000000 : ℝ)|^8297 ≤ (43076014227443/100000000000000 : ℝ)^6249
        have hw : |(212118927/400000000 : ℝ)|=(212118927/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432406919/10000000000 : ℝ)|^8297 ≤ (44477531120049/100000000000000 : ℝ)^6249
        have hw : |(5432406919/10000000000 : ℝ)|=(5432406919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130107153/625000000 : ℝ)|^8297 ≤ (6223227322321/50000000000000 : ℝ)^6249
        have hw : |(-130107153/625000000 : ℝ)|=(130107153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s3_7 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183789309/5000000000 : ℝ)*x 0 + (4572884551/10000000000 : ℝ)*x 1 + (4171593419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183789309/5000000000 : ℝ)^8297 ≤ (33291698219453/100000000000000 : ℝ)^6249 := by
    have hnat : (2183789309 : ℕ)^8297*100000000000000^6249 ≤ 33291698219453^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183789309 5000000000 33291698219453 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4572884551/10000000000 : ℝ)^8297 ≤ (8846338717233/25000000000000 : ℝ)^6249 := by
    have hnat : (4572884551 : ℕ)^8297*25000000000000^6249 ≤ 8846338717233^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572884551 10000000000 8846338717233 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171593419/10000000000 : ℝ)^8297 ≤ (31322946888167/100000000000000 : ℝ)^6249 := by
    have hnat : (4171593419 : ℕ)^8297*100000000000000^6249 ≤ 31322946888167^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171593419 10000000000 31322946888167 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183789309/5000000000 : ℝ), (4572884551/10000000000 : ℝ), (4171593419/10000000000 : ℝ)] ![(33291698219453/100000000000000 : ℝ), (8846338717233/25000000000000 : ℝ), (31322946888167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183789309/5000000000 : ℝ)|^8297 ≤ (33291698219453/100000000000000 : ℝ)^6249
        have hw : |(2183789309/5000000000 : ℝ)|=(2183789309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4572884551/10000000000 : ℝ)|^8297 ≤ (8846338717233/25000000000000 : ℝ)^6249
        have hw : |(4572884551/10000000000 : ℝ)|=(4572884551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171593419/10000000000 : ℝ)|^8297 ≤ (31322946888167/100000000000000 : ℝ)^6249
        have hw : |(4171593419/10000000000 : ℝ)|=(4171593419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1104_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16619/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1779/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10519/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14853/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16619/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1779/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16619/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1779/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16619/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1779/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16619/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1779/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16619/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1779/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16619/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1779/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1779/20000 : ℝ) ^ (1037/256 : ℝ) ≤ (346019157946421/6250000000000000000 : ℝ) := by
    have hpowers : (1779/20000 : ℝ)^1037 ≤ (346019157946421/6250000000000000000 : ℝ)^256 := by
      have hnat : (1779 : ℕ)^1037*6250000000000000000^256 ≤ 346019157946421^256*20000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1779 20000 346019157946421 6250000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1779/20000 : ℝ)) (X := (346019157946421/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16619/100000 : ℝ) ^ (1037/256 : ℝ) ≤ (17409283674988741/25000000000000000000 : ℝ) := by
    have hpowers : (16619/100000 : ℝ)^1037 ≤ (17409283674988741/25000000000000000000 : ℝ)^256 := by
      have hnat : (16619 : ℕ)^1037*25000000000000000000^256 ≤ 17409283674988741^256*100000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16619 100000 17409283674988741 25000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16619/100000 : ℝ)) (X := (17409283674988741/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125346019157946421/3125000000000000000 : ℝ) ≤ (2500068333431993/2500000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (3125346019157946421/3125000000000000000 : ℝ)^256 ≤ (2500068333431993/2500000000000000 : ℝ)^1037 := by
      have hnat : (3125346019157946421 : ℕ)^256*2500000000000000^1037 ≤ 2500068333431993^1037*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125346019157946421 3125000000000000000 2500068333431993 2500000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500068333431993/2500000000000000 : ℝ)) (X := (3125346019157946421/3125000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000751734412270977/1000000000000000000 : ℝ) ≤ (156278988301097/156250000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (1000751734412270977/1000000000000000000 : ℝ)^256 ≤ (156278988301097/156250000000000 : ℝ)^1037 := by
      have hnat : (1000751734412270977 : ℕ)^256*156250000000000^1037 ≤ 156278988301097^1037*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000751734412270977 1000000000000000000 156278988301097 156250000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156278988301097/156250000000000 : ℝ)) (X := (1000751734412270977/1000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12517409283674988741/12500000000000000000 : ℝ) ≤ (2500859292203111/2500000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (12517409283674988741/12500000000000000000 : ℝ)^256 ≤ (2500859292203111/2500000000000000 : ℝ)^1037 := by
      have hnat : (12517409283674988741 : ℕ)^256*2500000000000000^1037 ≤ 2500859292203111^1037*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12517409283674988741 12500000000000000000 2500859292203111 2500000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500859292203111/2500000000000000 : ℝ)) (X := (12517409283674988741/12500000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(346019157946421/6250000000000000000 : ℝ) ≤ ((9651746114579809661/9655000000000000000 : ℝ)+2*(395479385559/193100000000000 : ℝ)*(1779/20000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (9651746114579809661/9655000000000000000 : ℝ)+2*(395479385559/193100000000000 : ℝ)*(1779/20000 : ℝ)=(2500068333431993/2500000000000000 : ℝ) by norm_num, show 1+2*(346019157946421/6250000000000000000 : ℝ)=(3125346019157946421/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17409283674988741/25000000000000000000 : ℝ)+(346019157946421/6250000000000000000 : ℝ) ≤ ((9651746114579809661/9655000000000000000 : ℝ)+(395479385559/193100000000000 : ℝ)*((16619/100000 : ℝ)+(1779/20000 : ℝ)))^(1037/256 : ℝ) := by
    rw [show (9651746114579809661/9655000000000000000 : ℝ)+(395479385559/193100000000000 : ℝ)*((16619/100000 : ℝ)+(1779/20000 : ℝ))=(156278988301097/156250000000000 : ℝ) by norm_num, show 1+(17409283674988741/25000000000000000000 : ℝ)+(346019157946421/6250000000000000000 : ℝ)=(1000751734412270977/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17409283674988741/25000000000000000000 : ℝ) ≤ ((9651746114579809661/9655000000000000000 : ℝ)+2*(395479385559/193100000000000 : ℝ)*(16619/100000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (9651746114579809661/9655000000000000000 : ℝ)+2*(395479385559/193100000000000 : ℝ)*(16619/100000 : ℝ)=(2500859292203111/2500000000000000 : ℝ) by norm_num, show 1+2*(17409283674988741/25000000000000000000 : ℝ)=(12517409283674988741/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9651746114579809661/9655000000000000000 : ℝ)*(X 1 0+X 2 0)+(395479385559/193100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (1779/20000 : ℝ)) (hi := (16619/100000 : ℝ)) (c := (9651746114579809661/9655000000000000000 : ℝ)) (alpha := (395479385559/193100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9651746114579809661/9655000000000000000 : ℝ)*(X 0 1+X 2 1)+(395479385559/193100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (1779/20000 : ℝ)) (hi := (16619/100000 : ℝ)) (c := (9651746114579809661/9655000000000000000 : ℝ)) (alpha := (395479385559/193100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9651746114579809661/9655000000000000000 : ℝ)*(X 0 2+X 1 2)+(395479385559/193100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (1779/20000 : ℝ)) (hi := (16619/100000 : ℝ)) (c := (9651746114579809661/9655000000000000000 : ℝ)) (alpha := (395479385559/193100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1090472271/5000000000 : ℝ)*X 0 0+(271661421/500000000 : ℝ)*X 0 1+(5228369573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338681749/2500000000 : ℝ)*X 1 0+(-2285751669/10000000000 : ℝ)*X 1 1+(5228369699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070945427/2000000000 : ℝ)*X 2 0+(1045673959/2000000000 : ℝ)*X 2 1+(-2285751359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183769599/5000000000 : ℝ)*X 0 0+(2084985919/5000000000 : ℝ)*X 0 1+(4574496687/10000000000 : ℝ)*X 0 2+(2183769599/5000000000 : ℝ)*X 1 0+(2084985919/5000000000 : ℝ)*X 1 1+(4574496687/10000000000 : ℝ)*X 1 2+(2183769599/5000000000 : ℝ)*X 2 0+(2084985919/5000000000 : ℝ)*X 2 1+(4574496687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-436192907/2000000000 : ℝ)*X 0 0+(1307296613/2500000000 : ℝ)*X 0 1+(2716203451/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651486549/5000000000 : ℝ)*X 1 0+(-52042857/250000000 : ℝ)*X 1 1+(2716203559/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212118927/400000000 : ℝ)*X 2 0+(5432406919/10000000000 : ℝ)*X 2 1+(-130107153/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183789309/5000000000 : ℝ)*X 0 0+(4572884551/10000000000 : ℝ)*X 0 1+(4171593419/10000000000 : ℝ)*X 0 2+(2183789309/5000000000 : ℝ)*X 1 0+(4572884551/10000000000 : ℝ)*X 1 1+(4171593419/10000000000 : ℝ)*X 1 2+(2183789309/5000000000 : ℝ)*X 2 0+(4572884551/10000000000 : ℝ)*X 2 1+(4171593419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16021376103671620853097/4827500000000000000000000000 : ℝ) := by norm_num
    linear_combination (290869659/25000000000000 : ℝ)*(base19) + (1092726217/100000000000000 : ℝ)*(base23) + (52869139/50000000000000 : ℝ)*(lower2) + (7693421/100000000000000 : ℝ)*(upper3) + (98388631/50000000000000 : ℝ)*(upper5) + (459594786295061/12500000000000 : ℝ)*(major0) + (459594786295061/12500000000000 : ℝ)*(major1) + (459594786295061/12500000000000 : ℝ)*(major2) + (4881430898691157/100000000000000 : ℝ)*(sp0) + (1220364895452163/25000000000000 : ℝ)*(sp1) + (4881459652561071/100000000000000 : ℝ)*(sp2) + (2472046504974479/100000000000000 : ℝ)*(sp3) + (29846596131/100000000000000 : ℝ)*(sp4) + (9219833441/100000000000000 : ℝ)*(sp7) + (30900696560099/1250000000000 : ℝ)*(f.failure) + (610182593160911/12500000000000 : ℝ)*(f.sum) + (50965573812863/9655000000000000000000000000 : ℝ)*base66 + (156793585117853179/120687500000000000000000000000000 : ℝ)*base68 + (1132746748861521821/120687500000000000000000000000000 : ℝ)*base69 + (623621310638915679/120687500000000000000000000000000 : ℝ)*base72 + (48866266853517/9655000000000000000000000000 : ℝ)*base73 + (686326869494334321/120687500000000000000000000000000 : ℝ)*base75 + (594365718431603179/120687500000000000000000000000000 : ℝ)*base78 + (1478117580708209321/120687500000000000000000000000000 : ℝ)*base79 + (20336918238027/9655000000000000000000000000 : ℝ)*base81 + (1303/15625000000000000000 : ℝ)*base90 + (1303/15625000000000000000 : ℝ)*base92 + (1303/15625000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28221513739565901636057/9655000000000000000000000000 : ℝ) := by norm_num
    linear_combination (492375457/100000000000000 : ℝ)*(base19) + (747655123/100000000000000 : ℝ)*(base23) + (104957531/100000000000000 : ℝ)*(upper3) + (88762263/100000000000000 : ℝ)*(lower4) + (231647436707269/6250000000000 : ℝ)*(major0) + (231647436707269/6250000000000 : ℝ)*(major1) + (231647436707269/6250000000000 : ℝ)*(major2) + (44350287/400000000000 : ℝ)*(sp1) + (12772842231/100000000000000 : ℝ)*(sp2) + (119429067/100000000000000 : ℝ)*(sp3) + (4920760226132253/100000000000000 : ℝ)*(sp4) + (2460374323092523/50000000000000 : ℝ)*(sp5) + (4920746705634899/100000000000000 : ℝ)*(sp6) + (2491957531638127/100000000000000 : ℝ)*(sp7) + (1245978825533597/50000000000000 : ℝ)*(f.failure) + (4920760226132253/100000000000000 : ℝ)*(f.sum) + (212179225901/9655000000000000000000000000 : ℝ)*base65 + (40208672672230441/60343750000000000000000000000000 : ℝ)*base68 + (115612770760925809/60343750000000000000000000000000 : ℝ)*base69 + (630013380699300809/60343750000000000000000000000000 : ℝ)*base71 + (6738398270979/9655000000000000000000000000 : ℝ)*base74 + (407081803033824191/60343750000000000000000000000000 : ℝ)*base76 + (400091664015136691/60343750000000000000000000000000 : ℝ)*base78 + (277896877028707059/60343750000000000000000000000000 : ℝ)*base79 + (32514573217481/9655000000000000000000000000 : ℝ)*base81 + (1414009/625000000000000000000 : ℝ)*base90 + (1414009/625000000000000000000 : ℝ)*base92 + (1414009/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1104_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16619/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1779/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10519/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14853/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1104_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1104_s4_0 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-87370829/400000000 : ℝ)*x 0 + (5403778599/10000000000 : ℝ)*x 1 + (1313911199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87370829/400000000 : ℝ)^8297 ≤ (6633546335281/50000000000000 : ℝ)^6249 := by
    have hnat : (87370829 : ℕ)^8297*50000000000000^6249 ≤ 6633546335281^6249*400000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87370829 400000000 6633546335281 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403778599/10000000000 : ℝ)^8297 ≤ (2760411830149/6250000000000 : ℝ)^6249 := by
    have hnat : (5403778599 : ℕ)^8297*6250000000000^6249 ≤ 2760411830149^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403778599 10000000000 2760411830149 6250000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313911199/2500000000 : ℝ)^8297 ≤ (10641579509803/25000000000000 : ℝ)^6249 := by
    have hnat : (1313911199 : ℕ)^8297*25000000000000^6249 ≤ 10641579509803^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313911199 2500000000 10641579509803 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87370829/400000000 : ℝ), (5403778599/10000000000 : ℝ), (1313911199/2500000000 : ℝ)] ![(6633546335281/50000000000000 : ℝ), (2760411830149/6250000000000 : ℝ), (10641579509803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87370829/400000000 : ℝ)|^8297 ≤ (6633546335281/50000000000000 : ℝ)^6249
        have hw : |(-87370829/400000000 : ℝ)|=(87370829/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403778599/10000000000 : ℝ)|^8297 ≤ (2760411830149/6250000000000 : ℝ)^6249
        have hw : |(5403778599/10000000000 : ℝ)|=(5403778599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313911199/2500000000 : ℝ)|^8297 ≤ (10641579509803/25000000000000 : ℝ)^6249
        have hw : |(1313911199/2500000000 : ℝ)|=(1313911199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s4_1 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673700211/5000000000 : ℝ)*x 0 + (-2259582893/10000000000 : ℝ)*x 1 + (1313911191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673700211/5000000000 : ℝ)^8297 ≤ (4355582582667/10000000000000 : ℝ)^6249 := by
    have hnat : (2673700211 : ℕ)^8297*10000000000000^6249 ≤ 4355582582667^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673700211 5000000000 4355582582667 10000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259582893/10000000000 : ℝ)^8297 ≤ (13877856462759/100000000000000 : ℝ)^6249 := by
    have hnat : (2259582893 : ℕ)^8297*100000000000000^6249 ≤ 13877856462759^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259582893 10000000000 13877856462759 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313911191/2500000000 : ℝ)^8297 ≤ (425663176951/1000000000000 : ℝ)^6249 := by
    have hnat : (1313911191 : ℕ)^8297*1000000000000^6249 ≤ 425663176951^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313911191 2500000000 425663176951 1000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673700211/5000000000 : ℝ), (-2259582893/10000000000 : ℝ), (1313911191/2500000000 : ℝ)] ![(4355582582667/10000000000000 : ℝ), (13877856462759/100000000000000 : ℝ), (425663176951/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673700211/5000000000 : ℝ)|^8297 ≤ (4355582582667/10000000000000 : ℝ)^6249
        have hw : |(2673700211/5000000000 : ℝ)|=(2673700211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2259582893/10000000000 : ℝ)|^8297 ≤ (13877856462759/100000000000000 : ℝ)^6249
        have hw : |(-2259582893/10000000000 : ℝ)|=(2259582893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313911191/2500000000 : ℝ)|^8297 ≤ (425663176951/1000000000000 : ℝ)^6249
        have hw : |(1313911191/2500000000 : ℝ)|=(1313911191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s4_2 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668425109/1250000000 : ℝ)*x 0 + (1313911147/2500000000 : ℝ)*x 1 + (-2259582529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668425109/1250000000 : ℝ)^8297 ≤ (43555830693281/100000000000000 : ℝ)^6249 := by
    have hnat : (668425109 : ℕ)^8297*100000000000000^6249 ≤ 43555830693281^6249*1250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668425109 1250000000 43555830693281 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313911147/2500000000 : ℝ)^8297 ≤ (532078947531/1250000000000 : ℝ)^6249 := by
    have hnat : (1313911147 : ℕ)^8297*1250000000000^6249 ≤ 532078947531^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313911147 2500000000 532078947531 1250000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259582529/10000000000 : ℝ)^8297 ≤ (13877853494471/100000000000000 : ℝ)^6249 := by
    have hnat : (2259582529 : ℕ)^8297*100000000000000^6249 ≤ 13877853494471^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259582529 10000000000 13877853494471 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668425109/1250000000 : ℝ), (1313911147/2500000000 : ℝ), (-2259582529/10000000000 : ℝ)] ![(43555830693281/100000000000000 : ℝ), (532078947531/1250000000000 : ℝ), (13877853494471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668425109/1250000000 : ℝ)|^8297 ≤ (43555830693281/100000000000000 : ℝ)^6249
        have hw : |(668425109/1250000000 : ℝ)|=(668425109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313911147/2500000000 : ℝ)|^8297 ≤ (532078947531/1250000000000 : ℝ)^6249
        have hw : |(1313911147/2500000000 : ℝ)|=(1313911147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2259582529/10000000000 : ℝ)|^8297 ≤ (13877853494471/100000000000000 : ℝ)^6249
        have hw : |(-2259582529/10000000000 : ℝ)|=(2259582529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s4_3 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184759847/5000000000 : ℝ)*x 0 + (2112859557/5000000000 : ℝ)*x 1 + (2259116471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184759847/5000000000 : ℝ)^8297 ≤ (33311344482171/100000000000000 : ℝ)^6249 := by
    have hnat : (2184759847 : ℕ)^8297*100000000000000^6249 ≤ 33311344482171^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184759847 5000000000 33311344482171 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112859557/5000000000 : ℝ)^8297 ≤ (15931847129119/50000000000000 : ℝ)^6249 := by
    have hnat : (2112859557 : ℕ)^8297*50000000000000^6249 ≤ 15931847129119^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112859557 5000000000 15931847129119 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259116471/5000000000 : ℝ)^8297 ≤ (17412480622869/50000000000000 : ℝ)^6249 := by
    have hnat : (2259116471 : ℕ)^8297*50000000000000^6249 ≤ 17412480622869^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259116471 5000000000 17412480622869 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184759847/5000000000 : ℝ), (2112859557/5000000000 : ℝ), (2259116471/5000000000 : ℝ)] ![(33311344482171/100000000000000 : ℝ), (15931847129119/50000000000000 : ℝ), (17412480622869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184759847/5000000000 : ℝ)|^8297 ≤ (33311344482171/100000000000000 : ℝ)^6249
        have hw : |(2184759847/5000000000 : ℝ)|=(2184759847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112859557/5000000000 : ℝ)|^8297 ≤ (15931847129119/50000000000000 : ℝ)^6249
        have hw : |(2112859557/5000000000 : ℝ)|=(2112859557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259116471/5000000000 : ℝ)|^8297 ≤ (17412480622869/50000000000000 : ℝ)^6249
        have hw : |(2259116471/5000000000 : ℝ)|=(2259116471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s4_4 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-136517449/625000000 : ℝ)*x 0 + (5256072059/10000000000 : ℝ)*x 1 + (337709307/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136517449/625000000 : ℝ)^8297 ≤ (1326716088859/10000000000000 : ℝ)^6249 := by
    have hnat : (136517449 : ℕ)^8297*10000000000000^6249 ≤ 1326716088859^6249*625000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136517449 625000000 1326716088859 10000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256072059/10000000000 : ℝ)^8297 ≤ (2660682042601/6250000000000 : ℝ)^6249 := by
    have hnat : (5256072059 : ℕ)^8297*6250000000000^6249 ≤ 2660682042601^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256072059 10000000000 2660682042601 6250000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337709307/625000000 : ℝ)^8297 ≤ (44161926411/100000000000 : ℝ)^6249 := by
    have hnat : (337709307 : ℕ)^8297*100000000000^6249 ≤ 44161926411^6249*625000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337709307 625000000 44161926411 100000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136517449/625000000 : ℝ), (5256072059/10000000000 : ℝ), (337709307/625000000 : ℝ)] ![(1326716088859/10000000000000 : ℝ), (2660682042601/6250000000000 : ℝ), (44161926411/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136517449/625000000 : ℝ)|^8297 ≤ (1326716088859/10000000000000 : ℝ)^6249
        have hw : |(-136517449/625000000 : ℝ)|=(136517449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256072059/10000000000 : ℝ)|^8297 ≤ (2660682042601/6250000000000 : ℝ)^6249
        have hw : |(5256072059/10000000000 : ℝ)|=(5256072059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337709307/625000000 : ℝ)|^8297 ≤ (44161926411/100000000000 : ℝ)^6249
        have hw : |(337709307/625000000 : ℝ)|=(337709307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s4_5 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (21239919/40000000 : ℝ)*x 0 + (-1055939063/5000000000 : ℝ)*x 1 + (1080669821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21239919/40000000 : ℝ)^8297 ≤ (21575798812731/50000000000000 : ℝ)^6249 := by
    have hnat : (21239919 : ℕ)^8297*50000000000000^6249 ≤ 21575798812731^6249*40000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21239919 40000000 21575798812731 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055939063/5000000000 : ℝ)^8297 ≤ (634323692927/5000000000000 : ℝ)^6249 := by
    have hnat : (1055939063 : ℕ)^8297*5000000000000^6249 ≤ 634323692927^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055939063 5000000000 634323692927 5000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080669821/2000000000 : ℝ)^8297 ≤ (44161928505367/100000000000000 : ℝ)^6249 := by
    have hnat : (1080669821 : ℕ)^8297*100000000000000^6249 ≤ 44161928505367^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080669821 2000000000 44161928505367 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21239919/40000000 : ℝ), (-1055939063/5000000000 : ℝ), (1080669821/2000000000 : ℝ)] ![(21575798812731/50000000000000 : ℝ), (634323692927/5000000000000 : ℝ), (44161928505367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21239919/40000000 : ℝ)|^8297 ≤ (21575798812731/50000000000000 : ℝ)^6249
        have hw : |(21239919/40000000 : ℝ)|=(21239919/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1055939063/5000000000 : ℝ)|^8297 ≤ (634323692927/5000000000000 : ℝ)^6249
        have hw : |(-1055939063/5000000000 : ℝ)|=(1055939063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080669821/2000000000 : ℝ)|^8297 ≤ (44161928505367/100000000000000 : ℝ)^6249
        have hw : |(1080669821/2000000000 : ℝ)|=(1080669821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s4_6 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309979947/10000000000 : ℝ)*x 0 + (216133957/400000000 : ℝ)*x 1 + (-263984763/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309979947/10000000000 : ℝ)^8297 ≤ (43151599751059/100000000000000 : ℝ)^6249 := by
    have hnat : (5309979947 : ℕ)^8297*100000000000000^6249 ≤ 43151599751059^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309979947 10000000000 43151599751059 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216133957/400000000 : ℝ)^8297 ≤ (44161926552071/100000000000000 : ℝ)^6249 := by
    have hnat : (216133957 : ℕ)^8297*100000000000000^6249 ≤ 44161926552071^6249*400000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216133957 400000000 44161926552071 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263984763/1250000000 : ℝ)^8297 ≤ (12686473683069/100000000000000 : ℝ)^6249 := by
    have hnat : (263984763 : ℕ)^8297*100000000000000^6249 ≤ 12686473683069^6249*1250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263984763 1250000000 12686473683069 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309979947/10000000000 : ℝ), (216133957/400000000 : ℝ), (-263984763/1250000000 : ℝ)] ![(43151599751059/100000000000000 : ℝ), (44161926552071/100000000000000 : ℝ), (12686473683069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309979947/10000000000 : ℝ)|^8297 ≤ (43151599751059/100000000000000 : ℝ)^6249
        have hw : |(5309979947/10000000000 : ℝ)|=(5309979947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216133957/400000000 : ℝ)|^8297 ≤ (44161926552071/100000000000000 : ℝ)^6249
        have hw : |(216133957/400000000 : ℝ)|=(216133957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263984763/1250000000 : ℝ)|^8297 ≤ (12686473683069/100000000000000 : ℝ)^6249
        have hw : |(-263984763/1250000000 : ℝ)|=(263984763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s4_7 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184767313/5000000000 : ℝ)*x 0 + (4517388083/10000000000 : ℝ)*x 1 + (2113283779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184767313/5000000000 : ℝ)^8297 ≤ (33311495624897/100000000000000 : ℝ)^6249 := by
    have hnat : (2184767313 : ℕ)^8297*100000000000000^6249 ≤ 33311495624897^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184767313 5000000000 33311495624897 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517388083/10000000000 : ℝ)^8297 ≤ (6963263095791/20000000000000 : ℝ)^6249 := by
    have hnat : (4517388083 : ℕ)^8297*20000000000000^6249 ≤ 6963263095791^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517388083 10000000000 6963263095791 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113283779/5000000000 : ℝ)^8297 ≤ (7968047217509/25000000000000 : ℝ)^6249 := by
    have hnat : (2113283779 : ℕ)^8297*25000000000000^6249 ≤ 7968047217509^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113283779 5000000000 7968047217509 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184767313/5000000000 : ℝ), (4517388083/10000000000 : ℝ), (2113283779/5000000000 : ℝ)] ![(33311495624897/100000000000000 : ℝ), (6963263095791/20000000000000 : ℝ), (7968047217509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184767313/5000000000 : ℝ)|^8297 ≤ (33311495624897/100000000000000 : ℝ)^6249
        have hw : |(2184767313/5000000000 : ℝ)|=(2184767313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517388083/10000000000 : ℝ)|^8297 ≤ (6963263095791/20000000000000 : ℝ)^6249
        have hw : |(4517388083/10000000000 : ℝ)|=(4517388083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113283779/5000000000 : ℝ)|^8297 ≤ (7968047217509/25000000000000 : ℝ)^6249
        have hw : |(2113283779/5000000000 : ℝ)|=(2113283779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1104_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10519/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10519/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14853/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10519/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10519/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14853/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10519/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10519/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14853/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10519/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10519/100000 : ℝ) ^ (1037/256 : ℝ) ≤ (546012348935883/5000000000000000000 : ℝ) := by
    have hpowers : (10519/100000 : ℝ)^1037 ≤ (546012348935883/5000000000000000000 : ℝ)^256 := by
      have hnat : (10519 : ℕ)^1037*5000000000000000000^256 ≤ 546012348935883^256*100000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10519 100000 546012348935883 5000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10519/100000 : ℝ)) (X := (546012348935883/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14853/100000 : ℝ) ^ (1037/256 : ℝ) ≤ (22088713254502607/50000000000000000000 : ℝ) := by
    have hpowers : (14853/100000 : ℝ)^1037 ≤ (22088713254502607/50000000000000000000 : ℝ)^256 := by
      have hnat : (14853 : ℕ)^1037*50000000000000000000^256 ≤ 22088713254502607^256*100000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14853 100000 22088713254502607 50000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14853/100000 : ℝ)) (X := (22088713254502607/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500546012348935883/2500000000000000000 : ℝ) ≤ (1250067390388999/1250000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (2500546012348935883/2500000000000000000 : ℝ)^256 ≤ (1250067390388999/1250000000000000 : ℝ)^1037 := by
      have hnat : (2500546012348935883 : ℕ)^256*1250000000000000^1037 ≤ 1250067390388999^1037*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500546012348935883 2500000000000000000 1250067390388999 1250000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250067390388999/1250000000000000 : ℝ)) (X := (2500546012348935883/2500000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027548836743861437/50000000000000000000 : ℝ) ≤ (200027197837711/200000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (50027548836743861437/50000000000000000000 : ℝ)^256 ≤ (200027197837711/200000000000000 : ℝ)^1037 := by
      have hnat : (50027548836743861437 : ℕ)^256*200000000000000^1037 ≤ 200027197837711^1037*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027548836743861437 50000000000000000000 200027197837711 200000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200027197837711/200000000000000 : ℝ)) (X := (50027548836743861437/50000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022088713254502607/25000000000000000000 : ℝ) ≤ (2500545165164777/2500000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (25022088713254502607/25000000000000000000 : ℝ)^256 ≤ (2500545165164777/2500000000000000 : ℝ)^1037 := by
      have hnat : (25022088713254502607 : ℕ)^256*2500000000000000^1037 ≤ 2500545165164777^1037*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022088713254502607 25000000000000000000 2500545165164777 2500000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500545165164777/2500000000000000 : ℝ)) (X := (25022088713254502607/25000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(546012348935883/5000000000000000000 : ℝ) ≤ ((10831267306527315031/10835000000000000000 : ℝ)+2*(410384386779/216700000000000 : ℝ)*(10519/100000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (10831267306527315031/10835000000000000000 : ℝ)+2*(410384386779/216700000000000 : ℝ)*(10519/100000 : ℝ)=(1250067390388999/1250000000000000 : ℝ) by norm_num, show 1+2*(546012348935883/5000000000000000000 : ℝ)=(2500546012348935883/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22088713254502607/50000000000000000000 : ℝ)+(546012348935883/5000000000000000000 : ℝ) ≤ ((10831267306527315031/10835000000000000000 : ℝ)+(410384386779/216700000000000 : ℝ)*((14853/100000 : ℝ)+(10519/100000 : ℝ)))^(1037/256 : ℝ) := by
    rw [show (10831267306527315031/10835000000000000000 : ℝ)+(410384386779/216700000000000 : ℝ)*((14853/100000 : ℝ)+(10519/100000 : ℝ))=(200027197837711/200000000000000 : ℝ) by norm_num, show 1+(22088713254502607/50000000000000000000 : ℝ)+(546012348935883/5000000000000000000 : ℝ)=(50027548836743861437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22088713254502607/50000000000000000000 : ℝ) ≤ ((10831267306527315031/10835000000000000000 : ℝ)+2*(410384386779/216700000000000 : ℝ)*(14853/100000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (10831267306527315031/10835000000000000000 : ℝ)+2*(410384386779/216700000000000 : ℝ)*(14853/100000 : ℝ)=(2500545165164777/2500000000000000 : ℝ) by norm_num, show 1+2*(22088713254502607/50000000000000000000 : ℝ)=(25022088713254502607/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10831267306527315031/10835000000000000000 : ℝ)*(X 1 0+X 2 0)+(410384386779/216700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (10519/100000 : ℝ)) (hi := (14853/100000 : ℝ)) (c := (10831267306527315031/10835000000000000000 : ℝ)) (alpha := (410384386779/216700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10831267306527315031/10835000000000000000 : ℝ)*(X 0 1+X 2 1)+(410384386779/216700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (10519/100000 : ℝ)) (hi := (14853/100000 : ℝ)) (c := (10831267306527315031/10835000000000000000 : ℝ)) (alpha := (410384386779/216700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10831267306527315031/10835000000000000000 : ℝ)*(X 0 2+X 1 2)+(410384386779/216700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (10519/100000 : ℝ)) (hi := (14853/100000 : ℝ)) (c := (10831267306527315031/10835000000000000000 : ℝ)) (alpha := (410384386779/216700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87370829/400000000 : ℝ)*X 0 0+(5403778599/10000000000 : ℝ)*X 0 1+(1313911199/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673700211/5000000000 : ℝ)*X 1 0+(-2259582893/10000000000 : ℝ)*X 1 1+(1313911191/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668425109/1250000000 : ℝ)*X 2 0+(1313911147/2500000000 : ℝ)*X 2 1+(-2259582529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184759847/5000000000 : ℝ)*X 0 0+(2112859557/5000000000 : ℝ)*X 0 1+(2259116471/5000000000 : ℝ)*X 0 2+(2184759847/5000000000 : ℝ)*X 1 0+(2112859557/5000000000 : ℝ)*X 1 1+(2259116471/5000000000 : ℝ)*X 1 2+(2184759847/5000000000 : ℝ)*X 2 0+(2112859557/5000000000 : ℝ)*X 2 1+(2259116471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-136517449/625000000 : ℝ)*X 0 0+(5256072059/10000000000 : ℝ)*X 0 1+(337709307/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21239919/40000000 : ℝ)*X 1 0+(-1055939063/5000000000 : ℝ)*X 1 1+(1080669821/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309979947/10000000000 : ℝ)*X 2 0+(216133957/400000000 : ℝ)*X 2 1+(-263984763/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184767313/5000000000 : ℝ)*X 0 0+(4517388083/10000000000 : ℝ)*X 0 1+(2113283779/5000000000 : ℝ)*X 0 2+(2184767313/5000000000 : ℝ)*X 1 0+(4517388083/10000000000 : ℝ)*X 1 1+(2113283779/5000000000 : ℝ)*X 1 2+(2184767313/5000000000 : ℝ)*X 2 0+(4517388083/10000000000 : ℝ)*X 2 1+(2113283779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6255847211527194875919571383/541750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107283109/50000000000000 : ℝ)*(base19) + (130897071/25000000000000 : ℝ)*(lower2) + (36097841/100000000000000 : ℝ)*(upper3) + (105072199/100000000000000 : ℝ)*(lower4) + (60355827/100000000000000 : ℝ)*(upper5) + (5084642709689531/100000000000000 : ℝ)*(major0) + (5084642709689531/100000000000000 : ℝ)*(major1) + (5084642709689531/100000000000000 : ℝ)*(major2) + (210957503195681/3125000000000 : ℝ)*(sp0) + (6750642873254631/100000000000000 : ℝ)*(sp1) + (6750643087820849/100000000000000 : ℝ)*(sp2) + (341863890859423/10000000000000 : ℝ)*(sp3) + (2985559057/100000000000000 : ℝ)*(sp4) + (151902399/5000000000000 : ℝ)*(sp7) + (341864194664221/10000000000000 : ℝ)*(f.failure) + (6750643087820849/100000000000000 : ℝ)*(f.sum) + (145126872873371/10835000000000000000000000000 : ℝ)*base66 + (544162089933590461/1083500000000000000000000000000000 : ℝ)*base67 + (9846576456413909539/1083500000000000000000000000000000 : ℝ)*base70 + (9854392574175090461/1083500000000000000000000000000000 : ℝ)*base71 + (2325520034323/5417500000000000000000000000 : ℝ)*base74 + (20407203558691909539/1083500000000000000000000000000000 : ℝ)*base76 + (16365793896665909539/1083500000000000000000000000000000 : ℝ)*base78 + (174564027389909539/1083500000000000000000000000000000 : ℝ)*base80 + (791989793227/1354375000000000000000000000 : ℝ)*base82 + (1386263/125000000000000000000 : ℝ)*base89 + (1386263/125000000000000000000 : ℝ)*base91 + (1386263/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4467493365535233013579242273/541750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1470063837/100000000000000 : ℝ)*(base19) + (847527481/50000000000000 : ℝ)*(base23) + (1384749/100000000000000 : ℝ)*(upper2) + (161834269/100000000000000 : ℝ)*(upper3) + (44777303/12500000000000 : ℝ)*(upper5) + (5114244149111261/100000000000000 : ℝ)*(major0) + (5114244149111261/100000000000000 : ℝ)*(major1) + (5114244149111261/100000000000000 : ℝ)*(major2) + (21832420961/50000000000000 : ℝ)*(sp1) + (19737619889/50000000000000 : ℝ)*(sp2) + (6789943651246261/100000000000000 : ℝ)*(sp4) + (3394949258170251/50000000000000 : ℝ)*(sp5) + (6789902480951521/100000000000000 : ℝ)*(sp6) + (1719272186047937/50000000000000 : ℝ)*(sp7) + (1719272186047937/50000000000000 : ℝ)*(f.failure) + (6789943651246261/100000000000000 : ℝ)*(f.sum) + (56784985335181/10835000000000000000000000000 : ℝ)*base66 + (2397806724440885909/1083500000000000000000000000000000 : ℝ)*base68 + (4439855380178614091/1083500000000000000000000000000000 : ℝ)*base69 + (18812471749985385909/1083500000000000000000000000000000 : ℝ)*base72 + (44799989075079/10835000000000000000000000000 : ℝ)*base73 + (19841234615497614091/1083500000000000000000000000000000 : ℝ)*base75 + (15870238572271885909/1083500000000000000000000000000000 : ℝ)*base78 + (2668860491105885909/1083500000000000000000000000000000 : ℝ)*base80 + (43986811468409/10835000000000000000000000000 : ℝ)*base81 + (2423011/625000000000000000000 : ℝ)*base89 + (2423011/625000000000000000000 : ℝ)*base91 + (2423011/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1104_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14853/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10519/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1104_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1104_s5_0 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092498599/5000000000 : ℝ)*x 0 + (168622903/312500000 : ℝ)*x 1 + (2631506937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092498599/5000000000 : ℝ)^8297 ≤ (13272951663951/100000000000000 : ℝ)^6249 := by
    have hnat : (1092498599 : ℕ)^8297*100000000000000^6249 ≤ 13272951663951^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092498599 5000000000 13272951663951 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168622903/312500000 : ℝ)^8297 ≤ (22040734272879/50000000000000 : ℝ)^6249 := by
    have hnat : (168622903 : ℕ)^8297*50000000000000^6249 ≤ 22040734272879^6249*312500000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168622903 312500000 22040734272879 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631506937/5000000000 : ℝ)^8297 ≤ (1332674367747/3125000000000 : ℝ)^6249 := by
    have hnat : (2631506937 : ℕ)^8297*3125000000000^6249 ≤ 1332674367747^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631506937 5000000000 1332674367747 3125000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092498599/5000000000 : ℝ), (168622903/312500000 : ℝ), (2631506937/5000000000 : ℝ)] ![(13272951663951/100000000000000 : ℝ), (22040734272879/50000000000000 : ℝ), (1332674367747/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092498599/5000000000 : ℝ)|^8297 ≤ (13272951663951/100000000000000 : ℝ)^6249
        have hw : |(-1092498599/5000000000 : ℝ)|=(1092498599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168622903/312500000 : ℝ)|^8297 ≤ (22040734272879/50000000000000 : ℝ)^6249
        have hw : |(168622903/312500000 : ℝ)|=(168622903/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631506937/5000000000 : ℝ)|^8297 ≤ (1332674367747/3125000000000 : ℝ)^6249
        have hw : |(2631506937/5000000000 : ℝ)|=(2631506937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s5_1 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345440429/10000000000 : ℝ)*x 0 + (-1126229321/5000000000 : ℝ)*x 1 + (657876723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345440429/10000000000 : ℝ)^8297 ≤ (43534630381399/100000000000000 : ℝ)^6249 := by
    have hnat : (5345440429 : ℕ)^8297*100000000000000^6249 ≤ 43534630381399^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345440429 10000000000 43534630381399 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126229321/5000000000 : ℝ)^8297 ≤ (2763958162509/20000000000000 : ℝ)^6249 := by
    have hnat : (1126229321 : ℕ)^8297*20000000000000^6249 ≤ 2763958162509^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126229321 5000000000 2763958162509 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657876723/1250000000 : ℝ)^8297 ≤ (42645578799643/100000000000000 : ℝ)^6249 := by
    have hnat : (657876723 : ℕ)^8297*100000000000000^6249 ≤ 42645578799643^6249*1250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657876723 1250000000 42645578799643 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345440429/10000000000 : ℝ), (-1126229321/5000000000 : ℝ), (657876723/1250000000 : ℝ)] ![(43534630381399/100000000000000 : ℝ), (2763958162509/20000000000000 : ℝ), (42645578799643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345440429/10000000000 : ℝ)|^8297 ≤ (43534630381399/100000000000000 : ℝ)^6249
        have hw : |(5345440429/10000000000 : ℝ)|=(5345440429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126229321/5000000000 : ℝ)|^8297 ≤ (2763958162509/20000000000000 : ℝ)^6249
        have hw : |(-1126229321/5000000000 : ℝ)|=(1126229321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657876723/1250000000 : ℝ)|^8297 ≤ (42645578799643/100000000000000 : ℝ)^6249
        have hw : |(657876723/1250000000 : ℝ)|=(657876723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s5_2 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106908807/200000000 : ℝ)*x 0 + (1315753467/2500000000 : ℝ)*x 1 + (-450491727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106908807/200000000 : ℝ)^8297 ≤ (43534629527141/100000000000000 : ℝ)^6249 := by
    have hnat : (106908807 : ℕ)^8297*100000000000000^6249 ≤ 43534629527141^6249*200000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106908807 200000000 43534629527141 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315753467/2500000000 : ℝ)^8297 ≤ (21322789851677/50000000000000 : ℝ)^6249 := by
    have hnat : (1315753467 : ℕ)^8297*50000000000000^6249 ≤ 21322789851677^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315753467 2500000000 21322789851677 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450491727/2000000000 : ℝ)^8297 ≤ (6909895377761/50000000000000 : ℝ)^6249 := by
    have hnat : (450491727 : ℕ)^8297*50000000000000^6249 ≤ 6909895377761^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450491727 2000000000 6909895377761 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106908807/200000000 : ℝ), (1315753467/2500000000 : ℝ), (-450491727/2000000000 : ℝ)] ![(43534629527141/100000000000000 : ℝ), (21322789851677/50000000000000 : ℝ), (6909895377761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106908807/200000000 : ℝ)|^8297 ≤ (43534629527141/100000000000000 : ℝ)^6249
        have hw : |(106908807/200000000 : ℝ)|=(106908807/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315753467/2500000000 : ℝ)|^8297 ≤ (21322789851677/50000000000000 : ℝ)^6249
        have hw : |(1315753467/2500000000 : ℝ)|=(1315753467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-450491727/2000000000 : ℝ)|^8297 ≤ (6909895377761/50000000000000 : ℝ)^6249
        have hw : |(-450491727/2000000000 : ℝ)|=(450491727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s5_3 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873988511/2000000000 : ℝ)*x 0 + (4240686053/10000000000 : ℝ)*x 1 + (4503155741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873988511/2000000000 : ℝ)^8297 ≤ (33315624775629/100000000000000 : ℝ)^6249 := by
    have hnat : (873988511 : ℕ)^8297*100000000000000^6249 ≤ 33315624775629^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873988511 2000000000 33315624775629 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240686053/10000000000 : ℝ)^8297 ≤ (8003406263231/25000000000000 : ℝ)^6249 := by
    have hnat : (4240686053 : ℕ)^8297*25000000000000^6249 ≤ 8003406263231^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240686053 10000000000 8003406263231 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503155741/10000000000 : ℝ)^8297 ≤ (3467075016103/10000000000000 : ℝ)^6249 := by
    have hnat : (4503155741 : ℕ)^8297*10000000000000^6249 ≤ 3467075016103^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503155741 10000000000 3467075016103 10000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873988511/2000000000 : ℝ), (4240686053/10000000000 : ℝ), (4503155741/10000000000 : ℝ)] ![(33315624775629/100000000000000 : ℝ), (8003406263231/25000000000000 : ℝ), (3467075016103/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873988511/2000000000 : ℝ)|^8297 ≤ (33315624775629/100000000000000 : ℝ)^6249
        have hw : |(873988511/2000000000 : ℝ)|=(873988511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240686053/10000000000 : ℝ)|^8297 ≤ (8003406263231/25000000000000 : ℝ)^6249
        have hw : |(4240686053/10000000000 : ℝ)|=(4240686053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503155741/10000000000 : ℝ)|^8297 ≤ (3467075016103/10000000000000 : ℝ)^6249
        have hw : |(4503155741/10000000000 : ℝ)|=(4503155741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s5_4 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-218500269/1000000000 : ℝ)*x 0 + (5263358439/10000000000 : ℝ)*x 1 + (2697793523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218500269/1000000000 : ℝ)^8297 ≤ (13272995959277/100000000000000 : ℝ)^6249 := by
    have hnat : (218500269 : ℕ)^8297*100000000000000^6249 ≤ 13272995959277^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218500269 1000000000 13272995959277 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263358439/10000000000 : ℝ)^8297 ≤ (5331160849517/12500000000000 : ℝ)^6249 := by
    have hnat : (5263358439 : ℕ)^8297*12500000000000^6249 ≤ 5331160849517^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263358439 10000000000 5331160849517 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697793523/5000000000 : ℝ)^8297 ≤ (5509714654099/12500000000000 : ℝ)^6249 := by
    have hnat : (2697793523 : ℕ)^8297*12500000000000^6249 ≤ 5509714654099^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697793523 5000000000 5509714654099 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218500269/1000000000 : ℝ), (5263358439/10000000000 : ℝ), (2697793523/5000000000 : ℝ)] ![(13272995959277/100000000000000 : ℝ), (5331160849517/12500000000000 : ℝ), (5509714654099/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218500269/1000000000 : ℝ)|^8297 ≤ (13272995959277/100000000000000 : ℝ)^6249
        have hw : |(-218500269/1000000000 : ℝ)|=(218500269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263358439/10000000000 : ℝ)|^8297 ≤ (5331160849517/12500000000000 : ℝ)^6249
        have hw : |(5263358439/10000000000 : ℝ)|=(5263358439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697793523/5000000000 : ℝ)|^8297 ≤ (5509714654099/12500000000000 : ℝ)^6249
        have hw : |(2697793523/5000000000 : ℝ)|=(2697793523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s5_5 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311861593/10000000000 : ℝ)*x 0 + (-2119885411/10000000000 : ℝ)*x 1 + (5395587041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311861593/10000000000 : ℝ)^8297 ≤ (10792975892391/25000000000000 : ℝ)^6249 := by
    have hnat : (5311861593 : ℕ)^8297*25000000000000^6249 ≤ 10792975892391^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311861593 10000000000 10792975892391 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119885411/10000000000 : ℝ)^8297 ≤ (159379740527/1250000000000 : ℝ)^6249 := by
    have hnat : (2119885411 : ℕ)^8297*1250000000000^6249 ≤ 159379740527^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119885411 10000000000 159379740527 1250000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395587041/10000000000 : ℝ)^8297 ≤ (44077717178559/100000000000000 : ℝ)^6249 := by
    have hnat : (5395587041 : ℕ)^8297*100000000000000^6249 ≤ 44077717178559^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395587041 10000000000 44077717178559 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311861593/10000000000 : ℝ), (-2119885411/10000000000 : ℝ), (5395587041/10000000000 : ℝ)] ![(10792975892391/25000000000000 : ℝ), (159379740527/1250000000000 : ℝ), (44077717178559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311861593/10000000000 : ℝ)|^8297 ≤ (10792975892391/25000000000000 : ℝ)^6249
        have hw : |(5311861593/10000000000 : ℝ)|=(5311861593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119885411/10000000000 : ℝ)|^8297 ≤ (159379740527/1250000000000 : ℝ)^6249
        have hw : |(-2119885411/10000000000 : ℝ)|=(2119885411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395587041/10000000000 : ℝ)|^8297 ≤ (44077717178559/100000000000000 : ℝ)^6249
        have hw : |(5395587041/10000000000 : ℝ)|=(5395587041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s5_6 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655930799/5000000000 : ℝ)*x 0 + (5395587037/10000000000 : ℝ)*x 1 + (-2119885409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655930799/5000000000 : ℝ)^8297 ≤ (43171903623519/100000000000000 : ℝ)^6249 := by
    have hnat : (2655930799 : ℕ)^8297*100000000000000^6249 ≤ 43171903623519^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655930799 5000000000 43171903623519 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395587037/10000000000 : ℝ)^8297 ≤ (44077717135173/100000000000000 : ℝ)^6249 := by
    have hnat : (5395587037 : ℕ)^8297*100000000000000^6249 ≤ 44077717135173^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395587037 10000000000 44077717135173 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119885409/10000000000 : ℝ)^8297 ≤ (12750379226189/100000000000000 : ℝ)^6249 := by
    have hnat : (2119885409 : ℕ)^8297*100000000000000^6249 ≤ 12750379226189^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119885409 10000000000 12750379226189 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655930799/5000000000 : ℝ), (5395587037/10000000000 : ℝ), (-2119885409/10000000000 : ℝ)] ![(43171903623519/100000000000000 : ℝ), (44077717135173/100000000000000 : ℝ), (12750379226189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655930799/5000000000 : ℝ)|^8297 ≤ (43171903623519/100000000000000 : ℝ)^6249
        have hw : |(2655930799/5000000000 : ℝ)|=(2655930799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395587037/10000000000 : ℝ)|^8297 ≤ (44077717135173/100000000000000 : ℝ)^6249
        have hw : |(5395587037/10000000000 : ℝ)|=(5395587037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2119885409/10000000000 : ℝ)|^8297 ≤ (12750379226189/100000000000000 : ℝ)^6249
        have hw : |(-2119885409/10000000000 : ℝ)|=(2119885409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s5_7 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184976699/5000000000 : ℝ)*x 0 + (4502475203/10000000000 : ℝ)*x 1 + (1060342283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184976699/5000000000 : ℝ)^8297 ≤ (33315734532681/100000000000000 : ℝ)^6249 := by
    have hnat : (2184976699 : ℕ)^8297*100000000000000^6249 ≤ 33315734532681^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184976699 5000000000 33315734532681 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502475203/10000000000 : ℝ)^8297 ≤ (34663793538137/100000000000000 : ℝ)^6249 := by
    have hnat : (4502475203 : ℕ)^8297*100000000000000^6249 ≤ 34663793538137^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502475203 10000000000 34663793538137 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060342283/2500000000 : ℝ)^8297 ≤ (3202047191681/10000000000000 : ℝ)^6249 := by
    have hnat : (1060342283 : ℕ)^8297*10000000000000^6249 ≤ 3202047191681^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060342283 2500000000 3202047191681 10000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184976699/5000000000 : ℝ), (4502475203/10000000000 : ℝ), (1060342283/2500000000 : ℝ)] ![(33315734532681/100000000000000 : ℝ), (34663793538137/100000000000000 : ℝ), (3202047191681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184976699/5000000000 : ℝ)|^8297 ≤ (33315734532681/100000000000000 : ℝ)^6249
        have hw : |(2184976699/5000000000 : ℝ)|=(2184976699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502475203/10000000000 : ℝ)|^8297 ≤ (34663793538137/100000000000000 : ℝ)^6249
        have hw : |(4502475203/10000000000 : ℝ)|=(4502475203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060342283/2500000000 : ℝ)|^8297 ≤ (3202047191681/10000000000000 : ℝ)^6249
        have hw : |(1060342283/2500000000 : ℝ)|=(1060342283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1104_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5629/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11101/100000 : ℝ) ^ (1037/256 : ℝ) ≤ (6791109126706741/50000000000000000000 : ℝ) := by
    have hpowers : (11101/100000 : ℝ)^1037 ≤ (6791109126706741/50000000000000000000 : ℝ)^256 := by
      have hnat : (11101 : ℕ)^1037*50000000000000000000^256 ≤ 6791109126706741^256*100000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11101 100000 6791109126706741 50000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11101/100000 : ℝ)) (X := (6791109126706741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (1037/256 : ℝ) ≤ (37222628327967529/100000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^1037 ≤ (37222628327967529/100000000000000000000 : ℝ)^256 := by
      have hnat : (7119 : ℕ)^1037*100000000000000000000^256 ≤ 37222628327967529^256*50000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 37222628327967529 100000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (37222628327967529/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006791109126706741/25000000000000000000 : ℝ) ≤ (5000335264441087/5000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (25006791109126706741/25000000000000000000 : ℝ)^256 ≤ (5000335264441087/5000000000000000 : ℝ)^1037 := by
      have hnat : (25006791109126706741 : ℕ)^256*5000000000000000^1037 ≤ 5000335264441087^1037*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006791109126706741 25000000000000000000 5000335264441087 5000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000335264441087/5000000000000000 : ℝ)) (X := (25006791109126706741/25000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050804846581381011/100000000000000000000 : ℝ) ≤ (2500313489711229/2500000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (100050804846581381011/100000000000000000000 : ℝ)^256 ≤ (2500313489711229/2500000000000000 : ℝ)^1037 := by
      have hnat : (100050804846581381011 : ℕ)^256*2500000000000000^1037 ≤ 2500313489711229^1037*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050804846581381011 100000000000000000000 2500313489711229 2500000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500313489711229/2500000000000000 : ℝ)) (X := (100050804846581381011/100000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037222628327967529/50000000000000000000 : ℝ) ≤ (5000918694403829/5000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (50037222628327967529/50000000000000000000 : ℝ)^256 ≤ (5000918694403829/5000000000000000 : ℝ)^1037 := by
      have hnat : (50037222628327967529 : ℕ)^256*5000000000000000^1037 ≤ 5000918694403829^1037*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037222628327967529 50000000000000000000 5000918694403829 5000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000918694403829/5000000000000000 : ℝ)) (X := (50037222628327967529/50000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6791109126706741/50000000000000000000 : ℝ) ≤ ((15679575068535290977/15685000000000000000 : ℝ)+2*(291714981371/156850000000000 : ℝ)*(11101/100000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (15679575068535290977/15685000000000000000 : ℝ)+2*(291714981371/156850000000000 : ℝ)*(11101/100000 : ℝ)=(5000335264441087/5000000000000000 : ℝ) by norm_num, show 1+2*(6791109126706741/50000000000000000000 : ℝ)=(25006791109126706741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37222628327967529/100000000000000000000 : ℝ)+(6791109126706741/50000000000000000000 : ℝ) ≤ ((15679575068535290977/15685000000000000000 : ℝ)+(291714981371/156850000000000 : ℝ)*((7119/50000 : ℝ)+(11101/100000 : ℝ)))^(1037/256 : ℝ) := by
    rw [show (15679575068535290977/15685000000000000000 : ℝ)+(291714981371/156850000000000 : ℝ)*((7119/50000 : ℝ)+(11101/100000 : ℝ))=(2500313489711229/2500000000000000 : ℝ) by norm_num, show 1+(37222628327967529/100000000000000000000 : ℝ)+(6791109126706741/50000000000000000000 : ℝ)=(100050804846581381011/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37222628327967529/100000000000000000000 : ℝ) ≤ ((15679575068535290977/15685000000000000000 : ℝ)+2*(291714981371/156850000000000 : ℝ)*(7119/50000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (15679575068535290977/15685000000000000000 : ℝ)+2*(291714981371/156850000000000 : ℝ)*(7119/50000 : ℝ)=(5000918694403829/5000000000000000 : ℝ) by norm_num, show 1+2*(37222628327967529/100000000000000000000 : ℝ)=(50037222628327967529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15679575068535290977/15685000000000000000 : ℝ)*(X 1 0+X 2 0)+(291714981371/156850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (15679575068535290977/15685000000000000000 : ℝ)) (alpha := (291714981371/156850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15679575068535290977/15685000000000000000 : ℝ)*(X 0 1+X 2 1)+(291714981371/156850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (15679575068535290977/15685000000000000000 : ℝ)) (alpha := (291714981371/156850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15679575068535290977/15685000000000000000 : ℝ)*(X 0 2+X 1 2)+(291714981371/156850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (11101/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (15679575068535290977/15685000000000000000 : ℝ)) (alpha := (291714981371/156850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1092498599/5000000000 : ℝ)*X 0 0+(168622903/312500000 : ℝ)*X 0 1+(2631506937/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345440429/10000000000 : ℝ)*X 1 0+(-1126229321/5000000000 : ℝ)*X 1 1+(657876723/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106908807/200000000 : ℝ)*X 2 0+(1315753467/2500000000 : ℝ)*X 2 1+(-450491727/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873988511/2000000000 : ℝ)*X 0 0+(4240686053/10000000000 : ℝ)*X 0 1+(4503155741/10000000000 : ℝ)*X 0 2+(873988511/2000000000 : ℝ)*X 1 0+(4240686053/10000000000 : ℝ)*X 1 1+(4503155741/10000000000 : ℝ)*X 1 2+(873988511/2000000000 : ℝ)*X 2 0+(4240686053/10000000000 : ℝ)*X 2 1+(4503155741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-218500269/1000000000 : ℝ)*X 0 0+(5263358439/10000000000 : ℝ)*X 0 1+(2697793523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311861593/10000000000 : ℝ)*X 1 0+(-2119885411/10000000000 : ℝ)*X 1 1+(5395587041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655930799/5000000000 : ℝ)*X 2 0+(5395587037/10000000000 : ℝ)*X 2 1+(-2119885409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184976699/5000000000 : ℝ)*X 0 0+(4502475203/10000000000 : ℝ)*X 0 1+(1060342283/2500000000 : ℝ)*X 0 2+(2184976699/5000000000 : ℝ)*X 1 0+(4502475203/10000000000 : ℝ)*X 1 1+(1060342283/2500000000 : ℝ)*X 1 2+(2184976699/5000000000 : ℝ)*X 2 0+(4502475203/10000000000 : ℝ)*X 2 1+(1060342283/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6117917637403968995663540211/784250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1574065803/100000000000000 : ℝ)*(base19) + (677189307/50000000000000 : ℝ)*(base23) + (28998607/50000000000000 : ℝ)*(lower2) + (204413637/100000000000000 : ℝ)*(upper3) + (1127093/1000000000000 : ℝ)*(upper5) + (5666729481098881/100000000000000 : ℝ)*(major0) + (5666729481098881/100000000000000 : ℝ)*(major1) + (5666729481098881/100000000000000 : ℝ)*(major2) + (3761708505244149/50000000000000 : ℝ)*(sp0) + (7523451153158049/100000000000000 : ℝ)*(sp1) + (3761725686422619/50000000000000 : ℝ)*(sp2) + (1904991953353807/50000000000000 : ℝ)*(sp3) + (7143347111/20000000000000 : ℝ)*(sp4) + (4413646731/20000000000000 : ℝ)*(sp7) + (952501493735317/25000000000000 : ℝ)*(f.failure) + (1880863181805963/25000000000000 : ℝ)*(f.sum) + (13766953655023/3921250000000000000000000000 : ℝ)*base65 + (8338718434330803263/1568500000000000000000000000000000 : ℝ)*base68 + (13763222372866803263/1568500000000000000000000000000000 : ℝ)*base70 + (35801227819819303263/1568500000000000000000000000000000 : ℝ)*base72 + (102539038948137/15685000000000000000000000000 : ℝ)*base73 + (40878172266404196737/1568500000000000000000000000000000 : ℝ)*base75 + (9700117772430803263/1568500000000000000000000000000000 : ℝ)*base78 + (15079126270395696737/1568500000000000000000000000000000 : ℝ)*base79 + (5172672695769/7842500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2381849/312500000000000000000 : ℝ)*base90 + (2381849/312500000000000000000 : ℝ)*base92 + (2381849/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2008760685146955926408756799/784250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118892381/25000000000000 : ℝ)*(base19) + (131335133/25000000000000 : ℝ)*(base23) + (50533921/100000000000000 : ℝ)*(upper3) + (19142861/100000000000000 : ℝ)*(lower4) + (26483053/50000000000000 : ℝ)*(upper5) + (5696260417187829/100000000000000 : ℝ)*(major0) + (5696260417187829/100000000000000 : ℝ)*(major1) + (5696260417187829/100000000000000 : ℝ)*(major2) + (12420046141/100000000000000 : ℝ)*(sp1) + (841651083/6250000000000 : ℝ)*(sp2) + (1512531950254699/20000000000000 : ℝ)*(sp4) + (7562646855657829/100000000000000 : ℝ)*(sp5) + (1512529151903127/20000000000000 : ℝ)*(sp6) + (3829860997722889/100000000000000 : ℝ)*(sp7) + (3829860997722889/100000000000000 : ℝ)*(f.failure) + (1512531950254699/20000000000000 : ℝ)*(f.sum) + (23690828737899/7842500000000000000000000000 : ℝ)*base65 + (2866423552448181067/1568500000000000000000000000000000 : ℝ)*base68 + (9337428182850818933/1568500000000000000000000000000000 : ℝ)*base69 + (12961488965264181067/1568500000000000000000000000000000 : ℝ)*base72 + (14825214364423/3921250000000000000000000000 : ℝ)*base74 + (15522877318585318933/1568500000000000000000000000000000 : ℝ)*base75 + (14382194612178181067/1568500000000000000000000000000000 : ℝ)*base78 + (104379585187181067/1568500000000000000000000000000000 : ℝ)*base80 + (21718800305313/15685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6198933/1250000000000000000000 : ℝ)*base90 + (6198933/1250000000000000000000 : ℝ)*base92 + (6198933/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1104_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1104_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1104_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16619/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1779/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1104_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1104_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1104_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16619/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1779/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1104_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

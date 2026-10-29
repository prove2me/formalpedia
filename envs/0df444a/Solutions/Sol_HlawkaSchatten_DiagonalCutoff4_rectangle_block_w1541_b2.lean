-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1541_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:07:32.143772+00:00
-- url     : https://prove2.me/submissions/9277608b-c343-49b1-82b9-6f018f397b6e

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
theorem support_rectangle_w1541_box_0 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1617423121/10000000000 : ℝ)*x 0 + (5399706581/10000000000 : ℝ)*x 1 + (5399706213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1617423121/10000000000 : ℝ)^4579 ≤ (1196297683847/12500000000000 : ℝ)^3555 := by
    have hnat : (1617423121 : ℕ)^4579*12500000000000^3555 ≤ 1196297683847^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617423121 10000000000 1196297683847 12500000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399706581/10000000000 : ℝ)^4579 ≤ (45214811241153/100000000000000 : ℝ)^3555 := by
    have hnat : (5399706581 : ℕ)^4579*100000000000000^3555 ≤ 45214811241153^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399706581 10000000000 45214811241153 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399706213/10000000000 : ℝ)^4579 ≤ (45214807272077/100000000000000 : ℝ)^3555 := by
    have hnat : (5399706213 : ℕ)^4579*100000000000000^3555 ≤ 45214807272077^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399706213 10000000000 45214807272077 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1617423121/10000000000 : ℝ), (5399706581/10000000000 : ℝ), (5399706213/10000000000 : ℝ)] ![(1196297683847/12500000000000 : ℝ), (45214811241153/100000000000000 : ℝ), (45214807272077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1617423121/10000000000 : ℝ)|^4579 ≤ (1196297683847/12500000000000 : ℝ)^3555
        have hw : |(-1617423121/10000000000 : ℝ)|=(1617423121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399706581/10000000000 : ℝ)|^4579 ≤ (45214811241153/100000000000000 : ℝ)^3555
        have hw : |(5399706581/10000000000 : ℝ)|=(5399706581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399706213/10000000000 : ℝ)|^4579 ≤ (45214807272077/100000000000000 : ℝ)^3555
        have hw : |(5399706213/10000000000 : ℝ)|=(5399706213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_1 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271052633/10000000000 : ℝ)*x 0 + (-1796090361/10000000000 : ℝ)*x 1 + (5399705383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271052633/10000000000 : ℝ)^4579 ≤ (4383199862709/10000000000000 : ℝ)^3555 := by
    have hnat : (5271052633 : ℕ)^4579*10000000000000^3555 ≤ 4383199862709^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271052633 10000000000 4383199862709 10000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1796090361/10000000000 : ℝ)^4579 ≤ (2738300759179/25000000000000 : ℝ)^3555 := by
    have hnat : (1796090361 : ℕ)^4579*25000000000000^3555 ≤ 2738300759179^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796090361 10000000000 2738300759179 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399705383/10000000000 : ℝ)^4579 ≤ (9042959664017/20000000000000 : ℝ)^3555 := by
    have hnat : (5399705383 : ℕ)^4579*20000000000000^3555 ≤ 9042959664017^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399705383 10000000000 9042959664017 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271052633/10000000000 : ℝ), (-1796090361/10000000000 : ℝ), (5399705383/10000000000 : ℝ)] ![(4383199862709/10000000000000 : ℝ), (2738300759179/25000000000000 : ℝ), (9042959664017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271052633/10000000000 : ℝ)|^4579 ≤ (4383199862709/10000000000000 : ℝ)^3555
        have hw : |(5271052633/10000000000 : ℝ)|=(5271052633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1796090361/10000000000 : ℝ)|^4579 ≤ (2738300759179/25000000000000 : ℝ)^3555
        have hw : |(-1796090361/10000000000 : ℝ)|=(1796090361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399705383/10000000000 : ℝ)|^4579 ≤ (9042959664017/20000000000000 : ℝ)^3555
        have hw : |(5399705383/10000000000 : ℝ)|=(5399705383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_2 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271052399/10000000000 : ℝ)*x 0 + (5399705991/10000000000 : ℝ)*x 1 + (-898044923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271052399/10000000000 : ℝ)^4579 ≤ (21915998060373/50000000000000 : ℝ)^3555 := by
    have hnat : (5271052399 : ℕ)^4579*50000000000000^3555 ≤ 21915998060373^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271052399 10000000000 21915998060373 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399705991/10000000000 : ℝ)^4579 ≤ (45214804877689/100000000000000 : ℝ)^3555 := by
    have hnat : (5399705991 : ℕ)^4579*100000000000000^3555 ≤ 45214804877689^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399705991 10000000000 45214804877689 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898044923/5000000000 : ℝ)^4579 ≤ (10953198991411/100000000000000 : ℝ)^3555 := by
    have hnat : (898044923 : ℕ)^4579*100000000000000^3555 ≤ 10953198991411^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898044923 5000000000 10953198991411 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271052399/10000000000 : ℝ), (5399705991/10000000000 : ℝ), (-898044923/5000000000 : ℝ)] ![(21915998060373/50000000000000 : ℝ), (45214804877689/100000000000000 : ℝ), (10953198991411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271052399/10000000000 : ℝ)|^4579 ≤ (21915998060373/50000000000000 : ℝ)^3555
        have hw : |(5271052399/10000000000 : ℝ)|=(5271052399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399705991/10000000000 : ℝ)|^4579 ≤ (45214804877689/100000000000000 : ℝ)^3555
        have hw : |(5399705991/10000000000 : ℝ)|=(5399705991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898044923/5000000000 : ℝ)|^4579 ≤ (10953198991411/100000000000000 : ℝ)^3555
        have hw : |(-898044923/5000000000 : ℝ)|=(898044923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_3 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2229136121/5000000000 : ℝ)*x 0 + (2081174361/5000000000 : ℝ)*x 1 + (4162348897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2229136121/5000000000 : ℝ)^4579 ≤ (3532732643813/10000000000000 : ℝ)^3555 := by
    have hnat : (2229136121 : ℕ)^4579*10000000000000^3555 ≤ 3532732643813^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229136121 5000000000 3532732643813 10000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2081174361/5000000000 : ℝ)^4579 ≤ (6467267178741/20000000000000 : ℝ)^3555 := by
    have hnat : (2081174361 : ℕ)^4579*20000000000000^3555 ≤ 6467267178741^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081174361 5000000000 6467267178741 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162348897/10000000000 : ℝ)^4579 ≤ (2021021102803/6250000000000 : ℝ)^3555 := by
    have hnat : (4162348897 : ℕ)^4579*6250000000000^3555 ≤ 2021021102803^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162348897 10000000000 2021021102803 6250000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2229136121/5000000000 : ℝ), (2081174361/5000000000 : ℝ), (4162348897/10000000000 : ℝ)] ![(3532732643813/10000000000000 : ℝ), (6467267178741/20000000000000 : ℝ), (2021021102803/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2229136121/5000000000 : ℝ)|^4579 ≤ (3532732643813/10000000000000 : ℝ)^3555
        have hw : |(2229136121/5000000000 : ℝ)|=(2229136121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2081174361/5000000000 : ℝ)|^4579 ≤ (6467267178741/20000000000000 : ℝ)^3555
        have hw : |(2081174361/5000000000 : ℝ)|=(2081174361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162348897/10000000000 : ℝ)|^4579 ≤ (2021021102803/6250000000000 : ℝ)^3555
        have hw : |(4162348897/10000000000 : ℝ)|=(4162348897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_4 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-81600497/400000000 : ℝ)*x 0 + (2622223051/5000000000 : ℝ)*x 1 + (655555903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81600497/400000000 : ℝ)^4579 ≤ (12905534353523/100000000000000 : ℝ)^3555 := by
    have hnat : (81600497 : ℕ)^4579*100000000000000^3555 ≤ 12905534353523^3555*400000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81600497 400000000 12905534353523 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622223051/5000000000 : ℝ)^4579 ≤ (21773613408053/50000000000000 : ℝ)^3555 := by
    have hnat : (2622223051 : ℕ)^4579*50000000000000^3555 ≤ 21773613408053^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622223051 5000000000 21773613408053 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655555903/1250000000 : ℝ)^4579 ≤ (43547238816203/100000000000000 : ℝ)^3555 := by
    have hnat : (655555903 : ℕ)^4579*100000000000000^3555 ≤ 43547238816203^3555*1250000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655555903 1250000000 43547238816203 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81600497/400000000 : ℝ), (2622223051/5000000000 : ℝ), (655555903/1250000000 : ℝ)] ![(12905534353523/100000000000000 : ℝ), (21773613408053/50000000000000 : ℝ), (43547238816203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81600497/400000000 : ℝ)|^4579 ≤ (12905534353523/100000000000000 : ℝ)^3555
        have hw : |(-81600497/400000000 : ℝ)|=(81600497/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622223051/5000000000 : ℝ)|^4579 ≤ (21773613408053/50000000000000 : ℝ)^3555
        have hw : |(2622223051/5000000000 : ℝ)|=(2622223051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655555903/1250000000 : ℝ)|^4579 ≤ (43547238816203/100000000000000 : ℝ)^3555
        have hw : |(655555903/1250000000 : ℝ)|=(655555903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_5 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075781533/2000000000 : ℝ)*x 0 + (-465138437/2500000000 : ℝ)*x 1 + (655555867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075781533/2000000000 : ℝ)^4579 ≤ (8998121682649/20000000000000 : ℝ)^3555 := by
    have hnat : (1075781533 : ℕ)^4579*20000000000000^3555 ≤ 8998121682649^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075781533 2000000000 8998121682649 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465138437/2500000000 : ℝ)^4579 ≤ (11462155838289/100000000000000 : ℝ)^3555 := by
    have hnat : (465138437 : ℕ)^4579*100000000000000^3555 ≤ 11462155838289^3555*2500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465138437 2500000000 11462155838289 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655555867/1250000000 : ℝ)^4579 ≤ (10886808933991/25000000000000 : ℝ)^3555 := by
    have hnat : (655555867 : ℕ)^4579*25000000000000^3555 ≤ 10886808933991^3555*1250000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655555867 1250000000 10886808933991 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075781533/2000000000 : ℝ), (-465138437/2500000000 : ℝ), (655555867/1250000000 : ℝ)] ![(8998121682649/20000000000000 : ℝ), (11462155838289/100000000000000 : ℝ), (10886808933991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075781533/2000000000 : ℝ)|^4579 ≤ (8998121682649/20000000000000 : ℝ)^3555
        have hw : |(1075781533/2000000000 : ℝ)|=(1075781533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-465138437/2500000000 : ℝ)|^4579 ≤ (11462155838289/100000000000000 : ℝ)^3555
        have hw : |(-465138437/2500000000 : ℝ)|=(465138437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655555867/1250000000 : ℝ)|^4579 ≤ (10886808933991/25000000000000 : ℝ)^3555
        have hw : |(655555867/1250000000 : ℝ)|=(655555867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_6 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672363529/1250000000 : ℝ)*x 0 + (5244446523/10000000000 : ℝ)*x 1 + (-372110707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672363529/1250000000 : ℝ)^4579 ≤ (44990614521847/100000000000000 : ℝ)^3555 := by
    have hnat : (672363529 : ℕ)^4579*100000000000000^3555 ≤ 44990614521847^3555*1250000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672363529 1250000000 44990614521847 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244446523/10000000000 : ℝ)^4579 ≤ (1360850978713/3125000000000 : ℝ)^3555 := by
    have hnat : (5244446523 : ℕ)^4579*3125000000000^3555 ≤ 1360850978713^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244446523 10000000000 1360850978713 3125000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (372110707/2000000000 : ℝ)^4579 ≤ (5731077074051/50000000000000 : ℝ)^3555 := by
    have hnat : (372110707 : ℕ)^4579*50000000000000^3555 ≤ 5731077074051^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372110707 2000000000 5731077074051 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672363529/1250000000 : ℝ), (5244446523/10000000000 : ℝ), (-372110707/2000000000 : ℝ)] ![(44990614521847/100000000000000 : ℝ), (1360850978713/3125000000000 : ℝ), (5731077074051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672363529/1250000000 : ℝ)|^4579 ≤ (44990614521847/100000000000000 : ℝ)^3555
        have hw : |(672363529/1250000000 : ℝ)|=(672363529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244446523/10000000000 : ℝ)|^4579 ≤ (1360850978713/3125000000000 : ℝ)^3555
        have hw : |(5244446523/10000000000 : ℝ)|=(5244446523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-372110707/2000000000 : ℝ)|^4579 ≤ (5731077074051/50000000000000 : ℝ)^3555
        have hw : |(-372110707/2000000000 : ℝ)|=(372110707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_7 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32416643/80000000 : ℝ)*x 0 + (4365314269/10000000000 : ℝ)*x 1 + (4365313781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32416643/80000000 : ℝ)^4579 ≤ (31237169395549/100000000000000 : ℝ)^3555 := by
    have hnat : (32416643 : ℕ)^4579*100000000000000^3555 ≤ 31237169395549^3555*80000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32416643 80000000 31237169395549 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4365314269/10000000000 : ℝ)^4579 ≤ (34381417770381/100000000000000 : ℝ)^3555 := by
    have hnat : (4365314269 : ℕ)^4579*100000000000000^3555 ≤ 34381417770381^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365314269 10000000000 34381417770381 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4365313781/10000000000 : ℝ)^4579 ≤ (34381412819767/100000000000000 : ℝ)^3555 := by
    have hnat : (4365313781 : ℕ)^4579*100000000000000^3555 ≤ 34381412819767^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365313781 10000000000 34381412819767 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32416643/80000000 : ℝ), (4365314269/10000000000 : ℝ), (4365313781/10000000000 : ℝ)] ![(31237169395549/100000000000000 : ℝ), (34381417770381/100000000000000 : ℝ), (34381412819767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32416643/80000000 : ℝ)|^4579 ≤ (31237169395549/100000000000000 : ℝ)^3555
        have hw : |(32416643/80000000 : ℝ)|=(32416643/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4365314269/10000000000 : ℝ)|^4579 ≤ (34381417770381/100000000000000 : ℝ)^3555
        have hw : |(4365314269/10000000000 : ℝ)|=(4365314269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4365313781/10000000000 : ℝ)|^4579 ≤ (34381412819767/100000000000000 : ℝ)^3555
        have hw : |(4365313781/10000000000 : ℝ)|=(4365313781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_8 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950566163/10000000000 : ℝ)*x 0 + (2567683119/5000000000 : ℝ)*x 1 + (5420070067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950566163/10000000000 : ℝ)^4579 ≤ (2436267723833/20000000000000 : ℝ)^3555 := by
    have hnat : (1950566163 : ℕ)^4579*20000000000000^3555 ≤ 2436267723833^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950566163 10000000000 2436267723833 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567683119/5000000000 : ℝ)^4579 ≤ (42384099902811/100000000000000 : ℝ)^3555 := by
    have hnat : (2567683119 : ℕ)^4579*100000000000000^3555 ≤ 42384099902811^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567683119 5000000000 42384099902811 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420070067/10000000000 : ℝ)^4579 ≤ (9086912293823/20000000000000 : ℝ)^3555 := by
    have hnat : (5420070067 : ℕ)^4579*20000000000000^3555 ≤ 9086912293823^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420070067 10000000000 9086912293823 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950566163/10000000000 : ℝ), (2567683119/5000000000 : ℝ), (5420070067/10000000000 : ℝ)] ![(2436267723833/20000000000000 : ℝ), (42384099902811/100000000000000 : ℝ), (9086912293823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950566163/10000000000 : ℝ)|^4579 ≤ (2436267723833/20000000000000 : ℝ)^3555
        have hw : |(-1950566163/10000000000 : ℝ)|=(1950566163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567683119/5000000000 : ℝ)|^4579 ≤ (42384099902811/100000000000000 : ℝ)^3555
        have hw : |(2567683119/5000000000 : ℝ)|=(2567683119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420070067/10000000000 : ℝ)|^4579 ≤ (9086912293823/20000000000000 : ℝ)^3555
        have hw : |(5420070067/10000000000 : ℝ)|=(5420070067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_9 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314225119/2500000000 : ℝ)*x 0 + (-1787396167/10000000000 : ℝ)*x 1 + (5420070537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314225119/2500000000 : ℝ)^4579 ≤ (10920118822787/25000000000000 : ℝ)^3555 := by
    have hnat : (1314225119 : ℕ)^4579*25000000000000^3555 ≤ 10920118822787^3555*2500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314225119 2500000000 10920118822787 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1787396167/10000000000 : ℝ)^4579 ≤ (10884958153533/100000000000000 : ℝ)^3555 := by
    have hnat : (1787396167 : ℕ)^4579*100000000000000^3555 ≤ 10884958153533^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787396167 10000000000 10884958153533 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420070537/10000000000 : ℝ)^4579 ≤ (22717283271907/50000000000000 : ℝ)^3555 := by
    have hnat : (5420070537 : ℕ)^4579*50000000000000^3555 ≤ 22717283271907^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420070537 10000000000 22717283271907 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314225119/2500000000 : ℝ), (-1787396167/10000000000 : ℝ), (5420070537/10000000000 : ℝ)] ![(10920118822787/25000000000000 : ℝ), (10884958153533/100000000000000 : ℝ), (22717283271907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314225119/2500000000 : ℝ)|^4579 ≤ (10920118822787/25000000000000 : ℝ)^3555
        have hw : |(1314225119/2500000000 : ℝ)|=(1314225119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1787396167/10000000000 : ℝ)|^4579 ≤ (10884958153533/100000000000000 : ℝ)^3555
        have hw : |(-1787396167/10000000000 : ℝ)|=(1787396167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420070537/10000000000 : ℝ)|^4579 ≤ (22717283271907/50000000000000 : ℝ)^3555
        have hw : |(5420070537/10000000000 : ℝ)|=(5420070537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_10 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256899579/10000000000 : ℝ)*x 0 + (1355017957/2500000000 : ℝ)*x 1 + (-893697807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256899579/10000000000 : ℝ)^4579 ≤ (43680465690931/100000000000000 : ℝ)^3555 := by
    have hnat : (5256899579 : ℕ)^4579*100000000000000^3555 ≤ 43680465690931^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256899579 10000000000 43680465690931 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355017957/2500000000 : ℝ)^4579 ≤ (45434580483043/100000000000000 : ℝ)^3555 := by
    have hnat : (1355017957 : ℕ)^4579*100000000000000^3555 ≤ 45434580483043^3555*2500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355017957 2500000000 45434580483043 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893697807/5000000000 : ℝ)^4579 ≤ (10884953815807/100000000000000 : ℝ)^3555 := by
    have hnat : (893697807 : ℕ)^4579*100000000000000^3555 ≤ 10884953815807^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893697807 5000000000 10884953815807 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256899579/10000000000 : ℝ), (1355017957/2500000000 : ℝ), (-893697807/5000000000 : ℝ)] ![(43680465690931/100000000000000 : ℝ), (45434580483043/100000000000000 : ℝ), (10884953815807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256899579/10000000000 : ℝ)|^4579 ≤ (43680465690931/100000000000000 : ℝ)^3555
        have hw : |(5256899579/10000000000 : ℝ)|=(5256899579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355017957/2500000000 : ℝ)|^4579 ≤ (45434580483043/100000000000000 : ℝ)^3555
        have hw : |(1355017957/2500000000 : ℝ)|=(1355017957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-893697807/5000000000 : ℝ)|^4579 ≤ (10884953815807/100000000000000 : ℝ)^3555
        have hw : |(-893697807/5000000000 : ℝ)|=(893697807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_11 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4510402937/10000000000 : ℝ)*x 0 + (2067847007/5000000000 : ℝ)*x 1 + (516961597/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4510402937/10000000000 : ℝ)^4579 ≤ (35860289961159/100000000000000 : ℝ)^3555 := by
    have hnat : (4510402937 : ℕ)^4579*100000000000000^3555 ≤ 35860289961159^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510402937 10000000000 35860289961159 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067847007/5000000000 : ℝ)^4579 ≤ (16034930599661/50000000000000 : ℝ)^3555 := by
    have hnat : (2067847007 : ℕ)^4579*50000000000000^3555 ≤ 16034930599661^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067847007 5000000000 16034930599661 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516961597/1250000000 : ℝ)^4579 ≤ (6413969766829/20000000000000 : ℝ)^3555 := by
    have hnat : (516961597 : ℕ)^4579*20000000000000^3555 ≤ 6413969766829^3555*1250000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516961597 1250000000 6413969766829 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4510402937/10000000000 : ℝ), (2067847007/5000000000 : ℝ), (516961597/1250000000 : ℝ)] ![(35860289961159/100000000000000 : ℝ), (16034930599661/50000000000000 : ℝ), (6413969766829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4510402937/10000000000 : ℝ)|^4579 ≤ (35860289961159/100000000000000 : ℝ)^3555
        have hw : |(4510402937/10000000000 : ℝ)|=(4510402937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2067847007/5000000000 : ℝ)|^4579 ≤ (16034930599661/50000000000000 : ℝ)^3555
        have hw : |(2067847007/5000000000 : ℝ)|=(2067847007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516961597/1250000000 : ℝ)|^4579 ≤ (6413969766829/20000000000000 : ℝ)^3555
        have hw : |(516961597/1250000000 : ℝ)|=(516961597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_12 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-341333821/2000000000 : ℝ)*x 0 + (550537503/1000000000 : ℝ)*x 1 + (522940279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341333821/2000000000 : ℝ)^4579 ≤ (10255899918379/100000000000000 : ℝ)^3555 := by
    have hnat : (341333821 : ℕ)^4579*100000000000000^3555 ≤ 10255899918379^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341333821 2000000000 10255899918379 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550537503/1000000000 : ℝ)^4579 ≤ (11589424770921/25000000000000 : ℝ)^3555 := by
    have hnat : (550537503 : ℕ)^4579*25000000000000^3555 ≤ 11589424770921^3555*1000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550537503 1000000000 11589424770921 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522940279/1000000000 : ℝ)^4579 ≤ (8677280197029/20000000000000 : ℝ)^3555 := by
    have hnat : (522940279 : ℕ)^4579*20000000000000^3555 ≤ 8677280197029^3555*1000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522940279 1000000000 8677280197029 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341333821/2000000000 : ℝ), (550537503/1000000000 : ℝ), (522940279/1000000000 : ℝ)] ![(10255899918379/100000000000000 : ℝ), (11589424770921/25000000000000 : ℝ), (8677280197029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341333821/2000000000 : ℝ)|^4579 ≤ (10255899918379/100000000000000 : ℝ)^3555
        have hw : |(-341333821/2000000000 : ℝ)|=(341333821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550537503/1000000000 : ℝ)|^4579 ≤ (11589424770921/25000000000000 : ℝ)^3555
        have hw : |(550537503/1000000000 : ℝ)|=(550537503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522940279/1000000000 : ℝ)|^4579 ≤ (8677280197029/20000000000000 : ℝ)^3555
        have hw : |(522940279/1000000000 : ℝ)|=(522940279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_13 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389359373/10000000000 : ℝ)*x 0 + (-186662561/1000000000 : ℝ)*x 1 + (1045880511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389359373/10000000000 : ℝ)^4579 ≤ (22551620952411/50000000000000 : ℝ)^3555 := by
    have hnat : (5389359373 : ℕ)^4579*50000000000000^3555 ≤ 22551620952411^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389359373 10000000000 22551620952411 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186662561/1000000000 : ℝ)^4579 ≤ (5755179800369/50000000000000 : ℝ)^3555 := by
    have hnat : (186662561 : ℕ)^4579*50000000000000^3555 ≤ 5755179800369^3555*1000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186662561 1000000000 5755179800369 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045880511/2000000000 : ℝ)^4579 ≤ (21693199236917/50000000000000 : ℝ)^3555 := by
    have hnat : (1045880511 : ℕ)^4579*50000000000000^3555 ≤ 21693199236917^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045880511 2000000000 21693199236917 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389359373/10000000000 : ℝ), (-186662561/1000000000 : ℝ), (1045880511/2000000000 : ℝ)] ![(22551620952411/50000000000000 : ℝ), (5755179800369/50000000000000 : ℝ), (21693199236917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389359373/10000000000 : ℝ)|^4579 ≤ (22551620952411/50000000000000 : ℝ)^3555
        have hw : |(5389359373/10000000000 : ℝ)|=(5389359373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-186662561/1000000000 : ℝ)|^4579 ≤ (5755179800369/50000000000000 : ℝ)^3555
        have hw : |(-186662561/1000000000 : ℝ)|=(186662561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045880511/2000000000 : ℝ)|^4579 ≤ (21693199236917/50000000000000 : ℝ)^3555
        have hw : |(1045880511/2000000000 : ℝ)|=(1045880511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_14 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269467959/500000000 : ℝ)*x 0 + (5229402693/10000000000 : ℝ)*x 1 + (-233328211/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269467959/500000000 : ℝ)^4579 ≤ (11275809956091/25000000000000 : ℝ)^3555 := by
    have hnat : (269467959 : ℕ)^4579*25000000000000^3555 ≤ 11275809956091^3555*500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269467959 500000000 11275809956091 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229402693/10000000000 : ℝ)^4579 ≤ (43386399948561/100000000000000 : ℝ)^3555 := by
    have hnat : (5229402693 : ℕ)^4579*100000000000000^3555 ≤ 43386399948561^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229402693 10000000000 43386399948561 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233328211/1250000000 : ℝ)^4579 ≤ (575518011013/5000000000000 : ℝ)^3555 := by
    have hnat : (233328211 : ℕ)^4579*5000000000000^3555 ≤ 575518011013^3555*1250000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233328211 1250000000 575518011013 5000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269467959/500000000 : ℝ), (5229402693/10000000000 : ℝ), (-233328211/1250000000 : ℝ)] ![(11275809956091/25000000000000 : ℝ), (43386399948561/100000000000000 : ℝ), (575518011013/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269467959/500000000 : ℝ)|^4579 ≤ (11275809956091/25000000000000 : ℝ)^3555
        have hw : |(269467959/500000000 : ℝ)|=(269467959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229402693/10000000000 : ℝ)|^4579 ≤ (43386399948561/100000000000000 : ℝ)^3555
        have hw : |(5229402693/10000000000 : ℝ)|=(5229402693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233328211/1250000000 : ℝ)|^4579 ≤ (575518011013/5000000000000 : ℝ)^3555
        have hw : |(-233328211/1250000000 : ℝ)|=(233328211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_box_15 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4011859871/10000000000 : ℝ)*x 0 + (4384956499/10000000000 : ℝ)*x 1 + (4384956759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4011859871/10000000000 : ℝ)^4579 ≤ (30838374668787/100000000000000 : ℝ)^3555 := by
    have hnat : (4011859871 : ℕ)^4579*100000000000000^3555 ≤ 30838374668787^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011859871 10000000000 30838374668787 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4384956499/10000000000 : ℝ)^4579 ≤ (8645202835053/25000000000000 : ℝ)^3555 := by
    have hnat : (4384956499 : ℕ)^4579*25000000000000^3555 ≤ 8645202835053^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384956499 10000000000 8645202835053 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4384956759/10000000000 : ℝ)^4579 ≤ (540325218457/1562500000000 : ℝ)^3555 := by
    have hnat : (4384956759 : ℕ)^4579*1562500000000^3555 ≤ 540325218457^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384956759 10000000000 540325218457 1562500000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4011859871/10000000000 : ℝ), (4384956499/10000000000 : ℝ), (4384956759/10000000000 : ℝ)] ![(30838374668787/100000000000000 : ℝ), (8645202835053/25000000000000 : ℝ), (540325218457/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4011859871/10000000000 : ℝ)|^4579 ≤ (30838374668787/100000000000000 : ℝ)^3555
        have hw : |(4011859871/10000000000 : ℝ)|=(4011859871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4384956499/10000000000 : ℝ)|^4579 ≤ (8645202835053/25000000000000 : ℝ)^3555
        have hw : |(4384956499/10000000000 : ℝ)|=(4384956499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4384956759/10000000000 : ℝ)|^4579 ≤ (540325218457/1562500000000 : ℝ)^3555
        have hw : |(4384956759/10000000000 : ℝ)|=(4384956759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1541_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63781/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11753/20000 : ℝ) ∧ (129/160 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43093/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11023/100000 : ℝ) ^ (4577/1024 : ℝ) ≤ (524012938408471/10000000000000000000 : ℝ) := by
    have hpowers : (11023/100000 : ℝ)^4577 ≤ (524012938408471/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11023 : ℕ)^4577*10000000000000000000^1024 ≤ 524012938408471^1024*100000^4577 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11023 100000 524012938408471 10000000000000000000 4577 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11023/100000 : ℝ)) (X := (524012938408471/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4577/1024 : ℝ) ≤ (23940025903282497/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4577 ≤ (23940025903282497/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4577*100000000000000000000^1024 ≤ 23940025903282497^1024*20000^4577 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 23940025903282497 100000000000000000000 4577 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (23940025903282497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000524012938408471/5000000000000000000 : ℝ) ≤ (10000234462496427/10000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (5000524012938408471/5000000000000000000 : ℝ)^1024 ≤ (10000234462496427/10000000000000000 : ℝ)^4577 := by
      have hnat : (5000524012938408471 : ℕ)^1024*10000000000000000^4577 ≤ 10000234462496427^4577*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000524012938408471 5000000000000000000 10000234462496427 10000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000234462496427/10000000000000000 : ℝ)) (X := (5000524012938408471/5000000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029180155287367207/100000000000000000000 : ℝ) ≤ (10000652765902821/10000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (100029180155287367207/100000000000000000000 : ℝ)^1024 ≤ (10000652765902821/10000000000000000 : ℝ)^4577 := by
      have hnat : (100029180155287367207 : ℕ)^1024*10000000000000000^4577 ≤ 10000652765902821^4577*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029180155287367207 100000000000000000000 10000652765902821 10000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000652765902821/10000000000000000 : ℝ)) (X := (100029180155287367207/100000000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023940025903282497/50000000000000000000 : ℝ) ≤ (2000214213861843/2000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (50023940025903282497/50000000000000000000 : ℝ)^1024 ≤ (2000214213861843/2000000000000000 : ℝ)^4577 := by
      have hnat : (50023940025903282497 : ℕ)^1024*2000000000000000^4577 ≤ 2000214213861843^4577*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023940025903282497 50000000000000000000 2000214213861843 2000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000214213861843/2000000000000000 : ℝ)) (X := (50023940025903282497/50000000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(524012938408471/10000000000000000000 : ℝ) ≤ ((892236485095233903/892400000000000000 : ℝ)+2*(209151703197/223100000000000 : ℝ)*(11023/100000 : ℝ))^(4577/1024 : ℝ) := by
    rw [show (892236485095233903/892400000000000000 : ℝ)+2*(209151703197/223100000000000 : ℝ)*(11023/100000 : ℝ)=(10000234462496427/10000000000000000 : ℝ) by norm_num, show 1+2*(524012938408471/10000000000000000000 : ℝ)=(5000524012938408471/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23940025903282497/100000000000000000000 : ℝ)+(524012938408471/10000000000000000000 : ℝ) ≤ ((892236485095233903/892400000000000000 : ℝ)+(209151703197/223100000000000 : ℝ)*((3097/20000 : ℝ)+(11023/100000 : ℝ)))^(4577/1024 : ℝ) := by
    rw [show (892236485095233903/892400000000000000 : ℝ)+(209151703197/223100000000000 : ℝ)*((3097/20000 : ℝ)+(11023/100000 : ℝ))=(10000652765902821/10000000000000000 : ℝ) by norm_num, show 1+(23940025903282497/100000000000000000000 : ℝ)+(524012938408471/10000000000000000000 : ℝ)=(100029180155287367207/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23940025903282497/100000000000000000000 : ℝ) ≤ ((892236485095233903/892400000000000000 : ℝ)+2*(209151703197/223100000000000 : ℝ)*(3097/20000 : ℝ))^(4577/1024 : ℝ) := by
    rw [show (892236485095233903/892400000000000000 : ℝ)+2*(209151703197/223100000000000 : ℝ)*(3097/20000 : ℝ)=(2000214213861843/2000000000000000 : ℝ) by norm_num, show 1+2*(23940025903282497/100000000000000000000 : ℝ)=(50023940025903282497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (892236485095233903/892400000000000000 : ℝ)*(X 1 0+X 2 0)+(209151703197/223100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (11023/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (892236485095233903/892400000000000000 : ℝ)) (alpha := (209151703197/223100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (892236485095233903/892400000000000000 : ℝ)*(X 0 1+X 2 1)+(209151703197/223100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (11023/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (892236485095233903/892400000000000000 : ℝ)) (alpha := (209151703197/223100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (892236485095233903/892400000000000000 : ℝ)*(X 0 2+X 1 2)+(209151703197/223100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (11023/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (892236485095233903/892400000000000000 : ℝ)) (alpha := (209151703197/223100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1617423121/10000000000 : ℝ)*X 0 0+(5399706581/10000000000 : ℝ)*X 0 1+(5399706213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271052633/10000000000 : ℝ)*X 1 0+(-1796090361/10000000000 : ℝ)*X 1 1+(5399705383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271052399/10000000000 : ℝ)*X 2 0+(5399705991/10000000000 : ℝ)*X 2 1+(-898044923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2229136121/5000000000 : ℝ)*X 0 0+(2081174361/5000000000 : ℝ)*X 0 1+(4162348897/10000000000 : ℝ)*X 0 2+(2229136121/5000000000 : ℝ)*X 1 0+(2081174361/5000000000 : ℝ)*X 1 1+(4162348897/10000000000 : ℝ)*X 1 2+(2229136121/5000000000 : ℝ)*X 2 0+(2081174361/5000000000 : ℝ)*X 2 1+(4162348897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-81600497/400000000 : ℝ)*X 0 0+(2622223051/5000000000 : ℝ)*X 0 1+(655555903/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1075781533/2000000000 : ℝ)*X 1 0+(-465138437/2500000000 : ℝ)*X 1 1+(655555867/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672363529/1250000000 : ℝ)*X 2 0+(5244446523/10000000000 : ℝ)*X 2 1+(-372110707/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((32416643/80000000 : ℝ)*X 0 0+(4365314269/10000000000 : ℝ)*X 0 1+(4365313781/10000000000 : ℝ)*X 0 2+(32416643/80000000 : ℝ)*X 1 0+(4365314269/10000000000 : ℝ)*X 1 1+(4365313781/10000000000 : ℝ)*X 1 2+(32416643/80000000 : ℝ)*X 2 0+(4365314269/10000000000 : ℝ)*X 2 1+(4365313781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1950566163/10000000000 : ℝ)*X 0 0+(2567683119/5000000000 : ℝ)*X 0 1+(5420070067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314225119/2500000000 : ℝ)*X 1 0+(-1787396167/10000000000 : ℝ)*X 1 1+(5420070537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256899579/10000000000 : ℝ)*X 2 0+(1355017957/2500000000 : ℝ)*X 2 1+(-893697807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4510402937/10000000000 : ℝ)*X 0 0+(2067847007/5000000000 : ℝ)*X 0 1+(516961597/1250000000 : ℝ)*X 0 2+(4510402937/10000000000 : ℝ)*X 1 0+(2067847007/5000000000 : ℝ)*X 1 1+(516961597/1250000000 : ℝ)*X 1 2+(4510402937/10000000000 : ℝ)*X 2 0+(2067847007/5000000000 : ℝ)*X 2 1+(516961597/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-341333821/2000000000 : ℝ)*X 0 0+(550537503/1000000000 : ℝ)*X 0 1+(522940279/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5389359373/10000000000 : ℝ)*X 1 0+(-186662561/1000000000 : ℝ)*X 1 1+(1045880511/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((269467959/500000000 : ℝ)*X 2 0+(5229402693/10000000000 : ℝ)*X 2 1+(-233328211/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4011859871/10000000000 : ℝ)*X 0 0+(4384956499/10000000000 : ℝ)*X 0 1+(4384956759/10000000000 : ℝ)*X 0 2+(4011859871/10000000000 : ℝ)*X 1 0+(4384956499/10000000000 : ℝ)*X 1 1+(4384956759/10000000000 : ℝ)*X 1 2+(4011859871/10000000000 : ℝ)*X 2 0+(4384956499/10000000000 : ℝ)*X 2 1+(4384956759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63781/100000 : ℝ) ≤ (-7114460476334379147170764914447/11155000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (385313/1250000000000 : ℝ)*(upper1) + (129266141/100000000000000 : ℝ)*(lower2) + (49671279/100000000000000 : ℝ)*(lower3) + (259351/2000000000000 : ℝ)*(upper5) + (1132930494199483/50000000000000 : ℝ)*(major0) + (1132930494199483/50000000000000 : ℝ)*(major1) + (1132930494199483/50000000000000 : ℝ)*(major2) + (148791211/3125000000000 : ℝ)*(sp2) + (1315498693/50000000000000 : ℝ)*(sp3) + (398190734767691/12500000000000 : ℝ)*(sp4) + (1592766677011737/50000000000000 : ℝ)*(sp5) + (1592764296352361/50000000000000 : ℝ)*(sp6) + (683722699274661/50000000000000 : ℝ)*(sp7) + (3737940973/50000000000000 : ℝ)*(sp12) + (341862007386677/25000000000000 : ℝ)*(f.failure) + (1592766677011737/50000000000000 : ℝ)*(f.sum) + (3247857235171/5577500000000000000000000000 : ℝ)*base65 + (122346416107243851/44620000000000000000000000000000 : ℝ)*base68 + (84998762082956149/44620000000000000000000000000000 : ℝ)*base69 + (73214350756636149/44620000000000000000000000000000 : ℝ)*base71 + (15020682046547/2788750000000000000000000000 : ℝ)*base74 + (238061958402716149/44620000000000000000000000000000 : ℝ)*base75 + (3793245516596149/44620000000000000000000000000000 : ℝ)*base77 + (36791143991516149/44620000000000000000000000000000 : ℝ)*base79 + (8409643874173/2788750000000000000000000000 : ℝ)*base81 + (14686367/2500000000000000000000 : ℝ)*base89 + (14686367/2500000000000000000000 : ℝ)*base91 + (14686367/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11753/20000 : ℝ) ≤ (1311092535556011440355620913/2231000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106600489/100000000000000 : ℝ)*(lower1) + (1003033/4000000000000 : ℝ)*(lower3) + (129010261/100000000000000 : ℝ)*(upper4) + (8172033/12500000000000 : ℝ)*(lower5) + (468817275980271/20000000000000 : ℝ)*(major0) + (468817275980271/20000000000000 : ℝ)*(major1) + (468817275980271/20000000000000 : ℝ)*(major2) + (3253924196672479/100000000000000 : ℝ)*(sp0) + (813437887174787/25000000000000 : ℝ)*(sp1) + (3253896511861729/100000000000000 : ℝ)*(sp2) + (70732854259261/5000000000000 : ℝ)*(sp3) + (2466506847/100000000000000 : ℝ)*(sp8) + (175114480177/100000000000000 : ℝ)*(sp9) + (30151317597/100000000000000 : ℝ)*(sp10) + (70732854259261/5000000000000 : ℝ)*(f.failure) + (1626963331589663/50000000000000 : ℝ)*(f.sum) + (4181907862433/2231000000000000000000000000 : ℝ)*base66 + (44975575867924287/17848000000000000000000000000000 : ℝ)*base68 + (114203655630492287/17848000000000000000000000000000 : ℝ)*base70 + (44296917290627713/17848000000000000000000000000000 : ℝ)*base71 + (6153473401/8714843750000000000000000 : ℝ)*base74 + (29848616767028287/17848000000000000000000000000000 : ℝ)*base76 + (11952618233523713/17848000000000000000000000000000 : ℝ)*base77 + (58761285972315713/17848000000000000000000000000000 : ℝ)*base79 + (17358909629701/2231000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (818569/500000000000000000000 : ℝ)*base90 + (818569/500000000000000000000 : ℝ)*base92 + (818569/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (129/160 : ℝ) ≤ (899401306629097669386319359/1115500000000000000000000000 : ℝ) := by norm_num
    linear_combination (205221/1250000000000 : ℝ)*(upper1) + (7525123/4000000000000 : ℝ)*(upper3) + (13465421/12500000000000 : ℝ)*(upper4) + (5028749/10000000000000 : ℝ)*(lower5) + (253440733042839/10000000000000 : ℝ)*(major0) + (253440733042839/10000000000000 : ℝ)*(major1) + (253440733042839/10000000000000 : ℝ)*(major2) + (1627029361/50000000000000 : ℝ)*(sp0) + (298730361949/100000000000000 : ℝ)*(sp2) + (24552754901/50000000000000 : ℝ)*(sp3) + (1756209835481713/50000000000000 : ℝ)*(sp8) + (878105731255537/25000000000000 : ℝ)*(sp9) + (3512124194660199/100000000000000 : ℝ)*(sp10) + (1529466750849877/100000000000000 : ℝ)*(sp11) + (1194934262781/78125000000 : ℝ)*(f.failure) + (878105731255537/25000000000000 : ℝ)*(f.sum) + (2481811270057/2231000000000000000000000000 : ℝ)*base66 + (27328315455894617/8924000000000000000000000000000 : ℝ)*base67 + (16721584459873383/8924000000000000000000000000000 : ℝ)*base70 + (13542507686341383/8924000000000000000000000000000 : ℝ)*base72 + (774147564929/111550000000000000000000000 : ℝ)*base73 + (29952700836625383/8924000000000000000000000000000 : ℝ)*base76 + (9176395133882617/8924000000000000000000000000000 : ℝ)*base77 + (33669269358330617/8924000000000000000000000000000 : ℝ)*base79 + (238762840443/55775000000000000000000000 : ℝ)*base82 + (110601/7812500000000000000 : ℝ)*base89 + (110601/7812500000000000000 : ℝ)*base91 + (110601/7812500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-43093/50000 : ℝ) ≤ (-9613792396139217748892703051/11155000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277183/5000000000000 : ℝ)*(upper3) + (67265871/100000000000000 : ℝ)*(lower4) + (16124359/100000000000000 : ℝ)*(upper5) + (1287084978476527/50000000000000 : ℝ)*(major0) + (1287084978476527/50000000000000 : ℝ)*(major1) + (1287084978476527/50000000000000 : ℝ)*(major2) + (1047036737/100000000000000 : ℝ)*(sp4) + (61333473099/100000000000000 : ℝ)*(sp5) + (3674021367/6250000000000 : ℝ)*(sp6) + (2169491901/20000000000000 : ℝ)*(sp7) + (905888537794873/25000000000000 : ℝ)*(sp12) + (3623493864743129/100000000000000 : ℝ)*(sp13) + (3623496413874357/100000000000000 : ℝ)*(sp14) + (1553501770205983/100000000000000 : ℝ)*(sp15) + (97094538604093/6250000000000 : ℝ)*(f.failure) + (905888799554057/25000000000000 : ℝ)*(f.sum) + (22442572244773/11155000000000000000000000000 : ℝ)*base65 + (1537769400149119/44620000000000000000000000000000 : ℝ)*base68 + (252348305320029119/44620000000000000000000000000000 : ℝ)*base70 + (484401685004970881/44620000000000000000000000000000 : ℝ)*base71 + (1239300303731/5577500000000000000000000000 : ℝ)*base74 + (396470289611550881/44620000000000000000000000000000 : ℝ)*base75 + (116707158002469119/44620000000000000000000000000000 : ℝ)*base78 + (78875478863590881/44620000000000000000000000000000 : ℝ)*base79 + (7812047638523/2788750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3081303/625000000000000000000 : ℝ)*base89 + (3081303/625000000000000000000 : ℝ)*base91 + (3081303/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1541_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63781/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11753/20000 : ℝ) else (129/160 : ℝ) ≤ X j i ∧ X j i ≤ (43093/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1541_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1541_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63781/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11753/20000 : ℝ) else (129/160 : ℝ) ≤ X j i ∧ X j i ≤ (43093/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1541_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63781/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11753/20000 : ℝ) else (129/160 : ℝ) ≤ X j i ∧ X j i ≤ (43093/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1541_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

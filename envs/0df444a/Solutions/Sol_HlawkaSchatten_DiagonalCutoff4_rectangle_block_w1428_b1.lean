-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1428_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:53:36.222801+00:00
-- url     : https://prove2.me/submissions/0c7eb234-1c26-493c-a1b6-e9b42c3ad287

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
theorem support_rectangle_w1428_s3_0 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-492719461/2500000000 : ℝ)*x 0 + (1083477013/2000000000 : ℝ)*x 1 + (523847069/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492719461/2500000000 : ℝ)^1097 ≤ (6010691828841/50000000000000 : ℝ)^841 := by
    have hnat : (492719461 : ℕ)^1097*50000000000000^841 ≤ 6010691828841^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492719461 2500000000 6010691828841 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083477013/2000000000 : ℝ)^1097 ≤ (899053249231/2000000000000 : ℝ)^841 := by
    have hnat : (1083477013 : ℕ)^1097*2000000000000^841 ≤ 899053249231^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083477013 2000000000 899053249231 2000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523847069/1000000000 : ℝ)^1097 ≤ (43025953868159/100000000000000 : ℝ)^841 := by
    have hnat : (523847069 : ℕ)^1097*100000000000000^841 ≤ 43025953868159^841*1000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523847069 1000000000 43025953868159 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-492719461/2500000000 : ℝ), (1083477013/2000000000 : ℝ), (523847069/1000000000 : ℝ)] ![(6010691828841/50000000000000 : ℝ), (899053249231/2000000000000 : ℝ), (43025953868159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-492719461/2500000000 : ℝ)|^1097 ≤ (6010691828841/50000000000000 : ℝ)^841
        have hw : |(-492719461/2500000000 : ℝ)|=(492719461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083477013/2000000000 : ℝ)|^1097 ≤ (899053249231/2000000000000 : ℝ)^841
        have hw : |(1083477013/2000000000 : ℝ)|=(1083477013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523847069/1000000000 : ℝ)|^1097 ≤ (43025953868159/100000000000000 : ℝ)^841
        have hw : |(523847069/1000000000 : ℝ)|=(523847069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s3_1 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349701417/10000000000 : ℝ)*x 0 + (-2062143551/10000000000 : ℝ)*x 1 + (130961767/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349701417/10000000000 : ℝ)^1097 ≤ (2763841941421/6250000000000 : ℝ)^841 := by
    have hnat : (5349701417 : ℕ)^1097*6250000000000^841 ≤ 2763841941421^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349701417 10000000000 2763841941421 6250000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062143551/10000000000 : ℝ)^1097 ≤ (6376287581101/50000000000000 : ℝ)^841 := by
    have hnat : (2062143551 : ℕ)^1097*50000000000000^841 ≤ 6376287581101^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062143551 10000000000 6376287581101 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130961767/250000000 : ℝ)^1097 ≤ (43025953761023/100000000000000 : ℝ)^841 := by
    have hnat : (130961767 : ℕ)^1097*100000000000000^841 ≤ 43025953761023^841*250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130961767 250000000 43025953761023 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349701417/10000000000 : ℝ), (-2062143551/10000000000 : ℝ), (130961767/250000000 : ℝ)] ![(2763841941421/6250000000000 : ℝ), (6376287581101/50000000000000 : ℝ), (43025953761023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349701417/10000000000 : ℝ)|^1097 ≤ (2763841941421/6250000000000 : ℝ)^841
        have hw : |(5349701417/10000000000 : ℝ)|=(5349701417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062143551/10000000000 : ℝ)|^1097 ≤ (6376287581101/50000000000000 : ℝ)^841
        have hw : |(-2062143551/10000000000 : ℝ)|=(2062143551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130961767/250000000 : ℝ)|^1097 ≤ (43025953761023/100000000000000 : ℝ)^841
        have hw : |(130961767/250000000 : ℝ)|=(130961767/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s3_2 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337425363/2500000000 : ℝ)*x 0 + (654808829/1250000000 : ℝ)*x 1 + (-128883973/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337425363/2500000000 : ℝ)^1097 ≤ (44221471440119/100000000000000 : ℝ)^841 := by
    have hnat : (1337425363 : ℕ)^1097*100000000000000^841 ≤ 44221471440119^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337425363 2500000000 44221471440119 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654808829/1250000000 : ℝ)^1097 ≤ (43025953246769/100000000000000 : ℝ)^841 := by
    have hnat : (654808829 : ℕ)^1097*100000000000000^841 ≤ 43025953246769^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654808829 1250000000 43025953246769 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128883973/625000000 : ℝ)^1097 ≤ (6376287649667/50000000000000 : ℝ)^841 := by
    have hnat : (128883973 : ℕ)^1097*50000000000000^841 ≤ 6376287649667^841*625000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128883973 625000000 6376287649667 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337425363/2500000000 : ℝ), (654808829/1250000000 : ℝ), (-128883973/625000000 : ℝ)] ![(44221471440119/100000000000000 : ℝ), (43025953246769/100000000000000 : ℝ), (6376287649667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337425363/2500000000 : ℝ)|^1097 ≤ (44221471440119/100000000000000 : ℝ)^841
        have hw : |(1337425363/2500000000 : ℝ)|=(1337425363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654808829/1250000000 : ℝ)|^1097 ≤ (43025953246769/100000000000000 : ℝ)^841
        have hw : |(654808829/1250000000 : ℝ)|=(654808829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128883973/625000000 : ℝ)|^1097 ≤ (6376287649667/50000000000000 : ℝ)^841
        have hw : |(-128883973/625000000 : ℝ)|=(128883973/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s3_3 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1075993421/2500000000 : ℝ)*x 0 + (4114429839/10000000000 : ℝ)*x 1 + (562667421/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075993421/2500000000 : ℝ)^1097 ≤ (1664905906979/5000000000000 : ℝ)^841 := by
    have hnat : (1075993421 : ℕ)^1097*5000000000000^841 ≤ 1664905906979^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075993421 2500000000 1664905906979 5000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4114429839/10000000000 : ℝ)^1097 ≤ (31398268948969/100000000000000 : ℝ)^841 := by
    have hnat : (4114429839 : ℕ)^1097*100000000000000^841 ≤ 31398268948969^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114429839 10000000000 31398268948969 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562667421/1250000000 : ℝ)^1097 ≤ (35303612897097/100000000000000 : ℝ)^841 := by
    have hnat : (562667421 : ℕ)^1097*100000000000000^841 ≤ 35303612897097^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562667421 1250000000 35303612897097 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075993421/2500000000 : ℝ), (4114429839/10000000000 : ℝ), (562667421/1250000000 : ℝ)] ![(1664905906979/5000000000000 : ℝ), (31398268948969/100000000000000 : ℝ), (35303612897097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075993421/2500000000 : ℝ)|^1097 ≤ (1664905906979/5000000000000 : ℝ)^841
        have hw : |(1075993421/2500000000 : ℝ)|=(1075993421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4114429839/10000000000 : ℝ)|^1097 ≤ (31398268948969/100000000000000 : ℝ)^841
        have hw : |(4114429839/10000000000 : ℝ)|=(4114429839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562667421/1250000000 : ℝ)|^1097 ≤ (35303612897097/100000000000000 : ℝ)^841
        have hw : |(562667421/1250000000 : ℝ)|=(562667421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s3_4 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-492723219/2500000000 : ℝ)*x 0 + (5239185623/10000000000 : ℝ)*x 1 + (216666653/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492723219/2500000000 : ℝ)^1097 ≤ (6010751627667/50000000000000 : ℝ)^841 := by
    have hnat : (492723219 : ℕ)^1097*50000000000000^841 ≤ 6010751627667^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492723219 2500000000 6010751627667 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239185623/10000000000 : ℝ)^1097 ≤ (43033613554487/100000000000000 : ℝ)^841 := by
    have hnat : (5239185623 : ℕ)^1097*100000000000000^841 ≤ 43033613554487^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239185623 10000000000 43033613554487 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216666653/400000000 : ℝ)^1097 ≤ (8988976636357/20000000000000 : ℝ)^841 := by
    have hnat : (216666653 : ℕ)^1097*20000000000000^841 ≤ 8988976636357^841*400000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216666653 400000000 8988976636357 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-492723219/2500000000 : ℝ), (5239185623/10000000000 : ℝ), (216666653/400000000 : ℝ)] ![(6010751627667/50000000000000 : ℝ), (43033613554487/100000000000000 : ℝ), (8988976636357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-492723219/2500000000 : ℝ)|^1097 ≤ (6010751627667/50000000000000 : ℝ)^841
        have hw : |(-492723219/2500000000 : ℝ)|=(492723219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239185623/10000000000 : ℝ)|^1097 ≤ (43033613554487/100000000000000 : ℝ)^841
        have hw : |(5239185623/10000000000 : ℝ)|=(5239185623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216666653/400000000 : ℝ)|^1097 ≤ (8988976636357/20000000000000 : ℝ)^841
        have hw : |(216666653/400000000 : ℝ)|=(216666653/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s3_5 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (662899217/1250000000 : ℝ)*x 0 + (-376789601/2000000000 : ℝ)*x 1 + (541666629/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662899217/1250000000 : ℝ)^1097 ≤ (8744134568333/20000000000000 : ℝ)^841 := by
    have hnat : (662899217 : ℕ)^1097*20000000000000^841 ≤ 8744134568333^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662899217 1250000000 8744134568333 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376789601/2000000000 : ℝ)^1097 ≤ (5667222172581/50000000000000 : ℝ)^841 := by
    have hnat : (376789601 : ℕ)^1097*50000000000000^841 ≤ 5667222172581^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376789601 2000000000 5667222172581 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541666629/1000000000 : ℝ)^1097 ≤ (4494488280297/10000000000000 : ℝ)^841 := by
    have hnat : (541666629 : ℕ)^1097*10000000000000^841 ≤ 4494488280297^841*1000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541666629 1000000000 4494488280297 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662899217/1250000000 : ℝ), (-376789601/2000000000 : ℝ), (541666629/1000000000 : ℝ)] ![(8744134568333/20000000000000 : ℝ), (5667222172581/50000000000000 : ℝ), (4494488280297/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662899217/1250000000 : ℝ)|^1097 ≤ (8744134568333/20000000000000 : ℝ)^841
        have hw : |(662899217/1250000000 : ℝ)|=(662899217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-376789601/2000000000 : ℝ)|^1097 ≤ (5667222172581/50000000000000 : ℝ)^841
        have hw : |(-376789601/2000000000 : ℝ)|=(376789601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541666629/1000000000 : ℝ)|^1097 ≤ (4494488280297/10000000000000 : ℝ)^841
        have hw : |(541666629/1000000000 : ℝ)|=(541666629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s3_6 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1060638683/2000000000 : ℝ)*x 0 + (5416666637/10000000000 : ℝ)*x 1 + (-376789593/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060638683/2000000000 : ℝ)^1097 ≤ (43720669389711/100000000000000 : ℝ)^841 := by
    have hnat : (1060638683 : ℕ)^1097*100000000000000^841 ≤ 43720669389711^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060638683 2000000000 43720669389711 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416666637/10000000000 : ℝ)^1097 ≤ (44944886558647/100000000000000 : ℝ)^841 := by
    have hnat : (5416666637 : ℕ)^1097*100000000000000^841 ≤ 44944886558647^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416666637 10000000000 44944886558647 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (376789593/2000000000 : ℝ)^1097 ≤ (5667222015627/50000000000000 : ℝ)^841 := by
    have hnat : (376789593 : ℕ)^1097*50000000000000^841 ≤ 5667222015627^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376789593 2000000000 5667222015627 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060638683/2000000000 : ℝ), (5416666637/10000000000 : ℝ), (-376789593/2000000000 : ℝ)] ![(43720669389711/100000000000000 : ℝ), (44944886558647/100000000000000 : ℝ), (5667222015627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060638683/2000000000 : ℝ)|^1097 ≤ (43720669389711/100000000000000 : ℝ)^841
        have hw : |(1060638683/2000000000 : ℝ)|=(1060638683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416666637/10000000000 : ℝ)|^1097 ≤ (44944886558647/100000000000000 : ℝ)^841
        have hw : |(5416666637/10000000000 : ℝ)|=(5416666637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-376789593/2000000000 : ℝ)|^1097 ≤ (5667222015627/50000000000000 : ℝ)^841
        have hw : |(-376789593/2000000000 : ℝ)|=(376789593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s3_7 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4304006633/10000000000 : ℝ)*x 0 + (2249896991/5000000000 : ℝ)*x 1 + (4115984511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304006633/10000000000 : ℝ)^1097 ≤ (33298450648621/100000000000000 : ℝ)^841 := by
    have hnat : (4304006633 : ℕ)^1097*100000000000000^841 ≤ 33298450648621^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304006633 10000000000 33298450648621 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249896991/5000000000 : ℝ)^1097 ≤ (35287803973321/100000000000000 : ℝ)^841 := by
    have hnat : (2249896991 : ℕ)^1097*100000000000000^841 ≤ 35287803973321^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249896991 5000000000 35287803973321 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4115984511/10000000000 : ℝ)^1097 ≤ (31413745366087/100000000000000 : ℝ)^841 := by
    have hnat : (4115984511 : ℕ)^1097*100000000000000^841 ≤ 31413745366087^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115984511 10000000000 31413745366087 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304006633/10000000000 : ℝ), (2249896991/5000000000 : ℝ), (4115984511/10000000000 : ℝ)] ![(33298450648621/100000000000000 : ℝ), (35287803973321/100000000000000 : ℝ), (31413745366087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304006633/10000000000 : ℝ)|^1097 ≤ (33298450648621/100000000000000 : ℝ)^841
        have hw : |(4304006633/10000000000 : ℝ)|=(4304006633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249896991/5000000000 : ℝ)|^1097 ≤ (35287803973321/100000000000000 : ℝ)^841
        have hw : |(2249896991/5000000000 : ℝ)|=(2249896991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4115984511/10000000000 : ℝ)|^1097 ≤ (31413745366087/100000000000000 : ℝ)^841
        have hw : |(4115984511/10000000000 : ℝ)|=(4115984511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1428_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15803/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5579/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14947/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15803/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5181/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15803/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5181/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15803/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5181/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15803/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5181/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15803/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5181/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15803/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5181/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5181/50000 : ℝ) ^ (4387/1024 : ℝ) ≤ (3026588814071819/50000000000000000000 : ℝ) := by
    have hpowers : (5181/50000 : ℝ)^4387 ≤ (3026588814071819/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5181 : ℕ)^4387*50000000000000000000^1024 ≤ 3026588814071819^1024*50000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5181 50000 3026588814071819 50000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5181/50000 : ℝ)) (X := (3026588814071819/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15803/100000 : ℝ) ^ (4387/1024 : ℝ) ≤ (36919534222236351/100000000000000000000 : ℝ) := by
    have hpowers : (15803/100000 : ℝ)^4387 ≤ (36919534222236351/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15803 : ℕ)^4387*100000000000000000000^1024 ≤ 36919534222236351^1024*100000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15803 100000 36919534222236351 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15803/100000 : ℝ)) (X := (36919534222236351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003026588814071819/25000000000000000000 : ℝ) ≤ (2000056513939249/2000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (25003026588814071819/25000000000000000000 : ℝ)^1024 ≤ (2000056513939249/2000000000000000 : ℝ)^4387 := by
      have hnat : (25003026588814071819 : ℕ)^1024*2000000000000000^4387 ≤ 2000056513939249^4387*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003026588814071819 25000000000000000000 2000056513939249 2000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056513939249/2000000000000000 : ℝ)) (X := (25003026588814071819/25000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042972711850379989/100000000000000000000 : ℝ) ≤ (2000200578120931/2000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (100042972711850379989/100000000000000000000 : ℝ)^1024 ≤ (2000200578120931/2000000000000000 : ℝ)^4387 := by
      have hnat : (100042972711850379989 : ℕ)^1024*2000000000000000^4387 ≤ 2000200578120931^4387*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042972711850379989 100000000000000000000 2000200578120931 2000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000200578120931/2000000000000000 : ℝ)) (X := (100042972711850379989/100000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036919534222236351/50000000000000000000 : ℝ) ≤ (2000344642302613/2000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50036919534222236351/50000000000000000000 : ℝ)^1024 ≤ (2000344642302613/2000000000000000 : ℝ)^4387 := by
      have hnat : (50036919534222236351 : ℕ)^1024*2000000000000000^4387 ≤ 2000344642302613^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036919534222236351 50000000000000000000 2000344642302613 2000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000344642302613/2000000000000000 : ℝ)) (X := (50036919534222236351/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3026588814071819/50000000000000000000 : ℝ) ≤ ((10879321906242276041/10882000000000000000 : ℝ)+2*(72032090841/54410000000000 : ℝ)*(5181/50000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (10879321906242276041/10882000000000000000 : ℝ)+2*(72032090841/54410000000000 : ℝ)*(5181/50000 : ℝ)=(2000056513939249/2000000000000000 : ℝ) by norm_num, show 1+2*(3026588814071819/50000000000000000000 : ℝ)=(25003026588814071819/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36919534222236351/100000000000000000000 : ℝ)+(3026588814071819/50000000000000000000 : ℝ) ≤ ((10879321906242276041/10882000000000000000 : ℝ)+(72032090841/54410000000000 : ℝ)*((15803/100000 : ℝ)+(5181/50000 : ℝ)))^(4387/1024 : ℝ) := by
    rw [show (10879321906242276041/10882000000000000000 : ℝ)+(72032090841/54410000000000 : ℝ)*((15803/100000 : ℝ)+(5181/50000 : ℝ))=(2000200578120931/2000000000000000 : ℝ) by norm_num, show 1+(36919534222236351/100000000000000000000 : ℝ)+(3026588814071819/50000000000000000000 : ℝ)=(100042972711850379989/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36919534222236351/100000000000000000000 : ℝ) ≤ ((10879321906242276041/10882000000000000000 : ℝ)+2*(72032090841/54410000000000 : ℝ)*(15803/100000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (10879321906242276041/10882000000000000000 : ℝ)+2*(72032090841/54410000000000 : ℝ)*(15803/100000 : ℝ)=(2000344642302613/2000000000000000 : ℝ) by norm_num, show 1+2*(36919534222236351/100000000000000000000 : ℝ)=(50036919534222236351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10879321906242276041/10882000000000000000 : ℝ)*(X 1 0+X 2 0)+(72032090841/54410000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5181/50000 : ℝ)) (hi := (15803/100000 : ℝ)) (c := (10879321906242276041/10882000000000000000 : ℝ)) (alpha := (72032090841/54410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10879321906242276041/10882000000000000000 : ℝ)*(X 0 1+X 2 1)+(72032090841/54410000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5181/50000 : ℝ)) (hi := (15803/100000 : ℝ)) (c := (10879321906242276041/10882000000000000000 : ℝ)) (alpha := (72032090841/54410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10879321906242276041/10882000000000000000 : ℝ)*(X 0 2+X 1 2)+(72032090841/54410000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5181/50000 : ℝ)) (hi := (15803/100000 : ℝ)) (c := (10879321906242276041/10882000000000000000 : ℝ)) (alpha := (72032090841/54410000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-492719461/2500000000 : ℝ)*X 0 0+(1083477013/2000000000 : ℝ)*X 0 1+(523847069/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349701417/10000000000 : ℝ)*X 1 0+(-2062143551/10000000000 : ℝ)*X 1 1+(130961767/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337425363/2500000000 : ℝ)*X 2 0+(654808829/1250000000 : ℝ)*X 2 1+(-128883973/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075993421/2500000000 : ℝ)*X 0 0+(4114429839/10000000000 : ℝ)*X 0 1+(562667421/1250000000 : ℝ)*X 0 2+(1075993421/2500000000 : ℝ)*X 1 0+(4114429839/10000000000 : ℝ)*X 1 1+(562667421/1250000000 : ℝ)*X 1 2+(1075993421/2500000000 : ℝ)*X 2 0+(4114429839/10000000000 : ℝ)*X 2 1+(562667421/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-492723219/2500000000 : ℝ)*X 0 0+(5239185623/10000000000 : ℝ)*X 0 1+(216666653/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662899217/1250000000 : ℝ)*X 1 0+(-376789601/2000000000 : ℝ)*X 1 1+(541666629/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060638683/2000000000 : ℝ)*X 2 0+(5416666637/10000000000 : ℝ)*X 2 1+(-376789593/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304006633/10000000000 : ℝ)*X 0 0+(2249896991/5000000000 : ℝ)*X 0 1+(4115984511/10000000000 : ℝ)*X 0 2+(4304006633/10000000000 : ℝ)*X 1 0+(2249896991/5000000000 : ℝ)*X 1 1+(4115984511/10000000000 : ℝ)*X 1 2+(4304006633/10000000000 : ℝ)*X 2 0+(2249896991/5000000000 : ℝ)*X 2 1+(4115984511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5312098171845021896012570517/544100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1754388697/100000000000000 : ℝ)*(base19) + (1753538671/100000000000000 : ℝ)*(base23) + (269918649/100000000000000 : ℝ)*(upper3) + (2502173/12500000000000 : ℝ)*(upper4) + (1436483/625000000000 : ℝ)*(upper5) + (4086970200525679/100000000000000 : ℝ)*(major0) + (4086970200525679/100000000000000 : ℝ)*(major1) + (4086970200525679/100000000000000 : ℝ)*(major2) + (5589297699027617/100000000000000 : ℝ)*(sp0) + (1397331840579737/25000000000000 : ℝ)*(sp1) + (2794663681584487/50000000000000 : ℝ)*(sp2) + (1292298399829751/50000000000000 : ℝ)*(sp3) + (7854420007/25000000000000 : ℝ)*(sp4) + (7079623909/50000000000000 : ℝ)*(sp7) + (64615273972683/2500000000000 : ℝ)*(f.failure) + (1117865823341529/20000000000000 : ℝ)*(f.sum) + (839382023489/170031250000000000000000000 : ℝ)*base66 + (4335834320229843161/1088200000000000000000000000000000 : ℝ)*base68 + (2559604157710043161/1088200000000000000000000000000000 : ℝ)*base70 + (8738345989524843161/1088200000000000000000000000000000 : ℝ)*base72 + (2252325162917/1360250000000000000000000000 : ℝ)*base74 + (2382193004647956839/1088200000000000000000000000000000 : ℝ)*base75 + (12011217323727243161/1088200000000000000000000000000000 : ℝ)*base78 + (5803584508294356839/1088200000000000000000000000000000 : ℝ)*base79 + (913117095163/680125000000000000000000000 : ℝ)*base82 + (336601/125000000000000000000 : ℝ)*base89 + (336601/125000000000000000000 : ℝ)*base91 + (336601/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2141041266918828305420144823/272050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255226651/100000000000000 : ℝ)*(base19) + (95013939/100000000000000 : ℝ)*(base23) + (820171/2000000000000 : ℝ)*(upper3) + (40971761/50000000000000 : ℝ)*(lower4) + (1990649/5000000000000 : ℝ)*(upper5) + (2059967395122901/50000000000000 : ℝ)*(major0) + (2059967395122901/50000000000000 : ℝ)*(major1) + (2059967395122901/50000000000000 : ℝ)*(major2) + (789159469/25000000000000 : ℝ)*(sp1) + (615763867/10000000000000 : ℝ)*(sp2) + (563441146395441/10000000000000 : ℝ)*(sp4) + (5634408052089883/100000000000000 : ℝ)*(sp5) + (5634405211301799/100000000000000 : ℝ)*(sp6) + (26054578542029/1000000000000 : ℝ)*(sp7) + (26054578542029/1000000000000 : ℝ)*(f.failure) + (563441146395441/10000000000000 : ℝ)*(f.sum) + (2596423758897/680125000000000000000000000 : ℝ)*base66 + (4790798089532085059/544100000000000000000000000000000 : ℝ)*base68 + (6409239819004085059/544100000000000000000000000000000 : ℝ)*base70 + (3209689003497085059/544100000000000000000000000000000 : ℝ)*base72 + (6072365634941/1088200000000000000000000000 : ℝ)*base74 + (6473104372654085059/544100000000000000000000000000000 : ℝ)*base76 + (2015216651298414941/544100000000000000000000000000000 : ℝ)*base77 + (1931844709958614941/544100000000000000000000000000000 : ℝ)*base79 + (47681301598541/5441000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base88 + (316863/50000000000000000000 : ℝ)*base89 + (316863/50000000000000000000 : ℝ)*base91 + (316863/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1428_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15803/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14947/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1428_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1428_s4_0 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971785649/10000000000 : ℝ)*x 0 + (2704827987/5000000000 : ℝ)*x 1 + (2622800911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971785649/10000000000 : ℝ)^1097 ≤ (3007151709241/25000000000000 : ℝ)^841 := by
    have hnat : (1971785649 : ℕ)^1097*25000000000000^841 ≤ 3007151709241^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971785649 10000000000 3007151709241 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704827987/5000000000 : ℝ)^1097 ≤ (44869023155941/100000000000000 : ℝ)^841 := by
    have hnat : (2704827987 : ℕ)^1097*100000000000000^841 ≤ 44869023155941^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704827987 5000000000 44869023155941 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622800911/5000000000 : ℝ)^1097 ≤ (4310236999819/10000000000000 : ℝ)^841 := by
    have hnat : (2622800911 : ℕ)^1097*10000000000000^841 ≤ 4310236999819^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622800911 5000000000 4310236999819 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971785649/10000000000 : ℝ), (2704827987/5000000000 : ℝ), (2622800911/5000000000 : ℝ)] ![(3007151709241/25000000000000 : ℝ), (44869023155941/100000000000000 : ℝ), (4310236999819/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971785649/10000000000 : ℝ)|^1097 ≤ (3007151709241/25000000000000 : ℝ)^841
        have hw : |(-1971785649/10000000000 : ℝ)|=(1971785649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704827987/5000000000 : ℝ)|^1097 ≤ (44869023155941/100000000000000 : ℝ)^841
        have hw : |(2704827987/5000000000 : ℝ)|=(2704827987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622800911/5000000000 : ℝ)|^1097 ≤ (4310236999819/10000000000000 : ℝ)^841
        have hw : |(2622800911/5000000000 : ℝ)|=(2622800911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s4_1 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5347706111/10000000000 : ℝ)*x 0 + (-205533363/1000000000 : ℝ)*x 1 + (5245601993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347706111/10000000000 : ℝ)^1097 ≤ (44199958154427/100000000000000 : ℝ)^841 := by
    have hnat : (5347706111 : ℕ)^1097*100000000000000^841 ≤ 44199958154427^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347706111 10000000000 44199958154427 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205533363/1000000000 : ℝ)^1097 ≤ (6348834998853/50000000000000 : ℝ)^841 := by
    have hnat : (205533363 : ℕ)^1097*50000000000000^841 ≤ 6348834998853^841*1000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205533363 1000000000 6348834998853 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245601993/10000000000 : ℝ)^1097 ≤ (2155118591549/5000000000000 : ℝ)^841 := by
    have hnat : (5245601993 : ℕ)^1097*5000000000000^841 ≤ 2155118591549^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245601993 10000000000 2155118591549 5000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347706111/10000000000 : ℝ), (-205533363/1000000000 : ℝ), (5245601993/10000000000 : ℝ)] ![(44199958154427/100000000000000 : ℝ), (6348834998853/50000000000000 : ℝ), (2155118591549/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347706111/10000000000 : ℝ)|^1097 ≤ (44199958154427/100000000000000 : ℝ)^841
        have hw : |(5347706111/10000000000 : ℝ)|=(5347706111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205533363/1000000000 : ℝ)|^1097 ≤ (6348834998853/50000000000000 : ℝ)^841
        have hw : |(-205533363/1000000000 : ℝ)|=(205533363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245601993/10000000000 : ℝ)|^1097 ≤ (2155118591549/5000000000000 : ℝ)^841
        have hw : |(5245601993/10000000000 : ℝ)|=(5245601993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s4_2 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (167115811/312500000 : ℝ)*x 0 + (2622801117/5000000000 : ℝ)*x 1 + (-2055333523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167115811/312500000 : ℝ)^1097 ≤ (1767998257609/4000000000000 : ℝ)^841 := by
    have hnat : (167115811 : ℕ)^1097*4000000000000^841 ≤ 1767998257609^841*312500000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167115811 312500000 1767998257609 4000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622801117/5000000000 : ℝ)^1097 ≤ (21551187207017/50000000000000 : ℝ)^841 := by
    have hnat : (2622801117 : ℕ)^1097*50000000000000^841 ≤ 21551187207017^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622801117 5000000000 21551187207017 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055333523/10000000000 : ℝ)^1097 ≤ (253953382709/2000000000000 : ℝ)^841 := by
    have hnat : (2055333523 : ℕ)^1097*2000000000000^841 ≤ 253953382709^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055333523 10000000000 253953382709 2000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167115811/312500000 : ℝ), (2622801117/5000000000 : ℝ), (-2055333523/10000000000 : ℝ)] ![(1767998257609/4000000000000 : ℝ), (21551187207017/50000000000000 : ℝ), (253953382709/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167115811/312500000 : ℝ)|^1097 ≤ (1767998257609/4000000000000 : ℝ)^841
        have hw : |(167115811/312500000 : ℝ)|=(167115811/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622801117/5000000000 : ℝ)|^1097 ≤ (21551187207017/50000000000000 : ℝ)^841
        have hw : |(2622801117/5000000000 : ℝ)|=(2622801117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055333523/10000000000 : ℝ)|^1097 ≤ (253953382709/2000000000000 : ℝ)^841
        have hw : |(-2055333523/10000000000 : ℝ)|=(2055333523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s4_3 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2152264429/5000000000 : ℝ)*x 0 + (4130430933/10000000000 : ℝ)*x 1 + (4485204419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152264429/5000000000 : ℝ)^1097 ≤ (33303720852361/100000000000000 : ℝ)^841 := by
    have hnat : (2152264429 : ℕ)^1097*100000000000000^841 ≤ 33303720852361^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152264429 5000000000 33303720852361 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4130430933/10000000000 : ℝ)^1097 ≤ (15778820673511/50000000000000 : ℝ)^841 := by
    have hnat : (4130430933 : ℕ)^1097*50000000000000^841 ≤ 15778820673511^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130430933 10000000000 15778820673511 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485204419/10000000000 : ℝ)^1097 ≤ (17569318892861/50000000000000 : ℝ)^841 := by
    have hnat : (4485204419 : ℕ)^1097*50000000000000^841 ≤ 17569318892861^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485204419 10000000000 17569318892861 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152264429/5000000000 : ℝ), (4130430933/10000000000 : ℝ), (4485204419/10000000000 : ℝ)] ![(33303720852361/100000000000000 : ℝ), (15778820673511/50000000000000 : ℝ), (17569318892861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152264429/5000000000 : ℝ)|^1097 ≤ (33303720852361/100000000000000 : ℝ)^841
        have hw : |(2152264429/5000000000 : ℝ)|=(2152264429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4130430933/10000000000 : ℝ)|^1097 ≤ (15778820673511/50000000000000 : ℝ)^841
        have hw : |(4130430933/10000000000 : ℝ)|=(4130430933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485204419/10000000000 : ℝ)|^1097 ≤ (17569318892861/50000000000000 : ℝ)^841
        have hw : |(4485204419/10000000000 : ℝ)|=(4485204419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s4_4 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-98589883/500000000 : ℝ)*x 0 + (5246203277/10000000000 : ℝ)*x 1 + (216362051/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98589883/500000000 : ℝ)^1097 ≤ (12028702412299/100000000000000 : ℝ)^841 := by
    have hnat : (98589883 : ℕ)^1097*100000000000000^841 ≤ 12028702412299^841*500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98589883 500000000 12028702412299 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246203277/10000000000 : ℝ)^1097 ≤ (43108816545573/100000000000000 : ℝ)^841 := by
    have hnat : (5246203277 : ℕ)^1097*100000000000000^841 ≤ 43108816545573^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246203277 10000000000 43108816545573 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216362051/400000000 : ℝ)^1097 ≤ (44862481021559/100000000000000 : ℝ)^841 := by
    have hnat : (216362051 : ℕ)^1097*100000000000000^841 ≤ 44862481021559^841*400000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216362051 400000000 44862481021559 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98589883/500000000 : ℝ), (5246203277/10000000000 : ℝ), (216362051/400000000 : ℝ)] ![(12028702412299/100000000000000 : ℝ), (43108816545573/100000000000000 : ℝ), (44862481021559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98589883/500000000 : ℝ)|^1097 ≤ (12028702412299/100000000000000 : ℝ)^841
        have hw : |(-98589883/500000000 : ℝ)|=(98589883/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246203277/10000000000 : ℝ)|^1097 ≤ (43108816545573/100000000000000 : ℝ)^841
        have hw : |(5246203277/10000000000 : ℝ)|=(5246203277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216362051/400000000 : ℝ)|^1097 ≤ (44862481021559/100000000000000 : ℝ)^841
        have hw : |(216362051/400000000 : ℝ)|=(216362051/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s4_5 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (165783157/312500000 : ℝ)*x 0 + (-1891884143/10000000000 : ℝ)*x 1 + (1352262821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165783157/312500000 : ℝ)^1097 ≤ (21870377133931/50000000000000 : ℝ)^841 := by
    have hnat : (165783157 : ℕ)^1097*50000000000000^841 ≤ 21870377133931^841*312500000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165783157 312500000 21870377133931 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1891884143/10000000000 : ℝ)^1097 ≤ (712297787751/6250000000000 : ℝ)^841 := by
    have hnat : (1891884143 : ℕ)^1097*6250000000000^841 ≤ 712297787751^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891884143 10000000000 712297787751 6250000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352262821/2500000000 : ℝ)^1097 ≤ (44862481118927/100000000000000 : ℝ)^841 := by
    have hnat : (1352262821 : ℕ)^1097*100000000000000^841 ≤ 44862481118927^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352262821 2500000000 44862481118927 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165783157/312500000 : ℝ), (-1891884143/10000000000 : ℝ), (1352262821/2500000000 : ℝ)] ![(21870377133931/50000000000000 : ℝ), (712297787751/6250000000000 : ℝ), (44862481118927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165783157/312500000 : ℝ)|^1097 ≤ (21870377133931/50000000000000 : ℝ)^841
        have hw : |(165783157/312500000 : ℝ)|=(165783157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1891884143/10000000000 : ℝ)|^1097 ≤ (712297787751/6250000000000 : ℝ)^841
        have hw : |(-1891884143/10000000000 : ℝ)|=(1891884143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352262821/2500000000 : ℝ)|^1097 ≤ (44862481118927/100000000000000 : ℝ)^841
        have hw : |(1352262821/2500000000 : ℝ)|=(1352262821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s4_6 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652530503/5000000000 : ℝ)*x 0 + (2704525643/5000000000 : ℝ)*x 1 + (-472971041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652530503/5000000000 : ℝ)^1097 ≤ (21870377037137/50000000000000 : ℝ)^841 := by
    have hnat : (2652530503 : ℕ)^1097*50000000000000^841 ≤ 21870377037137^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652530503 5000000000 21870377037137 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704525643/5000000000 : ℝ)^1097 ≤ (11215620285141/25000000000000 : ℝ)^841 := by
    have hnat : (2704525643 : ℕ)^1097*25000000000000^841 ≤ 11215620285141^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704525643 5000000000 11215620285141 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472971041/2500000000 : ℝ)^1097 ≤ (2849191192257/25000000000000 : ℝ)^841 := by
    have hnat : (472971041 : ℕ)^1097*25000000000000^841 ≤ 2849191192257^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472971041 2500000000 2849191192257 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652530503/5000000000 : ℝ), (2704525643/5000000000 : ℝ), (-472971041/2500000000 : ℝ)] ![(21870377037137/50000000000000 : ℝ), (11215620285141/25000000000000 : ℝ), (2849191192257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652530503/5000000000 : ℝ)|^1097 ≤ (21870377037137/50000000000000 : ℝ)^841
        have hw : |(2652530503/5000000000 : ℝ)|=(2652530503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704525643/5000000000 : ℝ)|^1097 ≤ (11215620285141/25000000000000 : ℝ)^841
        have hw : |(2704525643/5000000000 : ℝ)|=(2704525643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-472971041/2500000000 : ℝ)|^1097 ≤ (2849191192257/25000000000000 : ℝ)^841
        have hw : |(-472971041/2500000000 : ℝ)|=(472971041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s4_7 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1076138637/2500000000 : ℝ)*x 0 + (2241951999/5000000000 : ℝ)*x 1 + (516467281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076138637/2500000000 : ℝ)^1097 ≤ (33303980116389/100000000000000 : ℝ)^841 := by
    have hnat : (1076138637 : ℕ)^1097*100000000000000^841 ≤ 33303980116389^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076138637 2500000000 33303980116389 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241951999/5000000000 : ℝ)^1097 ≤ (8781337304917/25000000000000 : ℝ)^841 := by
    have hnat : (2241951999 : ℕ)^1097*25000000000000^841 ≤ 8781337304917^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241951999 5000000000 8781337304917 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516467281/1250000000 : ℝ)^1097 ≤ (15785335321753/50000000000000 : ℝ)^841 := by
    have hnat : (516467281 : ℕ)^1097*50000000000000^841 ≤ 15785335321753^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516467281 1250000000 15785335321753 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076138637/2500000000 : ℝ), (2241951999/5000000000 : ℝ), (516467281/1250000000 : ℝ)] ![(33303980116389/100000000000000 : ℝ), (8781337304917/25000000000000 : ℝ), (15785335321753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076138637/2500000000 : ℝ)|^1097 ≤ (33303980116389/100000000000000 : ℝ)^841
        have hw : |(1076138637/2500000000 : ℝ)|=(1076138637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241951999/5000000000 : ℝ)|^1097 ≤ (8781337304917/25000000000000 : ℝ)^841
        have hw : |(2241951999/5000000000 : ℝ)|=(2241951999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516467281/1250000000 : ℝ)|^1097 ≤ (15785335321753/50000000000000 : ℝ)^841
        have hw : |(516467281/1250000000 : ℝ)|=(516467281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1428_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7393/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14947/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14947/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14947/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5579/50000 : ℝ) ^ (4387/1024 : ℝ) ≤ (4155840022615287/50000000000000000000 : ℝ) := by
    have hpowers : (5579/50000 : ℝ)^4387 ≤ (4155840022615287/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5579 : ℕ)^4387*50000000000000000000^1024 ≤ 4155840022615287^1024*50000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5579 50000 4155840022615287 50000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5579/50000 : ℝ)) (X := (4155840022615287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14947/100000 : ℝ) ^ (4387/1024 : ℝ) ≤ (1817695696120629/6250000000000000000 : ℝ) := by
    have hpowers : (14947/100000 : ℝ)^4387 ≤ (1817695696120629/6250000000000000000 : ℝ)^1024 := by
      have hnat : (14947 : ℕ)^4387*6250000000000000000^1024 ≤ 1817695696120629^1024*100000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14947 100000 1817695696120629 6250000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14947/100000 : ℝ)) (X := (1817695696120629/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004155840022615287/25000000000000000000 : ℝ) ≤ (2000077598524029/2000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (25004155840022615287/25000000000000000000 : ℝ)^1024 ≤ (2000077598524029/2000000000000000 : ℝ)^4387 := by
      have hnat : (25004155840022615287 : ℕ)^1024*2000000000000000^4387 ≤ 2000077598524029^4387*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004155840022615287 25000000000000000000 2000077598524029 2000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000077598524029/2000000000000000 : ℝ)) (X := (25004155840022615287/25000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018697405591580319/50000000000000000000 : ℝ) ≤ (10000872733060917/10000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50018697405591580319/50000000000000000000 : ℝ)^1024 ≤ (10000872733060917/10000000000000000 : ℝ)^4387 := by
      have hnat : (50018697405591580319 : ℕ)^1024*10000000000000000^4387 ≤ 10000872733060917^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018697405591580319 50000000000000000000 10000872733060917 10000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000872733060917/10000000000000000 : ℝ)) (X := (50018697405591580319/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126817695696120629/3125000000000000000 : ℝ) ≤ (10001357473501689/10000000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (3126817695696120629/3125000000000000000 : ℝ)^1024 ≤ (10001357473501689/10000000000000000 : ℝ)^4387 := by
      have hnat : (3126817695696120629 : ℕ)^1024*10000000000000000^4387 ≤ 10001357473501689^4387*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126817695696120629 3125000000000000000 10001357473501689 10000000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001357473501689/10000000000000000 : ℝ)) (X := (3126817695696120629/3125000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4155840022615287/50000000000000000000 : ℝ) ≤ ((12626884212120487151/12630000000000000000 : ℝ)+2*(40395036731/31575000000000 : ℝ)*(5579/50000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (12626884212120487151/12630000000000000000 : ℝ)+2*(40395036731/31575000000000 : ℝ)*(5579/50000 : ℝ)=(2000077598524029/2000000000000000 : ℝ) by norm_num, show 1+2*(4155840022615287/50000000000000000000 : ℝ)=(25004155840022615287/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1817695696120629/6250000000000000000 : ℝ)+(4155840022615287/50000000000000000000 : ℝ) ≤ ((12626884212120487151/12630000000000000000 : ℝ)+(40395036731/31575000000000 : ℝ)*((14947/100000 : ℝ)+(5579/50000 : ℝ)))^(4387/1024 : ℝ) := by
    rw [show (12626884212120487151/12630000000000000000 : ℝ)+(40395036731/31575000000000 : ℝ)*((14947/100000 : ℝ)+(5579/50000 : ℝ))=(10000872733060917/10000000000000000 : ℝ) by norm_num, show 1+(1817695696120629/6250000000000000000 : ℝ)+(4155840022615287/50000000000000000000 : ℝ)=(50018697405591580319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1817695696120629/6250000000000000000 : ℝ) ≤ ((12626884212120487151/12630000000000000000 : ℝ)+2*(40395036731/31575000000000 : ℝ)*(14947/100000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (12626884212120487151/12630000000000000000 : ℝ)+2*(40395036731/31575000000000 : ℝ)*(14947/100000 : ℝ)=(10001357473501689/10000000000000000 : ℝ) by norm_num, show 1+2*(1817695696120629/6250000000000000000 : ℝ)=(3126817695696120629/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12626884212120487151/12630000000000000000 : ℝ)*(X 1 0+X 2 0)+(40395036731/31575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (14947/100000 : ℝ)) (c := (12626884212120487151/12630000000000000000 : ℝ)) (alpha := (40395036731/31575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12626884212120487151/12630000000000000000 : ℝ)*(X 0 1+X 2 1)+(40395036731/31575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (14947/100000 : ℝ)) (c := (12626884212120487151/12630000000000000000 : ℝ)) (alpha := (40395036731/31575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12626884212120487151/12630000000000000000 : ℝ)*(X 0 2+X 1 2)+(40395036731/31575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (14947/100000 : ℝ)) (c := (12626884212120487151/12630000000000000000 : ℝ)) (alpha := (40395036731/31575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1971785649/10000000000 : ℝ)*X 0 0+(2704827987/5000000000 : ℝ)*X 0 1+(2622800911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347706111/10000000000 : ℝ)*X 1 0+(-205533363/1000000000 : ℝ)*X 1 1+(5245601993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167115811/312500000 : ℝ)*X 2 0+(2622801117/5000000000 : ℝ)*X 2 1+(-2055333523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152264429/5000000000 : ℝ)*X 0 0+(4130430933/10000000000 : ℝ)*X 0 1+(4485204419/10000000000 : ℝ)*X 0 2+(2152264429/5000000000 : ℝ)*X 1 0+(4130430933/10000000000 : ℝ)*X 1 1+(4485204419/10000000000 : ℝ)*X 1 2+(2152264429/5000000000 : ℝ)*X 2 0+(4130430933/10000000000 : ℝ)*X 2 1+(4485204419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98589883/500000000 : ℝ)*X 0 0+(5246203277/10000000000 : ℝ)*X 0 1+(216362051/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165783157/312500000 : ℝ)*X 1 0+(-1891884143/10000000000 : ℝ)*X 1 1+(1352262821/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652530503/5000000000 : ℝ)*X 2 0+(2704525643/5000000000 : ℝ)*X 2 1+(-472971041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1076138637/2500000000 : ℝ)*X 0 0+(2241951999/5000000000 : ℝ)*X 0 1+(516467281/1250000000 : ℝ)*X 0 2+(1076138637/2500000000 : ℝ)*X 1 0+(2241951999/5000000000 : ℝ)*X 1 1+(516467281/1250000000 : ℝ)*X 1 2+(1076138637/2500000000 : ℝ)*X 2 0+(2241951999/5000000000 : ℝ)*X 2 1+(516467281/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (433022451592608692965636223/105250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10831113/12500000000000 : ℝ)*(base19) + (15241611/50000000000000 : ℝ)*(lower2) + (18468777/25000000000000 : ℝ)*(lower4) + (10953217/10000000000000 : ℝ)*(upper5) + (4457136275005727/100000000000000 : ℝ)*(major0) + (4457136275005727/100000000000000 : ℝ)*(major1) + (4457136275005727/100000000000000 : ℝ)*(major2) + (3047778424061079/50000000000000 : ℝ)*(sp0) + (6095565659056647/100000000000000 : ℝ)*(sp1) + (1523891857949107/25000000000000 : ℝ)*(sp2) + (352337964317589/12500000000000 : ℝ)*(sp3) + (1058367427/10000000000000 : ℝ)*(sp4) + (1686090877/100000000000000 : ℝ)*(sp5) + (1266533389/100000000000000 : ℝ)*(sp7) + (1409352490537051/50000000000000 : ℝ)*(f.failure) + (1523891857949107/25000000000000 : ℝ)*(f.sum) + (10427257905029/3157500000000000000000000000 : ℝ)*base65 + (3151660663329713777/1263000000000000000000000000000000 : ℝ)*base67 + (1537235048391713777/1263000000000000000000000000000000 : ℝ)*base69 + (13348453610550713777/1263000000000000000000000000000000 : ℝ)*base71 + (13629679469807/6315000000000000000000000000 : ℝ)*base74 + (7133502905772713777/1263000000000000000000000000000000 : ℝ)*base75 + (8402303631117713777/1263000000000000000000000000000000 : ℝ)*base77 + (2745242725280286223/1263000000000000000000000000000000 : ℝ)*base80 + (9043377067/6166992187500000000000000 : ℝ)*base81 + (11979897/2500000000000000000000 : ℝ)*base89 + (11979897/2500000000000000000000 : ℝ)*base91 + (11979897/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (630391838789554498378659841/52625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2045593167/100000000000000 : ℝ)*(base19) + (1096479273/50000000000000 : ℝ)*(base23) + (32079517/12500000000000 : ℝ)*(upper3) + (75906153/100000000000000 : ℝ)*(lower4) + (14073941/6250000000000 : ℝ)*(upper5) + (2245066231835809/50000000000000 : ℝ)*(major0) + (2245066231835809/50000000000000 : ℝ)*(major1) + (2245066231835809/50000000000000 : ℝ)*(major2) + (42093288801/100000000000000 : ℝ)*(sp1) + (22609070533/50000000000000 : ℝ)*(sp2) + (1535173167104271/25000000000000 : ℝ)*(sp4) + (1535162132383779/25000000000000 : ℝ)*(sp5) + (191895164291171/3125000000000 : ℝ)*(sp6) + (88736620613377/3125000000000 : ℝ)*(sp7) + (88736620613377/3125000000000 : ℝ)*(f.failure) + (1535173167104271/25000000000000 : ℝ)*(f.sum) + (8253831631/789375000000000000000000000 : ℝ)*base66 + (411223665867790159/631500000000000000000000000000000 : ℝ)*base67 + (5291335786959790159/631500000000000000000000000000000 : ℝ)*base69 + (497588588082709841/631500000000000000000000000000000 : ℝ)*base72 + (1550644516511/3157500000000000000000000000 : ℝ)*base73 + (13418054196794290159/631500000000000000000000000000000 : ℝ)*base75 + (3312225671493790159/631500000000000000000000000000000 : ℝ)*base77 + (9577429640775790159/631500000000000000000000000000000 : ℝ)*base79 + (1076810199521/3157500000000000000000000000 : ℝ)*base81 + (1856781/156250000000000000000 : ℝ)*base90 + (1856781/156250000000000000000 : ℝ)*base92 + (1856781/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1428_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14947/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1428_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1428_s5_0 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-985959301/5000000000 : ℝ)*x 0 + (5408454423/10000000000 : ℝ)*x 1 + (5123746/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985959301/5000000000 : ℝ)^1097 ≤ (2405932959203/20000000000000 : ℝ)^841 := by
    have hnat : (985959301 : ℕ)^1097*20000000000000^841 ≤ 2405932959203^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985959301 5000000000 2405932959203 20000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408454423/10000000000 : ℝ)^1097 ≤ (4485602400083/10000000000000 : ℝ)^841 := by
    have hnat : (5408454423 : ℕ)^1097*10000000000000^841 ≤ 4485602400083^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408454423 10000000000 4485602400083 10000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5123746/9765625 : ℝ)^1097 ≤ (10778577797373/25000000000000 : ℝ)^841 := by
    have hnat : (5123746 : ℕ)^1097*25000000000000^841 ≤ 10778577797373^841*9765625^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123746 9765625 10778577797373 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-985959301/5000000000 : ℝ), (5408454423/10000000000 : ℝ), (5123746/9765625 : ℝ)] ![(2405932959203/20000000000000 : ℝ), (4485602400083/10000000000000 : ℝ), (10778577797373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-985959301/5000000000 : ℝ)|^1097 ≤ (2405932959203/20000000000000 : ℝ)^841
        have hw : |(-985959301/5000000000 : ℝ)|=(985959301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408454423/10000000000 : ℝ)|^1097 ≤ (4485602400083/10000000000000 : ℝ)^841
        have hw : |(5408454423/10000000000 : ℝ)|=(5408454423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5123746/9765625 : ℝ)|^1097 ≤ (10778577797373/25000000000000 : ℝ)^841
        have hw : |(5123746/9765625 : ℝ)|=(5123746/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s5_1 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668424573/1250000000 : ℝ)*x 0 + (-32097911/156250000 : ℝ)*x 1 + (5246715717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668424573/1250000000 : ℝ)^1097 ≤ (44196621127813/100000000000000 : ℝ)^841 := by
    have hnat : (668424573 : ℕ)^1097*100000000000000^841 ≤ 44196621127813^841*1250000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668424573 1250000000 44196621127813 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32097911/156250000 : ℝ)^1097 ≤ (396533427127/3125000000000 : ℝ)^841 := by
    have hnat : (32097911 : ℕ)^1097*3125000000000^841 ≤ 396533427127^841*156250000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32097911 156250000 396533427127 3125000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246715717/10000000000 : ℝ)^1097 ≤ (10778577296271/25000000000000 : ℝ)^841 := by
    have hnat : (5246715717 : ℕ)^1097*25000000000000^841 ≤ 10778577296271^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246715717 10000000000 10778577296271 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668424573/1250000000 : ℝ), (-32097911/156250000 : ℝ), (5246715717/10000000000 : ℝ)] ![(44196621127813/100000000000000 : ℝ), (396533427127/3125000000000 : ℝ), (10778577296271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668424573/1250000000 : ℝ)|^1097 ≤ (44196621127813/100000000000000 : ℝ)^841
        have hw : |(668424573/1250000000 : ℝ)|=(668424573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32097911/156250000 : ℝ)|^1097 ≤ (396533427127/3125000000000 : ℝ)^841
        have hw : |(-32097911/156250000 : ℝ)|=(32097911/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246715717/10000000000 : ℝ)|^1097 ≤ (10778577296271/25000000000000 : ℝ)^841
        have hw : |(5246715717/10000000000 : ℝ)|=(5246715717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s5_2 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069479299/2000000000 : ℝ)*x 0 + (5246715909/10000000000 : ℝ)*x 1 + (-2054266169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069479299/2000000000 : ℝ)^1097 ≤ (44196620168307/100000000000000 : ℝ)^841 := by
    have hnat : (1069479299 : ℕ)^1097*100000000000000^841 ≤ 44196620168307^841*2000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069479299 2000000000 44196620168307 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246715909/10000000000 : ℝ)^1097 ≤ (21557155621543/50000000000000 : ℝ)^841 := by
    have hnat : (5246715909 : ℕ)^1097*50000000000000^841 ≤ 21557155621543^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246715909 10000000000 21557155621543 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054266169/10000000000 : ℝ)^1097 ≤ (1586133572543/12500000000000 : ℝ)^841 := by
    have hnat : (2054266169 : ℕ)^1097*12500000000000^841 ≤ 1586133572543^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054266169 10000000000 1586133572543 12500000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069479299/2000000000 : ℝ), (5246715909/10000000000 : ℝ), (-2054266169/10000000000 : ℝ)] ![(44196620168307/100000000000000 : ℝ), (21557155621543/50000000000000 : ℝ), (1586133572543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069479299/2000000000 : ℝ)|^1097 ≤ (44196620168307/100000000000000 : ℝ)^841
        have hw : |(1069479299/2000000000 : ℝ)|=(1069479299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246715909/10000000000 : ℝ)|^1097 ≤ (21557155621543/50000000000000 : ℝ)^841
        have hw : |(5246715909/10000000000 : ℝ)|=(5246715909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054266169/10000000000 : ℝ)|^1097 ≤ (1586133572543/12500000000000 : ℝ)^841
        have hw : |(-2054266169/10000000000 : ℝ)|=(2054266169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s5_3 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2152305463/5000000000 : ℝ)*x 0 + (4132924487/10000000000 : ℝ)*x 1 + (1120672787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152305463/5000000000 : ℝ)^1097 ≤ (33304549086019/100000000000000 : ℝ)^841 := by
    have hnat : (2152305463 : ℕ)^1097*100000000000000^841 ≤ 33304549086019^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152305463 5000000000 33304549086019 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4132924487/10000000000 : ℝ)^1097 ≤ (31582494327467/100000000000000 : ℝ)^841 := by
    have hnat : (4132924487 : ℕ)^1097*100000000000000^841 ≤ 31582494327467^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132924487 10000000000 31582494327467 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120672787/2500000000 : ℝ)^1097 ≤ (35112956569543/100000000000000 : ℝ)^841 := by
    have hnat : (1120672787 : ℕ)^1097*100000000000000^841 ≤ 35112956569543^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120672787 2500000000 35112956569543 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152305463/5000000000 : ℝ), (4132924487/10000000000 : ℝ), (1120672787/2500000000 : ℝ)] ![(33304549086019/100000000000000 : ℝ), (31582494327467/100000000000000 : ℝ), (35112956569543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152305463/5000000000 : ℝ)|^1097 ≤ (33304549086019/100000000000000 : ℝ)^841
        have hw : |(2152305463/5000000000 : ℝ)|=(2152305463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4132924487/10000000000 : ℝ)|^1097 ≤ (31582494327467/100000000000000 : ℝ)^841
        have hw : |(4132924487/10000000000 : ℝ)|=(4132924487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120672787/2500000000 : ℝ)|^1097 ≤ (35112956569543/100000000000000 : ℝ)^841
        have hw : |(1120672787/2500000000 : ℝ)|=(1120672787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s5_4 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971929859/10000000000 : ℝ)*x 0 + (2623650231/5000000000 : ℝ)*x 1 + (5407866943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971929859/10000000000 : ℝ)^1097 ≤ (6014877186683/50000000000000 : ℝ)^841 := by
    have hnat : (1971929859 : ℕ)^1097*50000000000000^841 ≤ 6014877186683^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971929859 10000000000 6014877186683 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623650231/5000000000 : ℝ)^1097 ≤ (21560288516237/50000000000000 : ℝ)^841 := by
    have hnat : (2623650231 : ℕ)^1097*50000000000000^841 ≤ 21560288516237^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623650231 5000000000 21560288516237 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407866943/10000000000 : ℝ)^1097 ≤ (22424834291273/50000000000000 : ℝ)^841 := by
    have hnat : (5407866943 : ℕ)^1097*50000000000000^841 ≤ 22424834291273^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407866943 10000000000 22424834291273 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971929859/10000000000 : ℝ), (2623650231/5000000000 : ℝ), (5407866943/10000000000 : ℝ)] ![(6014877186683/50000000000000 : ℝ), (21560288516237/50000000000000 : ℝ), (22424834291273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971929859/10000000000 : ℝ)|^1097 ≤ (6014877186683/50000000000000 : ℝ)^841
        have hw : |(-1971929859/10000000000 : ℝ)|=(1971929859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623650231/5000000000 : ℝ)|^1097 ≤ (21560288516237/50000000000000 : ℝ)^841
        have hw : |(2623650231/5000000000 : ℝ)|=(2623650231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407866943/10000000000 : ℝ)|^1097 ≤ (22424834291273/50000000000000 : ℝ)^841
        have hw : |(5407866943/10000000000 : ℝ)|=(5407866943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s5_5 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652676489/5000000000 : ℝ)*x 0 + (-94655753/500000000 : ℝ)*x 1 + (2703933443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652676489/5000000000 : ℝ)^1097 ≤ (43743894231241/100000000000000 : ℝ)^841 := by
    have hnat : (2652676489 : ℕ)^1097*100000000000000^841 ≤ 43743894231241^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652676489 5000000000 43743894231241 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94655753/500000000 : ℝ)^1097 ≤ (712902361739/6250000000000 : ℝ)^841 := by
    have hnat : (94655753 : ℕ)^1097*6250000000000^841 ≤ 712902361739^841*500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94655753 500000000 712902361739 6250000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703933443/5000000000 : ℝ)^1097 ≤ (11212416991481/25000000000000 : ℝ)^841 := by
    have hnat : (2703933443 : ℕ)^1097*25000000000000^841 ≤ 11212416991481^841*5000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703933443 5000000000 11212416991481 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652676489/5000000000 : ℝ), (-94655753/500000000 : ℝ), (2703933443/5000000000 : ℝ)] ![(43743894231241/100000000000000 : ℝ), (712902361739/6250000000000 : ℝ), (11212416991481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652676489/5000000000 : ℝ)|^1097 ≤ (43743894231241/100000000000000 : ℝ)^841
        have hw : |(2652676489/5000000000 : ℝ)|=(2652676489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-94655753/500000000 : ℝ)|^1097 ≤ (712902361739/6250000000000 : ℝ)^841
        have hw : |(-94655753/500000000 : ℝ)|=(94655753/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703933443/5000000000 : ℝ)|^1097 ≤ (11212416991481/25000000000000 : ℝ)^841
        have hw : |(2703933443/5000000000 : ℝ)|=(2703933443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s5_6 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305353459/10000000000 : ℝ)*x 0 + (540786667/1000000000 : ℝ)*x 1 + (-1893114699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305353459/10000000000 : ℝ)^1097 ≤ (10935974851109/25000000000000 : ℝ)^841 := by
    have hnat : (5305353459 : ℕ)^1097*25000000000000^841 ≤ 10935974851109^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305353459 10000000000 10935974851109 25000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540786667/1000000000 : ℝ)^1097 ≤ (44849665629253/100000000000000 : ℝ)^841 := by
    have hnat : (540786667 : ℕ)^1097*100000000000000^841 ≤ 44849665629253^841*1000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540786667 1000000000 44849665629253 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893114699/10000000000 : ℝ)^1097 ≤ (5703217475309/50000000000000 : ℝ)^841 := by
    have hnat : (1893114699 : ℕ)^1097*50000000000000^841 ≤ 5703217475309^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893114699 10000000000 5703217475309 50000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305353459/10000000000 : ℝ), (540786667/1000000000 : ℝ), (-1893114699/10000000000 : ℝ)] ![(10935974851109/25000000000000 : ℝ), (44849665629253/100000000000000 : ℝ), (5703217475309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305353459/10000000000 : ℝ)|^1097 ≤ (10935974851109/25000000000000 : ℝ)^841
        have hw : |(5305353459/10000000000 : ℝ)|=(5305353459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540786667/1000000000 : ℝ)|^1097 ≤ (44849665629253/100000000000000 : ℝ)^841
        have hw : |(540786667/1000000000 : ℝ)|=(540786667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893114699/10000000000 : ℝ)|^1097 ≤ (5703217475309/50000000000000 : ℝ)^841
        have hw : |(-1893114699/10000000000 : ℝ)|=(1893114699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1428_s5_7 (p : ℝ) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1076158953/2500000000 : ℝ)*x 0 + (4481426809/10000000000 : ℝ)*x 1 + (413419517/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076158953/2500000000 : ℝ)^1097 ≤ (33304800237513/100000000000000 : ℝ)^841 := by
    have hnat : (1076158953 : ℕ)^1097*100000000000000^841 ≤ 33304800237513^841*2500000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076158953 2500000000 33304800237513 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481426809/10000000000 : ℝ)^1097 ≤ (35100038901999/100000000000000 : ℝ)^841 := by
    have hnat : (4481426809 : ℕ)^1097*100000000000000^841 ≤ 35100038901999^841*10000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481426809 10000000000 35100038901999 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413419517/1000000000 : ℝ)^1097 ≤ (31595160842083/100000000000000 : ℝ)^841 := by
    have hnat : (413419517 : ℕ)^1097*100000000000000^841 ≤ 31595160842083^841*1000000000^1097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413419517 1000000000 31595160842083 100000000000000 1097 841 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1097/256 : ℝ)) 1097 841 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076158953/2500000000 : ℝ), (4481426809/10000000000 : ℝ), (413419517/1000000000 : ℝ)] ![(33304800237513/100000000000000 : ℝ), (35100038901999/100000000000000 : ℝ), (31595160842083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076158953/2500000000 : ℝ)|^1097 ≤ (33304800237513/100000000000000 : ℝ)^841
        have hw : |(1076158953/2500000000 : ℝ)|=(1076158953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481426809/10000000000 : ℝ)|^1097 ≤ (35100038901999/100000000000000 : ℝ)^841
        have hw : |(4481426809/10000000000 : ℝ)|=(4481426809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413419517/1000000000 : ℝ)|^1097 ≤ (31595160842083/100000000000000 : ℝ)^841
        have hw : |(413419517/1000000000 : ℝ)|=(413419517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1428_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5667/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11311/100000 : ℝ) ^ (4387/1024 : ℝ) ≤ (2202765312186903/25000000000000000000 : ℝ) := by
    have hpowers : (11311/100000 : ℝ)^4387 ≤ (2202765312186903/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11311 : ℕ)^4387*25000000000000000000^1024 ≤ 2202765312186903^1024*100000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11311 100000 2202765312186903 25000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11311/100000 : ℝ)) (X := (2202765312186903/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7393/50000 : ℝ) ^ (4387/1024 : ℝ) ≤ (27764588382435591/100000000000000000000 : ℝ) := by
    have hpowers : (7393/50000 : ℝ)^4387 ≤ (27764588382435591/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7393 : ℕ)^4387*100000000000000000000^1024 ≤ 27764588382435591^1024*50000^4387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7393 50000 27764588382435591 100000000000000000000 4387 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7393/50000 : ℝ)) (X := (27764588382435591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502202765312186903/12500000000000000000 : ℝ) ≤ (39064106649861/39062500000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (12502202765312186903/12500000000000000000 : ℝ)^1024 ≤ (39064106649861/39062500000000 : ℝ)^4387 := by
      have hnat : (12502202765312186903 : ℕ)^1024*39062500000000^4387 ≤ 39064106649861^4387*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502202765312186903 12500000000000000000 39064106649861 39062500000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39064106649861/39062500000000 : ℝ)) (X := (12502202765312186903/12500000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036575649631183203/100000000000000000000 : ℝ) ≤ (200017072357283/200000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (100036575649631183203/100000000000000000000 : ℝ)^1024 ≤ (200017072357283/200000000000000 : ℝ)^4387 := by
      have hnat : (100036575649631183203 : ℕ)^1024*200000000000000^4387 ≤ 200017072357283^4387*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036575649631183203 100000000000000000000 200017072357283 200000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200017072357283/200000000000000 : ℝ)) (X := (100036575649631183203/100000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027764588382435591/50000000000000000000 : ℝ) ≤ (2500323983340971/2500000000000000 : ℝ) ^ (4387/1024 : ℝ) := by
    have hpowers : (50027764588382435591/50000000000000000000 : ℝ)^1024 ≤ (2500323983340971/2500000000000000 : ℝ)^4387 := by
      have hnat : (50027764588382435591 : ℕ)^1024*2500000000000000^4387 ≤ 2500323983340971^4387*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027764588382435591 50000000000000000000 2500323983340971 2500000000000000 1024 4387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500323983340971/2500000000000000 : ℝ)) (X := (50027764588382435591/50000000000000000000 : ℝ)) (by norm_num) 4387 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2202765312186903/25000000000000000000 : ℝ) ≤ ((8685355803620340763/8687500000000000000 : ℝ)+2*(221157749867/173750000000000 : ℝ)*(11311/100000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (8685355803620340763/8687500000000000000 : ℝ)+2*(221157749867/173750000000000 : ℝ)*(11311/100000 : ℝ)=(39064106649861/39062500000000 : ℝ) by norm_num, show 1+2*(2202765312186903/25000000000000000000 : ℝ)=(12502202765312186903/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27764588382435591/100000000000000000000 : ℝ)+(2202765312186903/25000000000000000000 : ℝ) ≤ ((8685355803620340763/8687500000000000000 : ℝ)+(221157749867/173750000000000 : ℝ)*((7393/50000 : ℝ)+(11311/100000 : ℝ)))^(4387/1024 : ℝ) := by
    rw [show (8685355803620340763/8687500000000000000 : ℝ)+(221157749867/173750000000000 : ℝ)*((7393/50000 : ℝ)+(11311/100000 : ℝ))=(200017072357283/200000000000000 : ℝ) by norm_num, show 1+(27764588382435591/100000000000000000000 : ℝ)+(2202765312186903/25000000000000000000 : ℝ)=(100036575649631183203/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27764588382435591/100000000000000000000 : ℝ) ≤ ((8685355803620340763/8687500000000000000 : ℝ)+2*(221157749867/173750000000000 : ℝ)*(7393/50000 : ℝ))^(4387/1024 : ℝ) := by
    rw [show (8685355803620340763/8687500000000000000 : ℝ)+2*(221157749867/173750000000000 : ℝ)*(7393/50000 : ℝ)=(2500323983340971/2500000000000000 : ℝ) by norm_num, show 1+2*(27764588382435591/100000000000000000000 : ℝ)=(50027764588382435591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8685355803620340763/8687500000000000000 : ℝ)*(X 1 0+X 2 0)+(221157749867/173750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (8685355803620340763/8687500000000000000 : ℝ)) (alpha := (221157749867/173750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8685355803620340763/8687500000000000000 : ℝ)*(X 0 1+X 2 1)+(221157749867/173750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (8685355803620340763/8687500000000000000 : ℝ)) (alpha := (221157749867/173750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8685355803620340763/8687500000000000000 : ℝ)*(X 0 2+X 1 2)+(221157749867/173750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4387/1024 : ℝ)) (lo := (11311/100000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (8685355803620340763/8687500000000000000 : ℝ)) (alpha := (221157749867/173750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-985959301/5000000000 : ℝ)*X 0 0+(5408454423/10000000000 : ℝ)*X 0 1+(5123746/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668424573/1250000000 : ℝ)*X 1 0+(-32097911/156250000 : ℝ)*X 1 1+(5246715717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069479299/2000000000 : ℝ)*X 2 0+(5246715909/10000000000 : ℝ)*X 2 1+(-2054266169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152305463/5000000000 : ℝ)*X 0 0+(4132924487/10000000000 : ℝ)*X 0 1+(1120672787/2500000000 : ℝ)*X 0 2+(2152305463/5000000000 : ℝ)*X 1 0+(4132924487/10000000000 : ℝ)*X 1 1+(1120672787/2500000000 : ℝ)*X 1 2+(2152305463/5000000000 : ℝ)*X 2 0+(4132924487/10000000000 : ℝ)*X 2 1+(1120672787/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1971929859/10000000000 : ℝ)*X 0 0+(2623650231/5000000000 : ℝ)*X 0 1+(5407866943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652676489/5000000000 : ℝ)*X 1 0+(-94655753/500000000 : ℝ)*X 1 1+(2703933443/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305353459/10000000000 : ℝ)*X 2 0+(540786667/1000000000 : ℝ)*X 2 1+(-1893114699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1076158953/2500000000 : ℝ)*X 0 0+(4481426809/10000000000 : ℝ)*X 0 1+(413419517/1000000000 : ℝ)*X 0 2+(1076158953/2500000000 : ℝ)*X 1 0+(4481426809/10000000000 : ℝ)*X 1 1+(413419517/1000000000 : ℝ)*X 1 2+(1076158953/2500000000 : ℝ)*X 2 0+(4481426809/10000000000 : ℝ)*X 2 1+(413419517/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1428_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91688796192385599471123/8687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1846896051/100000000000000 : ℝ)*(base19) + (1646576131/100000000000000 : ℝ)*(base23) + (26045651/50000000000000 : ℝ)*(lower2) + (32359741/20000000000000 : ℝ)*(upper3) + (122972067/50000000000000 : ℝ)*(upper5) + (2260493601423533/50000000000000 : ℝ)*(major0) + (2260493601423533/50000000000000 : ℝ)*(major1) + (2260493601423533/50000000000000 : ℝ)*(major2) + (6182852313220911/100000000000000 : ℝ)*(sp0) + (6182887727236079/100000000000000 : ℝ)*(sp1) + (6182887927555999/100000000000000 : ℝ)*(sp2) + (714766810844757/25000000000000 : ℝ)*(sp3) + (37260911219/100000000000000 : ℝ)*(sp4) + (17236379429/100000000000000 : ℝ)*(sp7) + (357385559969807/12500000000000 : ℝ)*(f.failure) + (618288957413213/10000000000000 : ℝ)*(f.sum) + (17174940055431/17375000000000000000000000000 : ℝ)*base66 + (1428030391440425679/434375000000000000000000000000000 : ℝ)*base67 + (64095908787699321/434375000000000000000000000000000 : ℝ)*base70 + (396549536515425679/434375000000000000000000000000000 : ℝ)*base71 + (75664262651931/17375000000000000000000000000 : ℝ)*base74 + (6215606752218949321/434375000000000000000000000000000 : ℝ)*base76 + (4104734970643949321/434375000000000000000000000000000 : ℝ)*base78 + (2310695351315425679/434375000000000000000000000000000 : ℝ)*base79 + (5599845541681/17375000000000000000000000000 : ℝ)*base82 + (8174571/625000000000000000000 : ℝ)*base90 + (8174571/625000000000000000000 : ℝ)*base92 + (8174571/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (154525850360302404214718289/86875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100452179/20000000000000 : ℝ)*(base19) + (1527790423/100000000000000 : ℝ)*(base23) + (150452473/100000000000000 : ℝ)*(lower4) + (20276993/100000000000000 : ℝ)*(upper5) + (910787708064001/20000000000000 : ℝ)*(major0) + (910787708064001/20000000000000 : ℝ)*(major1) + (910787708064001/20000000000000 : ℝ)*(major2) + (135198187/20000000000000 : ℝ)*(sp0) + (39954569/312500000000 : ℝ)*(sp1) + (35158573591/100000000000000 : ℝ)*(sp2) + (6227953351061339/100000000000000 : ℝ)*(sp4) + (3113970369664649/50000000000000 : ℝ)*(sp5) + (311395867034413/5000000000000 : ℝ)*(sp6) + (719980748574309/25000000000000 : ℝ)*(sp7) + (719980748574309/25000000000000 : ℝ)*(f.failure) + (3113977013526137/50000000000000 : ℝ)*(f.sum) + (15098211948741/3475000000000000000000000000 : ℝ)*base66 + (1212474582139727237/173750000000000000000000000000000 : ℝ)*base68 + (944613773347772763/173750000000000000000000000000000 : ℝ)*base69 + (520950581028477237/173750000000000000000000000000000 : ℝ)*base72 + (1527796532583/1737500000000000000000000000 : ℝ)*base74 + (3728159929011522763/173750000000000000000000000000000 : ℝ)*base75 + (3900243802227237/173750000000000000000000000000000 : ℝ)*base78 + (1060888009819727237/173750000000000000000000000000000 : ℝ)*base80 + (888769940241/3475000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (114023/1250000000000000000000 : ℝ)*base89 + (114023/1250000000000000000000 : ℝ)*base91 + (114023/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1428_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1428_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1428_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15803/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1428_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1428_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1428_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4387/1024 : ℝ) ≤ p) (hpb : p ≤ (1097/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79063547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15803/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5181/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1428_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

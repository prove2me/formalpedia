-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1441_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:45.529703+00:00
-- url     : https://prove2.me/submissions/cdb93f70-096f-4d77-93e9-bbcb247467ab

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
theorem support_rectangle_w1441_s0_0 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1752039901/10000000000 : ℝ)*x 0 + (595524463/1000000000 : ℝ)*x 1 + (2416987203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1752039901/10000000000 : ℝ)^4401 ≤ (5165775983463/50000000000000 : ℝ)^3377 := by
    have hnat : (1752039901 : ℕ)^4401*50000000000000^3377 ≤ 5165775983463^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752039901 10000000000 5165775983463 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595524463/1000000000 : ℝ)^4401 ≤ (25445613835389/50000000000000 : ℝ)^3377 := by
    have hnat : (595524463 : ℕ)^4401*50000000000000^3377 ≤ 25445613835389^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595524463 1000000000 25445613835389 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2416987203/5000000000 : ℝ)^4401 ≤ (7755444068841/20000000000000 : ℝ)^3377 := by
    have hnat : (2416987203 : ℕ)^4401*20000000000000^3377 ≤ 7755444068841^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416987203 5000000000 7755444068841 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1752039901/10000000000 : ℝ), (595524463/1000000000 : ℝ), (2416987203/5000000000 : ℝ)] ![(5165775983463/50000000000000 : ℝ), (25445613835389/50000000000000 : ℝ), (7755444068841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1752039901/10000000000 : ℝ)|^4401 ≤ (5165775983463/50000000000000 : ℝ)^3377
        have hw : |(-1752039901/10000000000 : ℝ)|=(1752039901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(595524463/1000000000 : ℝ)|^4401 ≤ (25445613835389/50000000000000 : ℝ)^3377
        have hw : |(595524463/1000000000 : ℝ)|=(595524463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2416987203/5000000000 : ℝ)|^4401 ≤ (7755444068841/20000000000000 : ℝ)^3377
        have hw : |(2416987203/5000000000 : ℝ)|=(2416987203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s0_1 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2745382727/5000000000 : ℝ)*x 0 + (-2384917003/10000000000 : ℝ)*x 1 + (4833974591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2745382727/5000000000 : ℝ)^4401 ≤ (45780693693383/100000000000000 : ℝ)^3377 := by
    have hnat : (2745382727 : ℕ)^4401*100000000000000^3377 ≤ 45780693693383^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745382727 5000000000 45780693693383 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2384917003/10000000000 : ℝ)^4401 ≤ (3860521001783/25000000000000 : ℝ)^3377 := by
    have hnat : (2384917003 : ℕ)^4401*25000000000000^3377 ≤ 3860521001783^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384917003 10000000000 3860521001783 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4833974591/10000000000 : ℝ)^4401 ≤ (242357639239/625000000000 : ℝ)^3377 := by
    have hnat : (4833974591 : ℕ)^4401*625000000000^3377 ≤ 242357639239^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833974591 10000000000 242357639239 625000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2745382727/5000000000 : ℝ), (-2384917003/10000000000 : ℝ), (4833974591/10000000000 : ℝ)] ![(45780693693383/100000000000000 : ℝ), (3860521001783/25000000000000 : ℝ), (242357639239/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2745382727/5000000000 : ℝ)|^4401 ≤ (45780693693383/100000000000000 : ℝ)^3377
        have hw : |(2745382727/5000000000 : ℝ)|=(2745382727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2384917003/10000000000 : ℝ)|^4401 ≤ (3860521001783/25000000000000 : ℝ)^3377
        have hw : |(-2384917003/10000000000 : ℝ)|=(2384917003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4833974591/10000000000 : ℝ)|^4401 ≤ (242357639239/625000000000 : ℝ)^3377
        have hw : |(4833974591/10000000000 : ℝ)|=(4833974591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s0_2 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6863457/12500000 : ℝ)*x 0 + (4833974589/10000000000 : ℝ)*x 1 + (-1192458409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6863457/12500000 : ℝ)^4401 ≤ (45780695279819/100000000000000 : ℝ)^3377 := by
    have hnat : (6863457 : ℕ)^4401*100000000000000^3377 ≤ 45780695279819^3377*12500000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6863457 12500000 45780695279819 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4833974589/10000000000 : ℝ)^4401 ≤ (38777222257331/100000000000000 : ℝ)^3377 := by
    have hnat : (4833974589 : ℕ)^4401*100000000000000^3377 ≤ 38777222257331^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833974589 10000000000 38777222257331 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192458409/5000000000 : ℝ)^4401 ≤ (7721041223027/50000000000000 : ℝ)^3377 := by
    have hnat : (1192458409 : ℕ)^4401*50000000000000^3377 ≤ 7721041223027^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192458409 5000000000 7721041223027 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6863457/12500000 : ℝ), (4833974589/10000000000 : ℝ), (-1192458409/5000000000 : ℝ)] ![(45780695279819/100000000000000 : ℝ), (38777222257331/100000000000000 : ℝ), (7721041223027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6863457/12500000 : ℝ)|^4401 ≤ (45780695279819/100000000000000 : ℝ)^3377
        have hw : |(6863457/12500000 : ℝ)|=(6863457/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4833974589/10000000000 : ℝ)|^4401 ≤ (38777222257331/100000000000000 : ℝ)^3377
        have hw : |(4833974589/10000000000 : ℝ)|=(4833974589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1192458409/5000000000 : ℝ)|^4401 ≤ (7721041223027/50000000000000 : ℝ)^3377
        have hw : |(-1192458409/5000000000 : ℝ)|=(1192458409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s0_3 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83285687/200000000 : ℝ)*x 0 + (3103080567/10000000000 : ℝ)*x 1 + (221577257/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83285687/200000000 : ℝ)^4401 ≤ (31928202841517/100000000000000 : ℝ)^3377 := by
    have hnat : (83285687 : ℕ)^4401*100000000000000^3377 ≤ 31928202841517^3377*200000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83285687 200000000 31928202841517 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103080567/10000000000 : ℝ)^4401 ≤ (21761589757739/100000000000000 : ℝ)^3377 := by
    have hnat : (3103080567 : ℕ)^4401*100000000000000^3377 ≤ 21761589757739^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103080567 10000000000 21761589757739 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221577257/400000000 : ℝ)^4401 ≤ (11577551845271/25000000000000 : ℝ)^3377 := by
    have hnat : (221577257 : ℕ)^4401*25000000000000^3377 ≤ 11577551845271^3377*400000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221577257 400000000 11577551845271 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83285687/200000000 : ℝ), (3103080567/10000000000 : ℝ), (221577257/400000000 : ℝ)] ![(31928202841517/100000000000000 : ℝ), (21761589757739/100000000000000 : ℝ), (11577551845271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83285687/200000000 : ℝ)|^4401 ≤ (31928202841517/100000000000000 : ℝ)^3377
        have hw : |(83285687/200000000 : ℝ)|=(83285687/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103080567/10000000000 : ℝ)|^4401 ≤ (21761589757739/100000000000000 : ℝ)^3377
        have hw : |(3103080567/10000000000 : ℝ)|=(3103080567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(221577257/400000000 : ℝ)|^4401 ≤ (11577551845271/25000000000000 : ℝ)^3377
        have hw : |(221577257/400000000 : ℝ)|=(221577257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s0_4 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-351199969/2000000000 : ℝ)*x 0 + (2431318167/5000000000 : ℝ)*x 1 + (740694931/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351199969/2000000000 : ℝ)^4401 ≤ (10361994419847/100000000000000 : ℝ)^3377 := by
    have hnat : (351199969 : ℕ)^4401*100000000000000^3377 ≤ 10361994419847^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351199969 2000000000 10361994419847 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2431318167/5000000000 : ℝ)^4401 ≤ (19538564064229/50000000000000 : ℝ)^3377 := by
    have hnat : (2431318167 : ℕ)^4401*50000000000000^3377 ≤ 19538564064229^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431318167 5000000000 19538564064229 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (740694931/1250000000 : ℝ)^4401 ≤ (50560877434711/100000000000000 : ℝ)^3377 := by
    have hnat : (740694931 : ℕ)^4401*100000000000000^3377 ≤ 50560877434711^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740694931 1250000000 50560877434711 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351199969/2000000000 : ℝ), (2431318167/5000000000 : ℝ), (740694931/1250000000 : ℝ)] ![(10361994419847/100000000000000 : ℝ), (19538564064229/50000000000000 : ℝ), (50560877434711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351199969/2000000000 : ℝ)|^4401 ≤ (10361994419847/100000000000000 : ℝ)^3377
        have hw : |(-351199969/2000000000 : ℝ)|=(351199969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2431318167/5000000000 : ℝ)|^4401 ≤ (19538564064229/50000000000000 : ℝ)^3377
        have hw : |(2431318167/5000000000 : ℝ)|=(2431318167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(740694931/1250000000 : ℝ)|^4401 ≤ (50560877434711/100000000000000 : ℝ)^3377
        have hw : |(740694931/1250000000 : ℝ)|=(740694931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s0_5 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518467361/1000000000 : ℝ)*x 0 + (-646665989/5000000000 : ℝ)*x 1 + (1481389833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518467361/1000000000 : ℝ)^4401 ≤ (531039788967/1250000000000 : ℝ)^3377 := by
    have hnat : (518467361 : ℕ)^4401*1250000000000^3377 ≤ 531039788967^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518467361 1000000000 531039788967 1250000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (646665989/5000000000 : ℝ)^4401 ≤ (1738985178759/25000000000000 : ℝ)^3377 := by
    have hnat : (646665989 : ℕ)^4401*25000000000000^3377 ≤ 1738985178759^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646665989 5000000000 1738985178759 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1481389833/2500000000 : ℝ)^4401 ≤ (50560876144789/100000000000000 : ℝ)^3377 := by
    have hnat : (1481389833 : ℕ)^4401*100000000000000^3377 ≤ 50560876144789^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1481389833 2500000000 50560876144789 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518467361/1000000000 : ℝ), (-646665989/5000000000 : ℝ), (1481389833/2500000000 : ℝ)] ![(531039788967/1250000000000 : ℝ), (1738985178759/25000000000000 : ℝ), (50560876144789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518467361/1000000000 : ℝ)|^4401 ≤ (531039788967/1250000000000 : ℝ)^3377
        have hw : |(518467361/1000000000 : ℝ)|=(518467361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-646665989/5000000000 : ℝ)|^4401 ≤ (1738985178759/25000000000000 : ℝ)^3377
        have hw : |(-646665989/5000000000 : ℝ)|=(646665989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1481389833/2500000000 : ℝ)|^4401 ≤ (50560876144789/100000000000000 : ℝ)^3377
        have hw : |(1481389833/2500000000 : ℝ)|=(1481389833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s0_6 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184673599/10000000000 : ℝ)*x 0 + (2962779739/5000000000 : ℝ)*x 1 + (-323332941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184673599/10000000000 : ℝ)^4401 ≤ (8496636599979/20000000000000 : ℝ)^3377 := by
    have hnat : (5184673599 : ℕ)^4401*20000000000000^3377 ≤ 8496636599979^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184673599 10000000000 8496636599979 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2962779739/5000000000 : ℝ)^4401 ≤ (6320109721039/12500000000000 : ℝ)^3377 := by
    have hnat : (2962779739 : ℕ)^4401*12500000000000^3377 ≤ 6320109721039^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2962779739 5000000000 6320109721039 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323332941/2500000000 : ℝ)^4401 ≤ (278237568603/4000000000000 : ℝ)^3377 := by
    have hnat : (323332941 : ℕ)^4401*4000000000000^3377 ≤ 278237568603^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323332941 2500000000 278237568603 4000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184673599/10000000000 : ℝ), (2962779739/5000000000 : ℝ), (-323332941/2500000000 : ℝ)] ![(8496636599979/20000000000000 : ℝ), (6320109721039/12500000000000 : ℝ), (278237568603/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184673599/10000000000 : ℝ)|^4401 ≤ (8496636599979/20000000000000 : ℝ)^3377
        have hw : |(5184673599/10000000000 : ℝ)|=(5184673599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2962779739/5000000000 : ℝ)|^4401 ≤ (6320109721039/12500000000000 : ℝ)^3377
        have hw : |(2962779739/5000000000 : ℝ)|=(2962779739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-323332941/2500000000 : ℝ)|^4401 ≤ (278237568603/4000000000000 : ℝ)^3377
        have hw : |(-323332941/2500000000 : ℝ)|=(323332941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s0_7 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (417288943/1000000000 : ℝ)*x 0 + (1095430773/2000000000 : ℝ)*x 1 + (1583790933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417288943/1000000000 : ℝ)^4401 ≤ (3201421211773/10000000000000 : ℝ)^3377 := by
    have hnat : (417288943 : ℕ)^4401*10000000000000^3377 ≤ 3201421211773^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417288943 1000000000 3201421211773 10000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095430773/2000000000 : ℝ)^4401 ≤ (22816422880217/50000000000000 : ℝ)^3377 := by
    have hnat : (1095430773 : ℕ)^4401*50000000000000^3377 ≤ 22816422880217^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095430773 2000000000 22816422880217 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583790933/5000000000 : ℝ)^4401 ≤ (2794117763001/12500000000000 : ℝ)^3377 := by
    have hnat : (1583790933 : ℕ)^4401*12500000000000^3377 ≤ 2794117763001^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583790933 5000000000 2794117763001 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417288943/1000000000 : ℝ), (1095430773/2000000000 : ℝ), (1583790933/5000000000 : ℝ)] ![(3201421211773/10000000000000 : ℝ), (22816422880217/50000000000000 : ℝ), (2794117763001/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417288943/1000000000 : ℝ)|^4401 ≤ (3201421211773/10000000000000 : ℝ)^3377
        have hw : |(417288943/1000000000 : ℝ)|=(417288943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095430773/2000000000 : ℝ)|^4401 ≤ (22816422880217/50000000000000 : ℝ)^3377
        have hw : |(1095430773/2000000000 : ℝ)|=(1095430773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1583790933/5000000000 : ℝ)|^4401 ≤ (2794117763001/12500000000000 : ℝ)^3377
        have hw : |(1583790933/5000000000 : ℝ)|=(1583790933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1441_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (533/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1047/4000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (275/64 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^275 ≤ (0 : ℝ)^64 := by
      have hnat : (0 : ℕ)^275*1^64 ≤ 0^64*1^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (275/64 : ℝ) ≤ (390060093836720377/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^275 ≤ (390060093836720377/20000000000000000000 : ℝ)^64 := by
      have hnat : (2 : ℕ)^275*20000000000000000000^64 ≤ 390060093836720377^64*5^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 390060093836720377 20000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (390060093836720377/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (1 : ℝ)^64 ≤ (1 : ℝ)^275 := by
      have hnat : (1 : ℕ)^64*1^275 ≤ 1^275*1^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (20390060093836720377/20000000000000000000 : ℝ) ≤ (5022526529424717/5000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (20390060093836720377/20000000000000000000 : ℝ)^64 ≤ (5022526529424717/5000000000000000 : ℝ)^275 := by
      have hnat : (20390060093836720377 : ℕ)^64*5000000000000000^275 ≤ 5022526529424717^275*20000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20390060093836720377 20000000000000000000 5022526529424717 5000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5022526529424717/5000000000000000 : ℝ)) (X := (20390060093836720377/20000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (10390060093836720377/10000000000000000000 : ℝ) ≤ (2522526529424717/2500000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (10390060093836720377/10000000000000000000 : ℝ)^64 ≤ (2522526529424717/2500000000000000 : ℝ)^275 := by
      have hnat : (10390060093836720377 : ℕ)^64*2500000000000000^275 ≤ 2522526529424717^275*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10390060093836720377 10000000000000000000 2522526529424717 2500000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2522526529424717/2500000000000000 : ℝ)) (X := (10390060093836720377/10000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(22526529424717/2000000000000000 : ℝ)*(0 : ℝ))^(275/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(22526529424717/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(390060093836720377/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(22526529424717/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(275/64 : ℝ) := by
    rw [show (1 : ℝ)+(22526529424717/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5022526529424717/5000000000000000 : ℝ) by norm_num, show 1+(390060093836720377/20000000000000000000 : ℝ)+(0 : ℝ)=(20390060093836720377/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(390060093836720377/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(22526529424717/2000000000000000 : ℝ)*(2/5 : ℝ))^(275/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(22526529424717/2000000000000000 : ℝ)*(2/5 : ℝ)=(2522526529424717/2500000000000000 : ℝ) by norm_num, show 1+2*(390060093836720377/20000000000000000000 : ℝ)=(10390060093836720377/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(22526529424717/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22526529424717/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(22526529424717/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22526529424717/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(22526529424717/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22526529424717/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1752039901/10000000000 : ℝ)*X 0 0+(595524463/1000000000 : ℝ)*X 0 1+(2416987203/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2745382727/5000000000 : ℝ)*X 1 0+(-2384917003/10000000000 : ℝ)*X 1 1+(4833974591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((6863457/12500000 : ℝ)*X 2 0+(4833974589/10000000000 : ℝ)*X 2 1+(-1192458409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((83285687/200000000 : ℝ)*X 0 0+(3103080567/10000000000 : ℝ)*X 0 1+(221577257/400000000 : ℝ)*X 0 2+(83285687/200000000 : ℝ)*X 1 0+(3103080567/10000000000 : ℝ)*X 1 1+(221577257/400000000 : ℝ)*X 1 2+(83285687/200000000 : ℝ)*X 2 0+(3103080567/10000000000 : ℝ)*X 2 1+(221577257/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-351199969/2000000000 : ℝ)*X 0 0+(2431318167/5000000000 : ℝ)*X 0 1+(740694931/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518467361/1000000000 : ℝ)*X 1 0+(-646665989/5000000000 : ℝ)*X 1 1+(1481389833/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5184673599/10000000000 : ℝ)*X 2 0+(2962779739/5000000000 : ℝ)*X 2 1+(-323332941/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((417288943/1000000000 : ℝ)*X 0 0+(1095430773/2000000000 : ℝ)*X 0 1+(1583790933/5000000000 : ℝ)*X 0 2+(417288943/1000000000 : ℝ)*X 1 0+(1095430773/2000000000 : ℝ)*X 1 1+(1583790933/5000000000 : ℝ)*X 1 2+(417288943/1000000000 : ℝ)*X 2 0+(1095430773/2000000000 : ℝ)*X 2 1+(1583790933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7885444515701699910177/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1213693189/100000000000000 : ℝ)*(base19) + (18916207/1562500000000 : ℝ)*(base23) + (37223273/25000000000000 : ℝ)*(upper3) + (14698999/100000000000000 : ℝ)*(upper4) + (45512017/25000000000000 : ℝ)*(upper5) + (40697130416871/6250000000000 : ℝ)*(major0) + (40697130416871/6250000000000 : ℝ)*(major1) + (40697130416871/6250000000000 : ℝ)*(major2) + (111481207388533/12500000000000 : ℝ)*(sp0) + (11148162205877/1250000000000 : ℝ)*(sp1) + (445926489763051/50000000000000 : ℝ)*(sp2) + (16418073958971/4000000000000 : ℝ)*(sp3) + (906211017/20000000000000 : ℝ)*(sp4) + (491494857/25000000000000 : ℝ)*(sp7) + (410453814953703/100000000000000 : ℝ)*(f.failure) + (891854190163349/100000000000000 : ℝ)*(f.sum) + (14307279944257/6250000000000000000000000000 : ℝ)*base65 + (18970223013007/12500000000000000000000000000 : ℝ)*base67 + (48525911363007/12500000000000000000000000000 : ℝ)*base69 + (52015084575507/12500000000000000000000000000 : ℝ)*base71 + (2127307955743/6250000000000000000000000000 : ℝ)*base74 + (10770657663007/12500000000000000000000000000 : ℝ)*base75 + (20157897424493/12500000000000000000000000000 : ℝ)*base78 + (67019044086993/12500000000000000000000000000 : ℝ)*base80 + (16787139406757/6250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (19690611/5000000000000000000000 : ℝ)*base89 + (19690611/5000000000000000000000 : ℝ)*base91 + (19690611/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (165206639772330697815489/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5563613/1562500000000 : ℝ)*(base19) + (7835533/2000000000000 : ℝ)*(base23) + (3840811/12500000000000 : ℝ)*(base39) + (41371249/100000000000000 : ℝ)*(upper3) + (54594893/100000000000000 : ℝ)*(upper5) + (343445588805063/50000000000000 : ℝ)*(major0) + (343445588805063/50000000000000 : ℝ)*(major1) + (686891146883639/100000000000000 : ℝ)*(major2) + (425045161/50000000000000 : ℝ)*(sp1) + (979540349/100000000000000 : ℝ)*(sp2) + (11760020538217/1250000000000 : ℝ)*(sp4) + (940800436895807/100000000000000 : ℝ)*(sp5) + (29400009452089/3125000000000 : ℝ)*(sp6) + (216490313183759/50000000000000 : ℝ)*(sp7) + (216490313183759/50000000000000 : ℝ)*(f.failure) + (117600209222981/12500000000000 : ℝ)*(f.sum) + (43836280922099/40000000000000000000000000000 : ℝ)*base66 + (840465052494837/200000000000000000000000000000 : ℝ)*base68 + (244940260142171/100000000000000000000000000000 : ℝ)*base69 + (1868694830094837/200000000000000000000000000000 : ℝ)*base72 + (148884906357901/40000000000000000000000000000 : ℝ)*base73 + (728018934457829/100000000000000000000000000000 : ℝ)*base76 + (358550662257829/100000000000000000000000000000 : ℝ)*base78 + (496596550557829/100000000000000000000000000000 : ℝ)*base80 + (149497885242171/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (22189883/2500000000000000000000 : ℝ)*base89 + (22189883/2500000000000000000000 : ℝ)*base91 + (2810117/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1441_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (533/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1047/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1441_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1441_s1_0 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1922700931/10000000000 : ℝ)*x 0 + (2800223153/5000000000 : ℝ)*x 1 + (634918119/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922700931/10000000000 : ℝ)^4401 ≤ (11662023906849/100000000000000 : ℝ)^3377 := by
    have hnat : (1922700931 : ℕ)^4401*100000000000000^3377 ≤ 11662023906849^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922700931 10000000000 11662023906849 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2800223153/5000000000 : ℝ)^4401 ≤ (23488039437761/50000000000000 : ℝ)^3377 := by
    have hnat : (2800223153 : ℕ)^4401*50000000000000^3377 ≤ 23488039437761^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800223153 5000000000 23488039437761 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634918119/1250000000 : ℝ)^4401 ≤ (41361897199169/100000000000000 : ℝ)^3377 := by
    have hnat : (634918119 : ℕ)^4401*100000000000000^3377 ≤ 41361897199169^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634918119 1250000000 41361897199169 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1922700931/10000000000 : ℝ), (2800223153/5000000000 : ℝ), (634918119/1250000000 : ℝ)] ![(11662023906849/100000000000000 : ℝ), (23488039437761/50000000000000 : ℝ), (41361897199169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1922700931/10000000000 : ℝ)|^4401 ≤ (11662023906849/100000000000000 : ℝ)^3377
        have hw : |(-1922700931/10000000000 : ℝ)|=(1922700931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2800223153/5000000000 : ℝ)|^4401 ≤ (23488039437761/50000000000000 : ℝ)^3377
        have hw : |(2800223153/5000000000 : ℝ)|=(2800223153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634918119/1250000000 : ℝ)|^4401 ≤ (41361897199169/100000000000000 : ℝ)^3377
        have hw : |(634918119/1250000000 : ℝ)|=(634918119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s1_1 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395607019/10000000000 : ℝ)*x 0 + (-2198574827/10000000000 : ℝ)*x 1 + (2539673239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395607019/10000000000 : ℝ)^4401 ≤ (894988596719/2000000000000 : ℝ)^3377 := by
    have hnat : (5395607019 : ℕ)^4401*2000000000000^3377 ≤ 894988596719^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395607019 10000000000 894988596719 2000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198574827/10000000000 : ℝ)^4401 ≤ (13888656748241/100000000000000 : ℝ)^3377 := by
    have hnat : (2198574827 : ℕ)^4401*100000000000000^3377 ≤ 13888656748241^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198574827 10000000000 13888656748241 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539673239/5000000000 : ℝ)^4401 ≤ (41361913393671/100000000000000 : ℝ)^3377 := by
    have hnat : (2539673239 : ℕ)^4401*100000000000000^3377 ≤ 41361913393671^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539673239 5000000000 41361913393671 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395607019/10000000000 : ℝ), (-2198574827/10000000000 : ℝ), (2539673239/5000000000 : ℝ)] ![(894988596719/2000000000000 : ℝ), (13888656748241/100000000000000 : ℝ), (41361913393671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395607019/10000000000 : ℝ)|^4401 ≤ (894988596719/2000000000000 : ℝ)^3377
        have hw : |(5395607019/10000000000 : ℝ)|=(5395607019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198574827/10000000000 : ℝ)|^4401 ≤ (13888656748241/100000000000000 : ℝ)^3377
        have hw : |(-2198574827/10000000000 : ℝ)|=(2198574827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539673239/5000000000 : ℝ)|^4401 ≤ (41361913393671/100000000000000 : ℝ)^3377
        have hw : |(2539673239/5000000000 : ℝ)|=(2539673239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s1_2 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84306379/156250000 : ℝ)*x 0 + (1269836271/2500000000 : ℝ)*x 1 + (-2198575001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84306379/156250000 : ℝ)^4401 ≤ (44749443206129/100000000000000 : ℝ)^3377 := by
    have hnat : (84306379 : ℕ)^4401*100000000000000^3377 ≤ 44749443206129^3377*156250000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84306379 156250000 44749443206129 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269836271/2500000000 : ℝ)^4401 ≤ (10340474650001/25000000000000 : ℝ)^3377 := by
    have hnat : (1269836271 : ℕ)^4401*25000000000000^3377 ≤ 10340474650001^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269836271 2500000000 10340474650001 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198575001/10000000000 : ℝ)^4401 ≤ (13888658180721/100000000000000 : ℝ)^3377 := by
    have hnat : (2198575001 : ℕ)^4401*100000000000000^3377 ≤ 13888658180721^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198575001 10000000000 13888658180721 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84306379/156250000 : ℝ), (1269836271/2500000000 : ℝ), (-2198575001/10000000000 : ℝ)] ![(44749443206129/100000000000000 : ℝ), (10340474650001/25000000000000 : ℝ), (13888658180721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84306379/156250000 : ℝ)|^4401 ≤ (44749443206129/100000000000000 : ℝ)^3377
        have hw : |(84306379/156250000 : ℝ)|=(84306379/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269836271/2500000000 : ℝ)|^4401 ≤ (10340474650001/25000000000000 : ℝ)^3377
        have hw : |(1269836271/2500000000 : ℝ)|=(1269836271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2198575001/10000000000 : ℝ)|^4401 ≤ (13888658180721/100000000000000 : ℝ)^3377
        have hw : |(-2198575001/10000000000 : ℝ)|=(2198575001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s1_3 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854891369/2000000000 : ℝ)*x 0 + (3741620163/10000000000 : ℝ)*x 1 + (304618221/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854891369/2000000000 : ℝ)^4401 ≤ (33033440293861/100000000000000 : ℝ)^3377 := by
    have hnat : (854891369 : ℕ)^4401*100000000000000^3377 ≤ 33033440293861^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854891369 2000000000 33033440293861 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3741620163/10000000000 : ℝ)^4401 ≤ (3471439309721/12500000000000 : ℝ)^3377 := by
    have hnat : (3741620163 : ℕ)^4401*12500000000000^3377 ≤ 3471439309721^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3741620163 10000000000 3471439309721 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (304618221/625000000 : ℝ)^4401 ≤ (7839009043429/20000000000000 : ℝ)^3377 := by
    have hnat : (304618221 : ℕ)^4401*20000000000000^3377 ≤ 7839009043429^3377*625000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304618221 625000000 7839009043429 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854891369/2000000000 : ℝ), (3741620163/10000000000 : ℝ), (304618221/625000000 : ℝ)] ![(33033440293861/100000000000000 : ℝ), (3471439309721/12500000000000 : ℝ), (7839009043429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854891369/2000000000 : ℝ)|^4401 ≤ (33033440293861/100000000000000 : ℝ)^3377
        have hw : |(854891369/2000000000 : ℝ)|=(854891369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3741620163/10000000000 : ℝ)|^4401 ≤ (3471439309721/12500000000000 : ℝ)^3377
        have hw : |(3741620163/10000000000 : ℝ)|=(3741620163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(304618221/625000000 : ℝ)|^4401 ≤ (7839009043429/20000000000000 : ℝ)^3377
        have hw : |(304618221/625000000 : ℝ)|=(304618221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s1_4 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1923082921/10000000000 : ℝ)*x 0 + (8136637/16000000 : ℝ)*x 1 + (699286431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1923082921/10000000000 : ℝ)^4401 ≤ (11665043494033/100000000000000 : ℝ)^3377 := by
    have hnat : (1923082921 : ℕ)^4401*100000000000000^3377 ≤ 11665043494033^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923082921 10000000000 11665043494033 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8136637/16000000 : ℝ)^4401 ≤ (8285229482601/20000000000000 : ℝ)^3377 := by
    have hnat : (8136637 : ℕ)^4401*20000000000000^3377 ≤ 8285229482601^3377*16000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8136637 16000000 8285229482601 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (699286431/1250000000 : ℝ)^4401 ≤ (23454404541899/50000000000000 : ℝ)^3377 := by
    have hnat : (699286431 : ℕ)^4401*50000000000000^3377 ≤ 23454404541899^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699286431 1250000000 23454404541899 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1923082921/10000000000 : ℝ), (8136637/16000000 : ℝ), (699286431/1250000000 : ℝ)] ![(11665043494033/100000000000000 : ℝ), (8285229482601/20000000000000 : ℝ), (23454404541899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1923082921/10000000000 : ℝ)|^4401 ≤ (11665043494033/100000000000000 : ℝ)^3377
        have hw : |(-1923082921/10000000000 : ℝ)|=(1923082921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8136637/16000000 : ℝ)|^4401 ≤ (8285229482601/20000000000000 : ℝ)^3377
        have hw : |(8136637/16000000 : ℝ)|=(8136637/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(699286431/1250000000 : ℝ)|^4401 ≤ (23454404541899/50000000000000 : ℝ)^3377
        have hw : |(699286431/1250000000 : ℝ)|=(699286431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s1_5 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259337819/10000000000 : ℝ)*x 0 + (-1683629347/10000000000 : ℝ)*x 1 + (349643217/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259337819/10000000000 : ℝ)^4401 ≤ (21641115179343/50000000000000 : ℝ)^3377 := by
    have hnat : (5259337819 : ℕ)^4401*50000000000000^3377 ≤ 21641115179343^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259337819 10000000000 21641115179343 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1683629347/10000000000 : ℝ)^4401 ≤ (1961792056873/20000000000000 : ℝ)^3377 := by
    have hnat : (1683629347 : ℕ)^4401*20000000000000^3377 ≤ 1961792056873^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683629347 10000000000 1961792056873 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349643217/625000000 : ℝ)^4401 ≤ (46908809346063/100000000000000 : ℝ)^3377 := by
    have hnat : (349643217 : ℕ)^4401*100000000000000^3377 ≤ 46908809346063^3377*625000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349643217 625000000 46908809346063 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259337819/10000000000 : ℝ), (-1683629347/10000000000 : ℝ), (349643217/625000000 : ℝ)] ![(21641115179343/50000000000000 : ℝ), (1961792056873/20000000000000 : ℝ), (46908809346063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259337819/10000000000 : ℝ)|^4401 ≤ (21641115179343/50000000000000 : ℝ)^3377
        have hw : |(5259337819/10000000000 : ℝ)|=(5259337819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1683629347/10000000000 : ℝ)|^4401 ≤ (1961792056873/20000000000000 : ℝ)^3377
        have hw : |(-1683629347/10000000000 : ℝ)|=(1683629347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(349643217/625000000 : ℝ)|^4401 ≤ (46908809346063/100000000000000 : ℝ)^3377
        have hw : |(349643217/625000000 : ℝ)|=(349643217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s1_6 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259337743/10000000000 : ℝ)*x 0 + (699286429/1250000000 : ℝ)*x 1 + (-1683629511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259337743/10000000000 : ℝ)^4401 ≤ (43282229543583/100000000000000 : ℝ)^3377 := by
    have hnat : (5259337743 : ℕ)^4401*100000000000000^3377 ≤ 43282229543583^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259337743 10000000000 43282229543583 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (699286429/1250000000 : ℝ)^4401 ≤ (23454404454477/50000000000000 : ℝ)^3377 := by
    have hnat : (699286429 : ℕ)^4401*50000000000000^3377 ≤ 23454404454477^3377*1250000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699286429 1250000000 23454404454477 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1683629511/10000000000 : ℝ)^4401 ≤ (9808961529569/100000000000000 : ℝ)^3377 := by
    have hnat : (1683629511 : ℕ)^4401*100000000000000^3377 ≤ 9808961529569^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683629511 10000000000 9808961529569 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259337743/10000000000 : ℝ), (699286429/1250000000 : ℝ), (-1683629511/10000000000 : ℝ)] ![(43282229543583/100000000000000 : ℝ), (23454404454477/50000000000000 : ℝ), (9808961529569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259337743/10000000000 : ℝ)|^4401 ≤ (43282229543583/100000000000000 : ℝ)^3377
        have hw : |(5259337743/10000000000 : ℝ)|=(5259337743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(699286429/1250000000 : ℝ)|^4401 ≤ (23454404454477/50000000000000 : ℝ)^3377
        have hw : |(699286429/1250000000 : ℝ)|=(699286429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1683629511/10000000000 : ℝ)|^4401 ≤ (9808961529569/100000000000000 : ℝ)^3377
        have hw : |(-1683629511/10000000000 : ℝ)|=(1683629511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s1_7 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275287339/10000000000 : ℝ)*x 0 + (194429611/400000000 : ℝ)*x 1 + (3754991307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275287339/10000000000 : ℝ)^4401 ≤ (33041804841689/100000000000000 : ℝ)^3377 := by
    have hnat : (4275287339 : ℕ)^4401*100000000000000^3377 ≤ 33041804841689^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275287339 10000000000 33041804841689 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194429611/400000000 : ℝ)^4401 ≤ (3905727187419/10000000000000 : ℝ)^3377 := by
    have hnat : (194429611 : ℕ)^4401*10000000000000^3377 ≤ 3905727187419^3377*400000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194429611 400000000 3905727187419 10000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3754991307/10000000000 : ℝ)^4401 ≤ (558018465421/2000000000000 : ℝ)^3377 := by
    have hnat : (3754991307 : ℕ)^4401*2000000000000^3377 ≤ 558018465421^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3754991307 10000000000 558018465421 2000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275287339/10000000000 : ℝ), (194429611/400000000 : ℝ), (3754991307/10000000000 : ℝ)] ![(33041804841689/100000000000000 : ℝ), (3905727187419/10000000000000 : ℝ), (558018465421/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275287339/10000000000 : ℝ)|^4401 ≤ (33041804841689/100000000000000 : ℝ)^3377
        have hw : |(4275287339/10000000000 : ℝ)|=(4275287339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(194429611/400000000 : ℝ)|^4401 ≤ (3905727187419/10000000000000 : ℝ)^3377
        have hw : |(194429611/400000000 : ℝ)|=(194429611/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3754991307/10000000000 : ℝ)|^4401 ≤ (558018465421/2000000000000 : ℝ)^3377
        have hw : |(3754991307/10000000000 : ℝ)|=(3754991307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1441_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1047/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (533/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (31/400 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1047/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (533/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1047/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (533/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1047/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (533/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1047/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (533/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1047/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (533/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1047/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (533/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (533/25000 : ℝ) ^ (275/64 : ℝ) ≤ (823981601481/12500000000000000000 : ℝ) := by
    have hpowers : (533/25000 : ℝ)^275 ≤ (823981601481/12500000000000000000 : ℝ)^64 := by
      have hnat : (533 : ℕ)^275*12500000000000000000^64 ≤ 823981601481^64*25000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        533 25000 823981601481 12500000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (533/25000 : ℝ)) (X := (823981601481/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hpowhi : (1047/4000 : ℝ) ^ (275/64 : ℝ) ≤ (157652868418997253/50000000000000000000 : ℝ) := by
    have hpowers : (1047/4000 : ℝ)^275 ≤ (157652868418997253/50000000000000000000 : ℝ)^64 := by
      have hnat : (1047 : ℕ)^275*50000000000000000000^64 ≤ 157652868418997253^64*4000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1047 4000 157652868418997253 50000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1047/4000 : ℝ)) (X := (157652868418997253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000823981601481/6250000000000000000 : ℝ) ≤ (1000000030682077/1000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (6250000823981601481/6250000000000000000 : ℝ)^64 ≤ (1000000030682077/1000000000000000 : ℝ)^275 := by
      have hnat : (6250000823981601481 : ℕ)^64*1000000000000000^275 ≤ 1000000030682077^275*6250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000823981601481 6250000000000000000 1000000030682077 1000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000030682077/1000000000000000 : ℝ)) (X := (6250000823981601481/6250000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50157656164345403177/50000000000000000000 : ℝ) ≤ (5003664658818311/5000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (50157656164345403177/50000000000000000000 : ℝ)^64 ≤ (5003664658818311/5000000000000000 : ℝ)^275 := by
      have hnat : (50157656164345403177 : ℕ)^64*5000000000000000^275 ≤ 5003664658818311^275*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50157656164345403177 50000000000000000000 5003664658818311 5000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003664658818311/5000000000000000 : ℝ)) (X := (50157656164345403177/50000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25157652868418997253/25000000000000000000 : ℝ) ≤ (5007329164226237/5000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (25157652868418997253/25000000000000000000 : ℝ)^64 ≤ (5007329164226237/5000000000000000 : ℝ)^275 := by
      have hnat : (25157652868418997253 : ℕ)^64*5000000000000000^275 ≤ 5007329164226237^275*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25157652868418997253 25000000000000000000 5007329164226237 5000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007329164226237/5000000000000000 : ℝ)) (X := (25157652868418997253/25000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(823981601481/12500000000000000000 : ℝ) ≤ ((120199378237386490091/120215000000000000000 : ℝ)+2*(1832252703963/601075000000000 : ℝ)*(533/25000 : ℝ))^(275/64 : ℝ) := by
    rw [show (120199378237386490091/120215000000000000000 : ℝ)+2*(1832252703963/601075000000000 : ℝ)*(533/25000 : ℝ)=(1000000030682077/1000000000000000 : ℝ) by norm_num, show 1+2*(823981601481/12500000000000000000 : ℝ)=(6250000823981601481/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(157652868418997253/50000000000000000000 : ℝ)+(823981601481/12500000000000000000 : ℝ) ≤ ((120199378237386490091/120215000000000000000 : ℝ)+(1832252703963/601075000000000 : ℝ)*((1047/4000 : ℝ)+(533/25000 : ℝ)))^(275/64 : ℝ) := by
    rw [show (120199378237386490091/120215000000000000000 : ℝ)+(1832252703963/601075000000000 : ℝ)*((1047/4000 : ℝ)+(533/25000 : ℝ))=(5003664658818311/5000000000000000 : ℝ) by norm_num, show 1+(157652868418997253/50000000000000000000 : ℝ)+(823981601481/12500000000000000000 : ℝ)=(50157656164345403177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(157652868418997253/50000000000000000000 : ℝ) ≤ ((120199378237386490091/120215000000000000000 : ℝ)+2*(1832252703963/601075000000000 : ℝ)*(1047/4000 : ℝ))^(275/64 : ℝ) := by
    rw [show (120199378237386490091/120215000000000000000 : ℝ)+2*(1832252703963/601075000000000 : ℝ)*(1047/4000 : ℝ)=(5007329164226237/5000000000000000 : ℝ) by norm_num, show 1+2*(157652868418997253/50000000000000000000 : ℝ)=(25157652868418997253/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (120199378237386490091/120215000000000000000 : ℝ)*(X 1 0+X 2 0)+(1832252703963/601075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (533/25000 : ℝ)) (hi := (1047/4000 : ℝ)) (c := (120199378237386490091/120215000000000000000 : ℝ)) (alpha := (1832252703963/601075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (120199378237386490091/120215000000000000000 : ℝ)*(X 0 1+X 2 1)+(1832252703963/601075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (533/25000 : ℝ)) (hi := (1047/4000 : ℝ)) (c := (120199378237386490091/120215000000000000000 : ℝ)) (alpha := (1832252703963/601075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (120199378237386490091/120215000000000000000 : ℝ)*(X 0 2+X 1 2)+(1832252703963/601075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (533/25000 : ℝ)) (hi := (1047/4000 : ℝ)) (c := (120199378237386490091/120215000000000000000 : ℝ)) (alpha := (1832252703963/601075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1922700931/10000000000 : ℝ)*X 0 0+(2800223153/5000000000 : ℝ)*X 0 1+(634918119/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5395607019/10000000000 : ℝ)*X 1 0+(-2198574827/10000000000 : ℝ)*X 1 1+(2539673239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((84306379/156250000 : ℝ)*X 2 0+(1269836271/2500000000 : ℝ)*X 2 1+(-2198575001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((854891369/2000000000 : ℝ)*X 0 0+(3741620163/10000000000 : ℝ)*X 0 1+(304618221/625000000 : ℝ)*X 0 2+(854891369/2000000000 : ℝ)*X 1 0+(3741620163/10000000000 : ℝ)*X 1 1+(304618221/625000000 : ℝ)*X 1 2+(854891369/2000000000 : ℝ)*X 2 0+(3741620163/10000000000 : ℝ)*X 2 1+(304618221/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1923082921/10000000000 : ℝ)*X 0 0+(8136637/16000000 : ℝ)*X 0 1+(699286431/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5259337819/10000000000 : ℝ)*X 1 0+(-1683629347/10000000000 : ℝ)*X 1 1+(349643217/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259337743/10000000000 : ℝ)*X 2 0+(699286429/1250000000 : ℝ)*X 2 1+(-1683629511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4275287339/10000000000 : ℝ)*X 0 0+(194429611/400000000 : ℝ)*X 0 1+(3754991307/10000000000 : ℝ)*X 0 2+(4275287339/10000000000 : ℝ)*X 1 0+(194429611/400000000 : ℝ)*X 1 1+(3754991307/10000000000 : ℝ)*X 1 2+(4275287339/10000000000 : ℝ)*X 2 0+(194429611/400000000 : ℝ)*X 2 1+(3754991307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10800099097125345096440482941/3005375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (262172833/50000000000000 : ℝ)*(base19) + (1448213/160000000000 : ℝ)*(base23) + (20416651/50000000000000 : ℝ)*(upper3) + (31926083/100000000000000 : ℝ)*(upper4) + (11769989/100000000000000 : ℝ)*(upper5) + (700554407857117/50000000000000 : ℝ)*(major0) + (700554407857117/50000000000000 : ℝ)*(major1) + (700554407857117/50000000000000 : ℝ)*(major2) + (119938823060871/6250000000000 : ℝ)*(sp0) + (479757637254967/25000000000000 : ℝ)*(sp1) + (239878771029051/12500000000000 : ℝ)*(sp2) + (27599471262527/3125000000000 : ℝ)*(sp3) + (4952195799/50000000000000 : ℝ)*(sp4) + (167893779/5000000000000 : ℝ)*(sp7) + (220796609569111/25000000000000 : ℝ)*(f.failure) + (959515536682767/50000000000000 : ℝ)*(f.sum) + (135490746020361/60107500000000000000000000000 : ℝ)*base66 + (15613515854404972353/6010750000000000000000000000000000 : ℝ)*base68 + (13801008104556472353/6010750000000000000000000000000000 : ℝ)*base70 + (54622139472615472353/6010750000000000000000000000000000 : ℝ)*base72 + (113481165760091/15026875000000000000000000000 : ℝ)*base73 + (10493678217527647/6010750000000000000000000000000000 : ℝ)*base75 + (31662919508392472353/6010750000000000000000000000000000 : ℝ)*base78 + (37714771142455527647/6010750000000000000000000000000000 : ℝ)*base79 + (132740962349957/30053750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3489693/1250000000000000000000 : ℝ)*base90 + (3489693/1250000000000000000000 : ℝ)*base92 + (3489693/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9149800396941036919671875907/1502687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43433309/100000000000000 : ℝ)*(base1) + (1332082963/100000000000000 : ℝ)*(base19) + (323281411/25000000000000 : ℝ)*(base23) + (153033797/100000000000000 : ℝ)*(upper3) + (61737111/50000000000000 : ℝ)*(upper5) + (358676573252447/25000000000000 : ℝ)*(major0) + (358676573252447/25000000000000 : ℝ)*(major1) + (358676573252447/25000000000000 : ℝ)*(major2) + (8044769643/100000000000000 : ℝ)*(sp1) + (3818537599/50000000000000 : ℝ)*(sp2) + (1965047878434881/100000000000000 : ℝ)*(sp4) + (1965038458148967/100000000000000 : ℝ)*(sp5) + (196503890480073/10000000000000 : ℝ)*(sp6) + (113045563077429/12500000000000 : ℝ)*(sp7) + (904364548052741/100000000000000 : ℝ)*(f.failure) + (491261958750393/25000000000000 : ℝ)*(f.sum) + (233102057049271/120215000000000000000000000000 : ℝ)*base65 + (23362326784552327677/3005375000000000000000000000000000 : ℝ)*base67 + (35302821749097202677/3005375000000000000000000000000000 : ℝ)*base69 + (15138849265719952677/3005375000000000000000000000000000 : ℝ)*base71 + (258626618787013/60107500000000000000000000000 : ℝ)*base73 + (8002358628988452677/3005375000000000000000000000000000 : ℝ)*base75 + (44240556909821952677/3005375000000000000000000000000000 : ℝ)*base77 + (26866672574017202677/3005375000000000000000000000000000 : ℝ)*base79 + (117186714254809/30053750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (42639383/5000000000000000000000 : ℝ)*base90 + (42639383/5000000000000000000000 : ℝ)*base92 + (42639383/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1441_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1047/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (533/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (31/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1441_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1441_s2_0 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-977472139/5000000000 : ℝ)*x 0 + (2727759189/5000000000 : ℝ)*x 1 + (5203504877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977472139/5000000000 : ℝ)^4401 ≤ (2979385427453/25000000000000 : ℝ)^3377 := by
    have hnat : (977472139 : ℕ)^4401*25000000000000^3377 ≤ 2979385427453^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977472139 5000000000 2979385427453 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727759189/5000000000 : ℝ)^4401 ≤ (181592288811/400000000000 : ℝ)^3377 := by
    have hnat : (2727759189 : ℕ)^4401*400000000000^3377 ≤ 181592288811^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727759189 5000000000 181592288811 400000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5203504877/10000000000 : ℝ)^4401 ≤ (42684386077491/100000000000000 : ℝ)^3377 := by
    have hnat : (5203504877 : ℕ)^4401*100000000000000^3377 ≤ 42684386077491^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203504877 10000000000 42684386077491 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977472139/5000000000 : ℝ), (2727759189/5000000000 : ℝ), (5203504877/10000000000 : ℝ)] ![(2979385427453/25000000000000 : ℝ), (181592288811/400000000000 : ℝ), (42684386077491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977472139/5000000000 : ℝ)|^4401 ≤ (2979385427453/25000000000000 : ℝ)^3377
        have hw : |(-977472139/5000000000 : ℝ)|=(977472139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727759189/5000000000 : ℝ)|^4401 ≤ (181592288811/400000000000 : ℝ)^3377
        have hw : |(2727759189/5000000000 : ℝ)|=(2727759189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5203504877/10000000000 : ℝ)|^4401 ≤ (42684386077491/100000000000000 : ℝ)^3377
        have hw : |(5203504877/10000000000 : ℝ)|=(5203504877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s2_1 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359385047/10000000000 : ℝ)*x 0 + (-2084536523/10000000000 : ℝ)*x 1 + (5203504681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359385047/10000000000 : ℝ)^4401 ≤ (5544790235797/12500000000000 : ℝ)^3377 := by
    have hnat : (5359385047 : ℕ)^4401*12500000000000^3377 ≤ 5544790235797^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359385047 10000000000 5544790235797 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084536523/10000000000 : ℝ)^4401 ≤ (12957294116017/100000000000000 : ℝ)^3377 := by
    have hnat : (2084536523 : ℕ)^4401*100000000000000^3377 ≤ 12957294116017^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084536523 10000000000 12957294116017 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5203504681/10000000000 : ℝ)^4401 ≤ (1333886999443/3125000000000 : ℝ)^3377 := by
    have hnat : (5203504681 : ℕ)^4401*3125000000000^3377 ≤ 1333886999443^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203504681 10000000000 1333886999443 3125000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359385047/10000000000 : ℝ), (-2084536523/10000000000 : ℝ), (5203504681/10000000000 : ℝ)] ![(5544790235797/12500000000000 : ℝ), (12957294116017/100000000000000 : ℝ), (1333886999443/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359385047/10000000000 : ℝ)|^4401 ≤ (5544790235797/12500000000000 : ℝ)^3377
        have hw : |(5359385047/10000000000 : ℝ)|=(5359385047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2084536523/10000000000 : ℝ)|^4401 ≤ (12957294116017/100000000000000 : ℝ)^3377
        have hw : |(-2084536523/10000000000 : ℝ)|=(2084536523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5203504681/10000000000 : ℝ)|^4401 ≤ (1333886999443/3125000000000 : ℝ)^3377
        have hw : |(5203504681/10000000000 : ℝ)|=(5203504681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s2_2 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071876911/2000000000 : ℝ)*x 0 + (5203505191/10000000000 : ℝ)*x 1 + (-416907301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071876911/2000000000 : ℝ)^4401 ≤ (2217915828971/5000000000000 : ℝ)^3377 := by
    have hnat : (1071876911 : ℕ)^4401*5000000000000^3377 ≤ 2217915828971^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071876911 2000000000 2217915828971 5000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5203505191/10000000000 : ℝ)^4401 ≤ (1333887169821/3125000000000 : ℝ)^3377 := by
    have hnat : (5203505191 : ℕ)^4401*3125000000000^3377 ≤ 1333887169821^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203505191 10000000000 1333887169821 3125000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416907301/2000000000 : ℝ)^4401 ≤ (12957293970203/100000000000000 : ℝ)^3377 := by
    have hnat : (416907301 : ℕ)^4401*100000000000000^3377 ≤ 12957293970203^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416907301 2000000000 12957293970203 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071876911/2000000000 : ℝ), (5203505191/10000000000 : ℝ), (-416907301/2000000000 : ℝ)] ![(2217915828971/5000000000000 : ℝ), (1333887169821/3125000000000 : ℝ), (12957293970203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071876911/2000000000 : ℝ)|^4401 ≤ (2217915828971/5000000000000 : ℝ)^3377
        have hw : |(1071876911/2000000000 : ℝ)|=(1071876911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5203505191/10000000000 : ℝ)|^4401 ≤ (1333887169821/3125000000000 : ℝ)^3377
        have hw : |(5203505191/10000000000 : ℝ)|=(5203505191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416907301/2000000000 : ℝ)|^4401 ≤ (12957293970203/100000000000000 : ℝ)^3377
        have hw : |(-416907301/2000000000 : ℝ)|=(416907301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s2_3 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297247529/10000000000 : ℝ)*x 0 + (2015621477/5000000000 : ℝ)*x 1 + (286176951/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297247529/10000000000 : ℝ)^4401 ≤ (33263161472673/100000000000000 : ℝ)^3377 := by
    have hnat : (4297247529 : ℕ)^4401*100000000000000^3377 ≤ 33263161472673^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297247529 10000000000 33263161472673 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015621477/5000000000 : ℝ)^4401 ≤ (15302667355777/50000000000000 : ℝ)^3377 := by
    have hnat : (2015621477 : ℕ)^4401*50000000000000^3377 ≤ 15302667355777^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015621477 5000000000 15302667355777 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286176951/625000000 : ℝ)^4401 ≤ (36131503805171/100000000000000 : ℝ)^3377 := by
    have hnat : (286176951 : ℕ)^4401*100000000000000^3377 ≤ 36131503805171^3377*625000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286176951 625000000 36131503805171 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297247529/10000000000 : ℝ), (2015621477/5000000000 : ℝ), (286176951/625000000 : ℝ)] ![(33263161472673/100000000000000 : ℝ), (15302667355777/50000000000000 : ℝ), (36131503805171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297247529/10000000000 : ℝ)|^4401 ≤ (33263161472673/100000000000000 : ℝ)^3377
        have hw : |(4297247529/10000000000 : ℝ)|=(4297247529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015621477/5000000000 : ℝ)|^4401 ≤ (15302667355777/50000000000000 : ℝ)^3377
        have hw : |(2015621477/5000000000 : ℝ)|=(2015621477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(286176951/625000000 : ℝ)|^4401 ≤ (36131503805171/100000000000000 : ℝ)^3377
        have hw : |(286176951/625000000 : ℝ)|=(286176951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s2_4 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390997483/2000000000 : ℝ)*x 0 + (5204929811/10000000000 : ℝ)*x 1 + (170440063/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390997483/2000000000 : ℝ)^4401 ≤ (5958942208809/50000000000000 : ℝ)^3377 := by
    have hnat : (390997483 : ℕ)^4401*50000000000000^3377 ≤ 5958942208809^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390997483 2000000000 5958942208809 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204929811/10000000000 : ℝ)^4401 ≤ (42699619804201/100000000000000 : ℝ)^3377 := by
    have hnat : (5204929811 : ℕ)^4401*100000000000000^3377 ≤ 42699619804201^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204929811 10000000000 42699619804201 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170440063/312500000 : ℝ)^4401 ≤ (5672811970079/12500000000000 : ℝ)^3377 := by
    have hnat : (170440063 : ℕ)^4401*12500000000000^3377 ≤ 5672811970079^3377*312500000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170440063 312500000 5672811970079 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390997483/2000000000 : ℝ), (5204929811/10000000000 : ℝ), (170440063/312500000 : ℝ)] ![(5958942208809/50000000000000 : ℝ), (42699619804201/100000000000000 : ℝ), (5672811970079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390997483/2000000000 : ℝ)|^4401 ≤ (5958942208809/50000000000000 : ℝ)^3377
        have hw : |(-390997483/2000000000 : ℝ)|=(390997483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204929811/10000000000 : ℝ)|^4401 ≤ (42699619804201/100000000000000 : ℝ)^3377
        have hw : |(5204929811/10000000000 : ℝ)|=(5204929811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170440063/312500000 : ℝ)|^4401 ≤ (5672811970079/12500000000000 : ℝ)^3377
        have hw : |(170440063/312500000 : ℝ)|=(170440063/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s2_5 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646889829/5000000000 : ℝ)*x 0 + (-366791671/2000000000 : ℝ)*x 1 + (2727041469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646889829/5000000000 : ℝ)^4401 ≤ (21825993310181/50000000000000 : ℝ)^3377 := by
    have hnat : (2646889829 : ℕ)^4401*50000000000000^3377 ≤ 21825993310181^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646889829 5000000000 21825993310181 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366791671/2000000000 : ℝ)^4401 ≤ (1370688449991/12500000000000 : ℝ)^3377 := by
    have hnat : (366791671 : ℕ)^4401*12500000000000^3377 ≤ 1370688449991^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366791671 2000000000 1370688449991 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727041469/5000000000 : ℝ)^4401 ≤ (45382505758743/100000000000000 : ℝ)^3377 := by
    have hnat : (2727041469 : ℕ)^4401*100000000000000^3377 ≤ 45382505758743^3377*5000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727041469 5000000000 45382505758743 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646889829/5000000000 : ℝ), (-366791671/2000000000 : ℝ), (2727041469/5000000000 : ℝ)] ![(21825993310181/50000000000000 : ℝ), (1370688449991/12500000000000 : ℝ), (45382505758743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646889829/5000000000 : ℝ)|^4401 ≤ (21825993310181/50000000000000 : ℝ)^3377
        have hw : |(2646889829/5000000000 : ℝ)|=(2646889829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366791671/2000000000 : ℝ)|^4401 ≤ (1370688449991/12500000000000 : ℝ)^3377
        have hw : |(-366791671/2000000000 : ℝ)|=(366791671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727041469/5000000000 : ℝ)|^4401 ≤ (45382505758743/100000000000000 : ℝ)^3377
        have hw : |(2727041469/5000000000 : ℝ)|=(2727041469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s2_6 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323444787/2500000000 : ℝ)*x 0 + (545408283/1000000000 : ℝ)*x 1 + (-1833959209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323444787/2500000000 : ℝ)^4401 ≤ (8730396227951/20000000000000 : ℝ)^3377 := by
    have hnat : (1323444787 : ℕ)^4401*20000000000000^3377 ≤ 8730396227951^3377*2500000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323444787 2500000000 8730396227951 20000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545408283/1000000000 : ℝ)^4401 ≤ (22691252293799/50000000000000 : ℝ)^3377 := by
    have hnat : (545408283 : ℕ)^4401*50000000000000^3377 ≤ 22691252293799^3377*1000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545408283 1000000000 22691252293799 50000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833959209/10000000000 : ℝ)^4401 ≤ (10965514254459/100000000000000 : ℝ)^3377 := by
    have hnat : (1833959209 : ℕ)^4401*100000000000000^3377 ≤ 10965514254459^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833959209 10000000000 10965514254459 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323444787/2500000000 : ℝ), (545408283/1000000000 : ℝ), (-1833959209/10000000000 : ℝ)] ![(8730396227951/20000000000000 : ℝ), (22691252293799/50000000000000 : ℝ), (10965514254459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323444787/2500000000 : ℝ)|^4401 ≤ (8730396227951/20000000000000 : ℝ)^3377
        have hw : |(1323444787/2500000000 : ℝ)|=(1323444787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545408283/1000000000 : ℝ)|^4401 ≤ (22691252293799/50000000000000 : ℝ)^3377
        have hw : |(545408283/1000000000 : ℝ)|=(545408283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1833959209/10000000000 : ℝ)|^4401 ≤ (10965514254459/100000000000000 : ℝ)^3377
        have hw : |(-1833959209/10000000000 : ℝ)|=(1833959209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1441_s2_7 (p : ℝ) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859468313/2000000000 : ℝ)*x 0 + (4575736169/10000000000 : ℝ)*x 1 + (4034363303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859468313/2000000000 : ℝ)^4401 ≤ (4158013760703/12500000000000 : ℝ)^3377 := by
    have hnat : (859468313 : ℕ)^4401*12500000000000^3377 ≤ 4158013760703^3377*2000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859468313 2000000000 4158013760703 12500000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4575736169/10000000000 : ℝ)^4401 ≤ (36099678363331/100000000000000 : ℝ)^3377 := by
    have hnat : (4575736169 : ℕ)^4401*100000000000000^3377 ≤ 36099678363331^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4575736169 10000000000 36099678363331 100000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034363303/10000000000 : ℝ)^4401 ≤ (7659052883389/25000000000000 : ℝ)^3377 := by
    have hnat : (4034363303 : ℕ)^4401*25000000000000^3377 ≤ 7659052883389^3377*10000000000^4401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034363303 10000000000 7659052883389 25000000000000 4401 3377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4401/1024 : ℝ)) 4401 3377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859468313/2000000000 : ℝ), (4575736169/10000000000 : ℝ), (4034363303/10000000000 : ℝ)] ![(4158013760703/12500000000000 : ℝ), (36099678363331/100000000000000 : ℝ), (7659052883389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859468313/2000000000 : ℝ)|^4401 ≤ (4158013760703/12500000000000 : ℝ)^3377
        have hw : |(859468313/2000000000 : ℝ)|=(859468313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4575736169/10000000000 : ℝ)|^4401 ≤ (36099678363331/100000000000000 : ℝ)^3377
        have hw : |(4575736169/10000000000 : ℝ)|=(4575736169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034363303/10000000000 : ℝ)|^4401 ≤ (7659052883389/25000000000000 : ℝ)^3377
        have hw : |(4034363303/10000000000 : ℝ)|=(4034363303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1441_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/400 : ℝ)*pair X i i ≤ pair X i h) :
    (10431/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (31/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (31/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (31/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (31/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (31/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (31/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (31/400 : ℝ) ^ (275/64 : ℝ) ≤ (211046554312183/12500000000000000000 : ℝ) := by
    have hpowers : (31/400 : ℝ)^275 ≤ (211046554312183/12500000000000000000 : ℝ)^64 := by
      have hnat : (31 : ℕ)^275*12500000000000000000^64 ≤ 211046554312183^64*400^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31 400 211046554312183 12500000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31/400 : ℝ)) (X := (211046554312183/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hpowhi : (18767/100000 : ℝ) ^ (275/64 : ℝ) ≤ (75486365100917889/100000000000000000000 : ℝ) := by
    have hpowers : (18767/100000 : ℝ)^275 ≤ (75486365100917889/100000000000000000000 : ℝ)^64 := by
      have hnat : (18767 : ℕ)^275*100000000000000000000^64 ≤ 75486365100917889^64*100000^275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18767 100000 75486365100917889 100000000000000000000 275 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18767/100000 : ℝ)) (X := (75486365100917889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250211046554312183/6250000000000000000 : ℝ) ≤ (10000078585044389/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (6250211046554312183/6250000000000000000 : ℝ)^64 ≤ (10000078585044389/10000000000000000 : ℝ)^275 := by
      have hnat : (6250211046554312183 : ℕ)^64*10000000000000000^275 ≤ 10000078585044389^275*6250000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250211046554312183 6250000000000000000 10000078585044389 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078585044389/10000000000000000 : ℝ)) (X := (6250211046554312183/6250000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100077174737535415353/100000000000000000000 : ℝ) ≤ (2500448883774637/2500000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (100077174737535415353/100000000000000000000 : ℝ)^64 ≤ (2500448883774637/2500000000000000 : ℝ)^275 := by
      have hnat : (100077174737535415353 : ℕ)^64*2500000000000000^275 ≤ 2500448883774637^275*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100077174737535415353 100000000000000000000 2500448883774637 2500000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500448883774637/2500000000000000 : ℝ)) (X := (100077174737535415353/100000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50075486365100917889/50000000000000000000 : ℝ) ≤ (10003512485152707/10000000000000000 : ℝ) ^ (275/64 : ℝ) := by
    have hpowers : (50075486365100917889/50000000000000000000 : ℝ)^64 ≤ (10003512485152707/10000000000000000 : ℝ)^275 := by
      have hnat : (50075486365100917889 : ℕ)^64*10000000000000000^275 ≤ 10003512485152707^275*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50075486365100917889 50000000000000000000 10003512485152707 10000000000000000 64 275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003512485152707/10000000000000000 : ℝ)) (X := (50075486365100917889/50000000000000000000 : ℝ)) (by norm_num) 275 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(211046554312183/12500000000000000000 : ℝ) ≤ ((110144253045594569113/110170000000000000000 : ℝ)+2*(1716950054159/1101700000000000 : ℝ)*(31/400 : ℝ))^(275/64 : ℝ) := by
    rw [show (110144253045594569113/110170000000000000000 : ℝ)+2*(1716950054159/1101700000000000 : ℝ)*(31/400 : ℝ)=(10000078585044389/10000000000000000 : ℝ) by norm_num, show 1+2*(211046554312183/12500000000000000000 : ℝ)=(6250211046554312183/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(75486365100917889/100000000000000000000 : ℝ)+(211046554312183/12500000000000000000 : ℝ) ≤ ((110144253045594569113/110170000000000000000 : ℝ)+(1716950054159/1101700000000000 : ℝ)*((18767/100000 : ℝ)+(31/400 : ℝ)))^(275/64 : ℝ) := by
    rw [show (110144253045594569113/110170000000000000000 : ℝ)+(1716950054159/1101700000000000 : ℝ)*((18767/100000 : ℝ)+(31/400 : ℝ))=(2500448883774637/2500000000000000 : ℝ) by norm_num, show 1+(75486365100917889/100000000000000000000 : ℝ)+(211046554312183/12500000000000000000 : ℝ)=(100077174737535415353/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(75486365100917889/100000000000000000000 : ℝ) ≤ ((110144253045594569113/110170000000000000000 : ℝ)+2*(1716950054159/1101700000000000 : ℝ)*(18767/100000 : ℝ))^(275/64 : ℝ) := by
    rw [show (110144253045594569113/110170000000000000000 : ℝ)+2*(1716950054159/1101700000000000 : ℝ)*(18767/100000 : ℝ)=(10003512485152707/10000000000000000 : ℝ) by norm_num, show 1+2*(75486365100917889/100000000000000000000 : ℝ)=(50075486365100917889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (110144253045594569113/110170000000000000000 : ℝ)*(X 1 0+X 2 0)+(1716950054159/1101700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (31/400 : ℝ)) (hi := (18767/100000 : ℝ)) (c := (110144253045594569113/110170000000000000000 : ℝ)) (alpha := (1716950054159/1101700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (110144253045594569113/110170000000000000000 : ℝ)*(X 0 1+X 2 1)+(1716950054159/1101700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (31/400 : ℝ)) (hi := (18767/100000 : ℝ)) (c := (110144253045594569113/110170000000000000000 : ℝ)) (alpha := (1716950054159/1101700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (110144253045594569113/110170000000000000000 : ℝ)*(X 0 2+X 1 2)+(1716950054159/1101700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (275/64 : ℝ)) (lo := (31/400 : ℝ)) (hi := (18767/100000 : ℝ)) (c := (110144253045594569113/110170000000000000000 : ℝ)) (alpha := (1716950054159/1101700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-977472139/5000000000 : ℝ)*X 0 0+(2727759189/5000000000 : ℝ)*X 0 1+(5203504877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359385047/10000000000 : ℝ)*X 1 0+(-2084536523/10000000000 : ℝ)*X 1 1+(5203504681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071876911/2000000000 : ℝ)*X 2 0+(5203505191/10000000000 : ℝ)*X 2 1+(-416907301/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297247529/10000000000 : ℝ)*X 0 0+(2015621477/5000000000 : ℝ)*X 0 1+(286176951/625000000 : ℝ)*X 0 2+(4297247529/10000000000 : ℝ)*X 1 0+(2015621477/5000000000 : ℝ)*X 1 1+(286176951/625000000 : ℝ)*X 1 2+(4297247529/10000000000 : ℝ)*X 2 0+(2015621477/5000000000 : ℝ)*X 2 1+(286176951/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-390997483/2000000000 : ℝ)*X 0 0+(5204929811/10000000000 : ℝ)*X 0 1+(170440063/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646889829/5000000000 : ℝ)*X 1 0+(-366791671/2000000000 : ℝ)*X 1 1+(2727041469/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323444787/2500000000 : ℝ)*X 2 0+(545408283/1000000000 : ℝ)*X 2 1+(-1833959209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859468313/2000000000 : ℝ)*X 0 0+(4575736169/10000000000 : ℝ)*X 0 1+(4034363303/10000000000 : ℝ)*X 0 2+(859468313/2000000000 : ℝ)*X 1 0+(4575736169/10000000000 : ℝ)*X 1 1+(4034363303/10000000000 : ℝ)*X 1 2+(859468313/2000000000 : ℝ)*X 2 0+(4575736169/10000000000 : ℝ)*X 2 1+(4034363303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1441_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28568936737647958671367984173/5508500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (509594403/100000000000000 : ℝ)*(base19) + (37749241/100000000000000 : ℝ)*(base23) + (42708499/50000000000000 : ℝ)*(lower2) + (83326509/50000000000000 : ℝ)*(upper3) + (27764861/100000000000000 : ℝ)*(lower4) + (30381677/100000000000000 : ℝ)*(upper5) + (2897120309345069/100000000000000 : ℝ)*(major0) + (2897120309345069/100000000000000 : ℝ)*(major1) + (2897120309345069/100000000000000 : ℝ)*(major2) + (992011458955199/25000000000000 : ℝ)*(sp0) + (3968045326226393/100000000000000 : ℝ)*(sp1) + (793609159614311/20000000000000 : ℝ)*(sp2) + (456547921728261/25000000000000 : ℝ)*(sp3) + (584615679/20000000000000 : ℝ)*(sp7) + (913097304995719/50000000000000 : ℝ)*(f.failure) + (992011458955199/25000000000000 : ℝ)*(f.sum) + (18307191430471/13771250000000000000000000000 : ℝ)*base66 + (106765710205039646203/11017000000000000000000000000000000 : ℝ)*base68 + (31149348162293646203/11017000000000000000000000000000000 : ℝ)*base70 + (49622209127190646203/11017000000000000000000000000000000 : ℝ)*base72 + (156096327749349/55085000000000000000000000000 : ℝ)*base74 + (83559679913490646203/11017000000000000000000000000000000 : ℝ)*base76 + (83454177309608646203/11017000000000000000000000000000000 : ℝ)*base78 + (6944563495028646203/11017000000000000000000000000000000 : ℝ)*base80 + (139120948404281/55085000000000000000000000000 : ℝ)*base81 + (14215597/2500000000000000000000 : ℝ)*base90 + (14215597/2500000000000000000000 : ℝ)*base92 + (14215597/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2146460659108181374475005497/550850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216711991/100000000000000 : ℝ)*(base21) + (94076051/100000000000000 : ℝ)*(base29) + (14366613/50000000000000 : ℝ)*(upper3) + (162108407/100000000000000 : ℝ)*(lower4) + (732596259162641/25000000000000 : ℝ)*(major0) + (586077026145323/20000000000000 : ℝ)*(major1) + (586077026145323/20000000000000 : ℝ)*(major2) + (11579540351/100000000000000 : ℝ)*(sp1) + (126240551/5000000000000 : ℝ)*(sp2) + (811384419/20000000000000 : ℝ)*(sp3) + (125425221901833/3125000000000 : ℝ)*(sp4) + (802719085448451/20000000000000 : ℝ)*(sp5) + (2006802132629797/50000000000000 : ℝ)*(sp6) + (369431794756937/20000000000000 : ℝ)*(sp7) + (92358151535339/5000000000000 : ℝ)*(f.failure) + (125425221901833/3125000000000 : ℝ)*(f.sum) + (13967290199323/11017000000000000000000000000 : ℝ)*base66 + (11939763328856491501/2203400000000000000000000000000000 : ℝ)*base68 + (6387257376600491501/2203400000000000000000000000000000 : ℝ)*base70 + (31540456949783017567/2754250000000000000000000000000000 : ℝ)*base72 + (86845528216971/110170000000000000000000000000 : ℝ)*base73 + (12716254160787671501/2203400000000000000000000000000000 : ℝ)*base76 + (2704891269135732433/2754250000000000000000000000000000 : ℝ)*base77 + (4790306936780271501/2203400000000000000000000000000000 : ℝ)*base80 + (359886719343469/110170000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1194343/250000000000000000000 : ℝ)*base89 + (1194343/250000000000000000000 : ℝ)*base91 + (1194343/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1441_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (31/400 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1441_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1441_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15763/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1441_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1441_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1441_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (275/64 : ℝ) ≤ p) (hpb : p ≤ (4401/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79321237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15763/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1441_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

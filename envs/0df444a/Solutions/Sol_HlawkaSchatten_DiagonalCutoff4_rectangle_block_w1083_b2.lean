-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1083_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:12.329275+00:00
-- url     : https://prove2.me/submissions/8dbe35c1-4df7-48f9-9b2b-60a912508e16

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
theorem support_rectangle_w1083_s6_0 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-439075729/2000000000 : ℝ)*x 0 + (1078913869/2000000000 : ℝ)*x 1 + (1316070343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439075729/2000000000 : ℝ)^2069 ≤ (6667193249797/50000000000000 : ℝ)^1557 := by
    have hnat : (439075729 : ℕ)^2069*50000000000000^1557 ≤ 6667193249797^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439075729 2000000000 6667193249797 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078913869/2000000000 : ℝ)^2069 ≤ (44036634000989/100000000000000 : ℝ)^1557 := by
    have hnat : (1078913869 : ℕ)^2069*100000000000000^1557 ≤ 44036634000989^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078913869 2000000000 44036634000989 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316070343/2500000000 : ℝ)^2069 ≤ (42628979487497/100000000000000 : ℝ)^1557 := by
    have hnat : (1316070343 : ℕ)^2069*100000000000000^1557 ≤ 42628979487497^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316070343 2500000000 42628979487497 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439075729/2000000000 : ℝ), (1078913869/2000000000 : ℝ), (1316070343/2500000000 : ℝ)] ![(6667193249797/50000000000000 : ℝ), (44036634000989/100000000000000 : ℝ), (42628979487497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439075729/2000000000 : ℝ)|^2069 ≤ (6667193249797/50000000000000 : ℝ)^1557
        have hw : |(-439075729/2000000000 : ℝ)|=(439075729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078913869/2000000000 : ℝ)|^2069 ≤ (44036634000989/100000000000000 : ℝ)^1557
        have hw : |(1078913869/2000000000 : ℝ)|=(1078913869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316070343/2500000000 : ℝ)|^2069 ≤ (42628979487497/100000000000000 : ℝ)^1557
        have hw : |(1316070343/2500000000 : ℝ)|=(1316070343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s6_1 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345065437/10000000000 : ℝ)*x 0 + (-2261485371/10000000000 : ℝ)*x 1 + (658035169/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345065437/10000000000 : ℝ)^2069 ≤ (21750226399401/50000000000000 : ℝ)^1557 := by
    have hnat : (5345065437 : ℕ)^2069*50000000000000^1557 ≤ 21750226399401^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345065437 10000000000 21750226399401 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261485371/10000000000 : ℝ)^2069 ≤ (3467641978377/25000000000000 : ℝ)^1557 := by
    have hnat : (2261485371 : ℕ)^2069*25000000000000^1557 ≤ 3467641978377^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261485371 10000000000 3467641978377 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658035169/1250000000 : ℝ)^2069 ≤ (10657244818071/25000000000000 : ℝ)^1557 := by
    have hnat : (658035169 : ℕ)^2069*25000000000000^1557 ≤ 10657244818071^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658035169 1250000000 10657244818071 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345065437/10000000000 : ℝ), (-2261485371/10000000000 : ℝ), (658035169/1250000000 : ℝ)] ![(21750226399401/50000000000000 : ℝ), (3467641978377/25000000000000 : ℝ), (10657244818071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345065437/10000000000 : ℝ)|^2069 ≤ (21750226399401/50000000000000 : ℝ)^1557
        have hw : |(5345065437/10000000000 : ℝ)|=(5345065437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2261485371/10000000000 : ℝ)|^2069 ≤ (3467641978377/25000000000000 : ℝ)^1557
        have hw : |(-2261485371/10000000000 : ℝ)|=(2261485371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658035169/1250000000 : ℝ)|^2069 ≤ (10657244818071/25000000000000 : ℝ)^1557
        have hw : |(658035169/1250000000 : ℝ)|=(658035169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s6_2 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267253271/500000000 : ℝ)*x 0 + (5264281391/10000000000 : ℝ)*x 1 + (-1130742671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267253271/500000000 : ℝ)^2069 ≤ (43500452614953/100000000000000 : ℝ)^1557 := by
    have hnat : (267253271 : ℕ)^2069*100000000000000^1557 ≤ 43500452614953^1557*500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267253271 500000000 43500452614953 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264281391/10000000000 : ℝ)^2069 ≤ (42628979691949/100000000000000 : ℝ)^1557 := by
    have hnat : (5264281391 : ℕ)^2069*100000000000000^1557 ≤ 42628979691949^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264281391 10000000000 42628979691949 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130742671/5000000000 : ℝ)^2069 ≤ (277411353543/2000000000000 : ℝ)^1557 := by
    have hnat : (1130742671 : ℕ)^2069*2000000000000^1557 ≤ 277411353543^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130742671 5000000000 277411353543 2000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267253271/500000000 : ℝ), (5264281391/10000000000 : ℝ), (-1130742671/5000000000 : ℝ)] ![(43500452614953/100000000000000 : ℝ), (42628979691949/100000000000000 : ℝ), (277411353543/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267253271/500000000 : ℝ)|^2069 ≤ (43500452614953/100000000000000 : ℝ)^1557
        have hw : |(267253271/500000000 : ℝ)|=(267253271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264281391/10000000000 : ℝ)|^2069 ≤ (42628979691949/100000000000000 : ℝ)^1557
        have hw : |(5264281391/10000000000 : ℝ)|=(5264281391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1130742671/5000000000 : ℝ)|^2069 ≤ (277411353543/2000000000000 : ℝ)^1557
        have hw : |(-1130742671/5000000000 : ℝ)|=(1130742671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s6_3 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (874605547/2000000000 : ℝ)*x 0 + (4246816733/10000000000 : ℝ)*x 1 + (900605013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874605547/2000000000 : ℝ)^2069 ≤ (33316391439091/100000000000000 : ℝ)^1557 := by
    have hnat : (874605547 : ℕ)^2069*100000000000000^1557 ≤ 33316391439091^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874605547 2000000000 33316391439091 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246816733/10000000000 : ℝ)^2069 ≤ (16022373776843/50000000000000 : ℝ)^1557 := by
    have hnat : (4246816733 : ℕ)^2069*50000000000000^1557 ≤ 16022373776843^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246816733 10000000000 16022373776843 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900605013/2000000000 : ℝ)^2069 ≤ (34638860996279/100000000000000 : ℝ)^1557 := by
    have hnat : (900605013 : ℕ)^2069*100000000000000^1557 ≤ 34638860996279^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900605013 2000000000 34638860996279 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874605547/2000000000 : ℝ), (4246816733/10000000000 : ℝ), (900605013/2000000000 : ℝ)] ![(33316391439091/100000000000000 : ℝ), (16022373776843/50000000000000 : ℝ), (34638860996279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874605547/2000000000 : ℝ)|^2069 ≤ (33316391439091/100000000000000 : ℝ)^1557
        have hw : |(874605547/2000000000 : ℝ)|=(874605547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246816733/10000000000 : ℝ)|^2069 ≤ (16022373776843/50000000000000 : ℝ)^1557
        have hw : |(4246816733/10000000000 : ℝ)|=(4246816733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900605013/2000000000 : ℝ)|^2069 ≤ (34638860996279/100000000000000 : ℝ)^1557
        have hw : |(900605013/2000000000 : ℝ)|=(900605013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s6_4 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195383329/10000000000 : ℝ)*x 0 + (658076329/1250000000 : ℝ)*x 1 + (5394239229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195383329/10000000000 : ℝ)^2069 ≤ (13334424304879/100000000000000 : ℝ)^1557 := by
    have hnat : (2195383329 : ℕ)^2069*100000000000000^1557 ≤ 13334424304879^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195383329 10000000000 13334424304879 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658076329/1250000000 : ℝ)^2069 ≤ (21316261284571/50000000000000 : ℝ)^1557 := by
    have hnat : (658076329 : ℕ)^2069*50000000000000^1557 ≤ 21316261284571^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658076329 1250000000 21316261284571 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394239229/10000000000 : ℝ)^2069 ≤ (44033053107379/100000000000000 : ℝ)^1557 := by
    have hnat : (5394239229 : ℕ)^2069*100000000000000^1557 ≤ 44033053107379^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394239229 10000000000 44033053107379 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195383329/10000000000 : ℝ), (658076329/1250000000 : ℝ), (5394239229/10000000000 : ℝ)] ![(13334424304879/100000000000000 : ℝ), (21316261284571/50000000000000 : ℝ), (44033053107379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195383329/10000000000 : ℝ)|^2069 ≤ (13334424304879/100000000000000 : ℝ)^1557
        have hw : |(-2195383329/10000000000 : ℝ)|=(2195383329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658076329/1250000000 : ℝ)|^2069 ≤ (21316261284571/50000000000000 : ℝ)^1557
        have hw : |(658076329/1250000000 : ℝ)|=(658076329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394239229/10000000000 : ℝ)|^2069 ≤ (44033053107379/100000000000000 : ℝ)^1557
        have hw : |(5394239229/10000000000 : ℝ)|=(5394239229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s6_5 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132805101/250000000 : ℝ)*x 0 + (-426305591/2000000000 : ℝ)*x 1 + (539423927/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132805101/250000000 : ℝ)^2069 ≤ (21572713947179/50000000000000 : ℝ)^1557 := by
    have hnat : (132805101 : ℕ)^2069*50000000000000^1557 ≤ 21572713947179^1557*250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132805101 250000000 21572713947179 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426305591/2000000000 : ℝ)^2069 ≤ (12821518546251/100000000000000 : ℝ)^1557 := by
    have hnat : (426305591 : ℕ)^2069*100000000000000^1557 ≤ 12821518546251^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426305591 2000000000 12821518546251 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539423927/1000000000 : ℝ)^2069 ≤ (44033053552117/100000000000000 : ℝ)^1557 := by
    have hnat : (539423927 : ℕ)^2069*100000000000000^1557 ≤ 44033053552117^1557*1000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539423927 1000000000 44033053552117 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132805101/250000000 : ℝ), (-426305591/2000000000 : ℝ), (539423927/1000000000 : ℝ)] ![(21572713947179/50000000000000 : ℝ), (12821518546251/100000000000000 : ℝ), (44033053552117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132805101/250000000 : ℝ)|^2069 ≤ (21572713947179/50000000000000 : ℝ)^1557
        have hw : |(132805101/250000000 : ℝ)|=(132805101/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426305591/2000000000 : ℝ)|^2069 ≤ (12821518546251/100000000000000 : ℝ)^1557
        have hw : |(-426305591/2000000000 : ℝ)|=(426305591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539423927/1000000000 : ℝ)|^2069 ≤ (44033053552117/100000000000000 : ℝ)^1557
        have hw : |(539423927/1000000000 : ℝ)|=(539423927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s6_6 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531220421/1000000000 : ℝ)*x 0 + (5394239239/10000000000 : ℝ)*x 1 + (-1065763883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531220421/1000000000 : ℝ)^2069 ≤ (10786357432281/25000000000000 : ℝ)^1557 := by
    have hnat : (531220421 : ℕ)^2069*25000000000000^1557 ≤ 10786357432281^1557*1000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531220421 1000000000 10786357432281 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394239239/10000000000 : ℝ)^2069 ≤ (11008263303963/25000000000000 : ℝ)^1557 := by
    have hnat : (5394239239 : ℕ)^2069*25000000000000^1557 ≤ 11008263303963^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394239239 10000000000 11008263303963 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065763883/5000000000 : ℝ)^2069 ≤ (6410758517769/50000000000000 : ℝ)^1557 := by
    have hnat : (1065763883 : ℕ)^2069*50000000000000^1557 ≤ 6410758517769^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065763883 5000000000 6410758517769 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531220421/1000000000 : ℝ), (5394239239/10000000000 : ℝ), (-1065763883/5000000000 : ℝ)] ![(10786357432281/25000000000000 : ℝ), (11008263303963/25000000000000 : ℝ), (6410758517769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531220421/1000000000 : ℝ)|^2069 ≤ (10786357432281/25000000000000 : ℝ)^1557
        have hw : |(531220421/1000000000 : ℝ)|=(531220421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394239239/10000000000 : ℝ)|^2069 ≤ (11008263303963/25000000000000 : ℝ)^1557
        have hw : |(5394239239/10000000000 : ℝ)|=(5394239239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065763883/5000000000 : ℝ)|^2069 ≤ (6410758517769/50000000000000 : ℝ)^1557
        have hw : |(-1065763883/5000000000 : ℝ)|=(1065763883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s6_7 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4373037511/10000000000 : ℝ)*x 0 + (450237833/1000000000 : ℝ)*x 1 + (849493229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373037511/10000000000 : ℝ)^2069 ≤ (16658245205159/50000000000000 : ℝ)^1557 := by
    have hnat : (4373037511 : ℕ)^2069*50000000000000^1557 ≤ 16658245205159^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373037511 10000000000 16658245205159 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450237833/1000000000 : ℝ)^2069 ≤ (216451564373/625000000000 : ℝ)^1557 := by
    have hnat : (450237833 : ℕ)^2069*625000000000^1557 ≤ 216451564373^1557*1000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450237833 1000000000 216451564373 625000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849493229/2000000000 : ℝ)^2069 ≤ (2003203705283/6250000000000 : ℝ)^1557 := by
    have hnat : (849493229 : ℕ)^2069*6250000000000^1557 ≤ 2003203705283^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849493229 2000000000 2003203705283 6250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373037511/10000000000 : ℝ), (450237833/1000000000 : ℝ), (849493229/2000000000 : ℝ)] ![(16658245205159/50000000000000 : ℝ), (216451564373/625000000000 : ℝ), (2003203705283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373037511/10000000000 : ℝ)|^2069 ≤ (16658245205159/50000000000000 : ℝ)^1557
        have hw : |(4373037511/10000000000 : ℝ)|=(4373037511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450237833/1000000000 : ℝ)|^2069 ≤ (216451564373/625000000000 : ℝ)^1557
        have hw : |(450237833/1000000000 : ℝ)|=(450237833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849493229/2000000000 : ℝ)|^2069 ≤ (2003203705283/6250000000000 : ℝ)^1557
        have hw : |(849493229/2000000000 : ℝ)|=(849493229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1083_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2253/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1753/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (5613/50000 : ℝ) ^ (8275/2048 : ℝ) ≤ (1453477439524687/10000000000000000000 : ℝ) := by
    have hpowers : (5613/50000 : ℝ)^8275 ≤ (1453477439524687/10000000000000000000 : ℝ)^2048 := by
      have hnat : (5613 : ℕ)^8275*10000000000000000000^2048 ≤ 1453477439524687^2048*50000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5613 50000 1453477439524687 10000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5613/50000 : ℝ)) (X := (1453477439524687/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2813/20000 : ℝ) ^ (8275/2048 : ℝ) ≤ (18071962494973837/50000000000000000000 : ℝ) := by
    have hpowers : (2813/20000 : ℝ)^8275 ≤ (18071962494973837/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2813 : ℕ)^8275*50000000000000000000^2048 ≤ 18071962494973837^2048*20000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 20000 18071962494973837 50000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/20000 : ℝ)) (X := (18071962494973837/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001453477439524687/5000000000000000000 : ℝ) ≤ (10000719370700099/10000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (5001453477439524687/5000000000000000000 : ℝ)^2048 ≤ (10000719370700099/10000000000000000 : ℝ)^8275 := by
      have hnat : (5001453477439524687 : ℕ)^2048*10000000000000000^8275 ≤ 10000719370700099^8275*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001453477439524687 5000000000000000000 10000719370700099 10000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000719370700099/10000000000000000 : ℝ)) (X := (5001453477439524687/5000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253167418711574659/6250000000000000000 : ℝ) ≤ (500062701022037/500000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (6253167418711574659/6250000000000000000 : ℝ)^2048 ≤ (500062701022037/500000000000000 : ℝ)^8275 := by
      have hnat : (6253167418711574659 : ℕ)^2048*500000000000000^8275 ≤ 500062701022037^8275*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253167418711574659 6250000000000000000 500062701022037 500000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500062701022037/500000000000000 : ℝ)) (X := (6253167418711574659/6250000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018071962494973837/25000000000000000000 : ℝ) ≤ (10001788670181381/10000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (25018071962494973837/25000000000000000000 : ℝ)^2048 ≤ (10001788670181381/10000000000000000 : ℝ)^8275 := by
      have hnat : (25018071962494973837 : ℕ)^2048*10000000000000000^8275 ≤ 10001788670181381^8275*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018071962494973837 25000000000000000000 10001788670181381 10000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001788670181381/10000000000000000 : ℝ)) (X := (25018071962494973837/25000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1453477439524687/10000000000000000000 : ℝ) ≤ ((28380038337440709329/28390000000000000000 : ℝ)+2*(534649740641/283900000000000 : ℝ)*(5613/50000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (28380038337440709329/28390000000000000000 : ℝ)+2*(534649740641/283900000000000 : ℝ)*(5613/50000 : ℝ)=(10000719370700099/10000000000000000 : ℝ) by norm_num, show 1+2*(1453477439524687/10000000000000000000 : ℝ)=(5001453477439524687/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18071962494973837/50000000000000000000 : ℝ)+(1453477439524687/10000000000000000000 : ℝ) ≤ ((28380038337440709329/28390000000000000000 : ℝ)+(534649740641/283900000000000 : ℝ)*((2813/20000 : ℝ)+(5613/50000 : ℝ)))^(8275/2048 : ℝ) := by
    rw [show (28380038337440709329/28390000000000000000 : ℝ)+(534649740641/283900000000000 : ℝ)*((2813/20000 : ℝ)+(5613/50000 : ℝ))=(500062701022037/500000000000000 : ℝ) by norm_num, show 1+(18071962494973837/50000000000000000000 : ℝ)+(1453477439524687/10000000000000000000 : ℝ)=(6253167418711574659/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18071962494973837/50000000000000000000 : ℝ) ≤ ((28380038337440709329/28390000000000000000 : ℝ)+2*(534649740641/283900000000000 : ℝ)*(2813/20000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (28380038337440709329/28390000000000000000 : ℝ)+2*(534649740641/283900000000000 : ℝ)*(2813/20000 : ℝ)=(10001788670181381/10000000000000000 : ℝ) by norm_num, show 1+2*(18071962494973837/50000000000000000000 : ℝ)=(25018071962494973837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28380038337440709329/28390000000000000000 : ℝ)*(X 1 0+X 2 0)+(534649740641/283900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (28380038337440709329/28390000000000000000 : ℝ)) (alpha := (534649740641/283900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28380038337440709329/28390000000000000000 : ℝ)*(X 0 1+X 2 1)+(534649740641/283900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (28380038337440709329/28390000000000000000 : ℝ)) (alpha := (534649740641/283900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28380038337440709329/28390000000000000000 : ℝ)*(X 0 2+X 1 2)+(534649740641/283900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (28380038337440709329/28390000000000000000 : ℝ)) (alpha := (534649740641/283900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-439075729/2000000000 : ℝ)*X 0 0+(1078913869/2000000000 : ℝ)*X 0 1+(1316070343/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345065437/10000000000 : ℝ)*X 1 0+(-2261485371/10000000000 : ℝ)*X 1 1+(658035169/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267253271/500000000 : ℝ)*X 2 0+(5264281391/10000000000 : ℝ)*X 2 1+(-1130742671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874605547/2000000000 : ℝ)*X 0 0+(4246816733/10000000000 : ℝ)*X 0 1+(900605013/2000000000 : ℝ)*X 0 2+(874605547/2000000000 : ℝ)*X 1 0+(4246816733/10000000000 : ℝ)*X 1 1+(900605013/2000000000 : ℝ)*X 1 2+(874605547/2000000000 : ℝ)*X 2 0+(4246816733/10000000000 : ℝ)*X 2 1+(900605013/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2195383329/10000000000 : ℝ)*X 0 0+(658076329/1250000000 : ℝ)*X 0 1+(5394239229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132805101/250000000 : ℝ)*X 1 0+(-426305591/2000000000 : ℝ)*X 1 1+(539423927/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531220421/1000000000 : ℝ)*X 2 0+(5394239239/10000000000 : ℝ)*X 2 1+(-1065763883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373037511/10000000000 : ℝ)*X 0 0+(450237833/1000000000 : ℝ)*X 0 1+(849493229/2000000000 : ℝ)*X 0 2+(4373037511/10000000000 : ℝ)*X 1 0+(450237833/1000000000 : ℝ)*X 1 1+(849493229/2000000000 : ℝ)*X 1 2+(4373037511/10000000000 : ℝ)*X 2 0+(450237833/1000000000 : ℝ)*X 2 1+(849493229/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1453022381718610478862604059/709750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (620903241/100000000000000 : ℝ)*(base19) + (490668431/100000000000000 : ℝ)*(base23) + (28281641/50000000000000 : ℝ)*(lower2) + (12344693/20000000000000 : ℝ)*(upper3) + (5951069/25000000000000 : ℝ)*(upper5) + (2894607604940819/50000000000000 : ℝ)*(major0) + (2894607604940819/50000000000000 : ℝ)*(major1) + (2894607604940819/50000000000000 : ℝ)*(major2) + (3837661308765721/50000000000000 : ℝ)*(sp0) + (1918834672974769/25000000000000 : ℝ)*(sp1) + (1535067764426777/20000000000000 : ℝ)*(sp2) + (3903081741642191/100000000000000 : ℝ)*(sp3) + (8347635437/50000000000000 : ℝ)*(sp4) + (1859415543/20000000000000 : ℝ)*(sp7) + (1951545519359953/50000000000000 : ℝ)*(f.failure) + (1918834828200579/25000000000000 : ℝ)*(f.sum) + (4282279990841/1774375000000000000000000000 : ℝ)*base65 + (23760554782790399549/1419500000000000000000000000000000 : ℝ)*base68 + (36956815660945899549/1419500000000000000000000000000000 : ℝ)*base70 + (12814499499634899549/1419500000000000000000000000000000 : ℝ)*base72 + (17304553095657/14195000000000000000000000000 : ℝ)*base74 + (38654560631294899549/1419500000000000000000000000000000 : ℝ)*base76 + (7567914632350899549/1419500000000000000000000000000000 : ℝ)*base78 + (17726056126041899549/1419500000000000000000000000000000 : ℝ)*base80 + (56524074150971/7097500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9829337/2500000000000000000000 : ℝ)*base89 + (9829337/2500000000000000000000 : ℝ)*base91 + (9829337/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120262258864584543895840977/20875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (134321469/50000000000000 : ℝ)*(base8) + (5727633/4000000000000 : ℝ)*(base15) + (47968407/50000000000000 : ℝ)*(lower2) + (9930069/10000000000000 : ℝ)*(upper3) + (7130743/50000000000000 : ℝ)*(upper5) + (1454659233328893/25000000000000 : ℝ)*(major0) + (1454659233328893/25000000000000 : ℝ)*(major1) + (1454659233328893/25000000000000 : ℝ)*(major2) + (9712929377/100000000000000 : ℝ)*(sp2) + (468381667/20000000000000 : ℝ)*(sp3) + (964293278799541/12500000000000 : ℝ)*(sp4) + (7714346355848441/100000000000000 : ℝ)*(sp5) + (120536512282967/1562500000000 : ℝ)*(sp6) + (980731208411997/25000000000000 : ℝ)*(sp7) + (3922927175556323/100000000000000 : ℝ)*(f.failure) + (3857173249519633/50000000000000 : ℝ)*(f.sum) + (37608487057357/14195000000000000000000000000 : ℝ)*base65 + (3210611480524392797/709750000000000000000000000000000 : ℝ)*base67 + (13255344625078392797/709750000000000000000000000000000 : ℝ)*base69 + (1800806821835107203/709750000000000000000000000000000 : ℝ)*base72 + (39543899969787/3548750000000000000000000000 : ℝ)*base74 + (6232136316637892797/709750000000000000000000000000000 : ℝ)*base75 + (2193419357090107203/709750000000000000000000000000000 : ℝ)*base78 + (10669190161830142797/709750000000000000000000000000000 : ℝ)*base79 + (62781790585517/14195000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (38172933/5000000000000000000000 : ℝ)*base90 + (38172933/5000000000000000000000 : ℝ)*base92 + (38172933/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1083_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1083_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1083_s7_0 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-439083319/2000000000 : ℝ)*x 0 + (5394140667/10000000000 : ℝ)*x 1 + (2632342517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439083319/2000000000 : ℝ)^2069 ≤ (3333673200163/25000000000000 : ℝ)^1557 := by
    have hnat : (439083319 : ℕ)^2069*25000000000000^1557 ≤ 3333673200163^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439083319 2000000000 3333673200163 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394140667/10000000000 : ℝ)^2069 ≤ (44031983981907/100000000000000 : ℝ)^1557 := by
    have hnat : (5394140667 : ℕ)^2069*100000000000000^1557 ≤ 44031983981907^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394140667 10000000000 44031983981907 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632342517/5000000000 : ℝ)^2069 ≤ (21316661599951/50000000000000 : ℝ)^1557 := by
    have hnat : (2632342517 : ℕ)^2069*50000000000000^1557 ≤ 21316661599951^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632342517 5000000000 21316661599951 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439083319/2000000000 : ℝ), (5394140667/10000000000 : ℝ), (2632342517/5000000000 : ℝ)] ![(3333673200163/25000000000000 : ℝ), (44031983981907/100000000000000 : ℝ), (21316661599951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439083319/2000000000 : ℝ)|^2069 ≤ (3333673200163/25000000000000 : ℝ)^1557
        have hw : |(-439083319/2000000000 : ℝ)|=(439083319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394140667/10000000000 : ℝ)|^2069 ≤ (44031983981907/100000000000000 : ℝ)^1557
        have hw : |(5394140667/10000000000 : ℝ)|=(5394140667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632342517/5000000000 : ℝ)|^2069 ≤ (21316661599951/50000000000000 : ℝ)^1557
        have hw : |(2632342517/5000000000 : ℝ)|=(2632342517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s7_1 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344958013/10000000000 : ℝ)*x 0 + (-90443797/400000000 : ℝ)*x 1 + (658085629/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344958013/10000000000 : ℝ)^2069 ≤ (173997164197/400000000000 : ℝ)^1557 := by
    have hnat : (5344958013 : ℕ)^2069*400000000000^1557 ≤ 173997164197^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344958013 10000000000 173997164197 400000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90443797/400000000 : ℝ)^2069 ≤ (6933692880509/50000000000000 : ℝ)^1557 := by
    have hnat : (90443797 : ℕ)^2069*50000000000000^1557 ≤ 6933692880509^1557*400000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90443797 400000000 6933692880509 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658085629/1250000000 : ℝ)^2069 ≤ (2131666158919/5000000000000 : ℝ)^1557 := by
    have hnat : (658085629 : ℕ)^2069*5000000000000^1557 ≤ 2131666158919^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658085629 1250000000 2131666158919 5000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344958013/10000000000 : ℝ), (-90443797/400000000 : ℝ), (658085629/1250000000 : ℝ)] ![(173997164197/400000000000 : ℝ), (6933692880509/50000000000000 : ℝ), (2131666158919/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344958013/10000000000 : ℝ)|^2069 ≤ (173997164197/400000000000 : ℝ)^1557
        have hw : |(5344958013/10000000000 : ℝ)|=(5344958013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90443797/400000000 : ℝ)|^2069 ≤ (6933692880509/50000000000000 : ℝ)^1557
        have hw : |(-90443797/400000000 : ℝ)|=(90443797/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658085629/1250000000 : ℝ)|^2069 ≤ (2131666158919/5000000000000 : ℝ)^1557
        have hw : |(658085629/1250000000 : ℝ)|=(658085629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s7_2 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344958013/10000000000 : ℝ)*x 0 + (658085629/1250000000 : ℝ)*x 1 + (-90443797/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344958013/10000000000 : ℝ)^2069 ≤ (173997164197/400000000000 : ℝ)^1557 := by
    have hnat : (5344958013 : ℕ)^2069*400000000000^1557 ≤ 173997164197^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344958013 10000000000 173997164197 400000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658085629/1250000000 : ℝ)^2069 ≤ (2131666158919/5000000000000 : ℝ)^1557 := by
    have hnat : (658085629 : ℕ)^2069*5000000000000^1557 ≤ 2131666158919^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658085629 1250000000 2131666158919 5000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90443797/400000000 : ℝ)^2069 ≤ (6933692880509/50000000000000 : ℝ)^1557 := by
    have hnat : (90443797 : ℕ)^2069*50000000000000^1557 ≤ 6933692880509^1557*400000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90443797 400000000 6933692880509 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344958013/10000000000 : ℝ), (658085629/1250000000 : ℝ), (-90443797/400000000 : ℝ)] ![(173997164197/400000000000 : ℝ), (2131666158919/5000000000000 : ℝ), (6933692880509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344958013/10000000000 : ℝ)|^2069 ≤ (173997164197/400000000000 : ℝ)^1557
        have hw : |(5344958013/10000000000 : ℝ)|=(5344958013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658085629/1250000000 : ℝ)|^2069 ≤ (2131666158919/5000000000000 : ℝ)^1557
        have hw : |(658085629/1250000000 : ℝ)|=(658085629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90443797/400000000 : ℝ)|^2069 ≤ (6933692880509/50000000000000 : ℝ)^1557
        have hw : |(-90443797/400000000 : ℝ)|=(90443797/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s7_3 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (218652449/500000000 : ℝ)*x 0 + (2123816177/5000000000 : ℝ)*x 1 + (4502203913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218652449/500000000 : ℝ)^2069 ≤ (33316606521397/100000000000000 : ℝ)^1557 := by
    have hnat : (218652449 : ℕ)^2069*100000000000000^1557 ≤ 33316606521397^1557*500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218652449 500000000 33316606521397 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123816177/5000000000 : ℝ)^2069 ≤ (32052925934427/100000000000000 : ℝ)^1557 := by
    have hnat : (2123816177 : ℕ)^2069*100000000000000^1557 ≤ 32052925934427^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123816177 5000000000 32052925934427 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502203913/10000000000 : ℝ)^2069 ≤ (2164404220263/6250000000000 : ℝ)^1557 := by
    have hnat : (4502203913 : ℕ)^2069*6250000000000^1557 ≤ 2164404220263^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502203913 10000000000 2164404220263 6250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218652449/500000000 : ℝ), (2123816177/5000000000 : ℝ), (4502203913/10000000000 : ℝ)] ![(33316606521397/100000000000000 : ℝ), (32052925934427/100000000000000 : ℝ), (2164404220263/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218652449/500000000 : ℝ)|^2069 ≤ (33316606521397/100000000000000 : ℝ)^1557
        have hw : |(218652449/500000000 : ℝ)|=(218652449/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123816177/5000000000 : ℝ)|^2069 ≤ (32052925934427/100000000000000 : ℝ)^1557
        have hw : |(2123816177/5000000000 : ℝ)|=(2123816177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502203913/10000000000 : ℝ)|^2069 ≤ (2164404220263/6250000000000 : ℝ)^1557
        have hw : |(4502203913/10000000000 : ℝ)|=(4502203913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s7_4 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-439084327/2000000000 : ℝ)*x 0 + (5265009867/10000000000 : ℝ)*x 1 + (2696907331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439084327/2000000000 : ℝ)^2069 ≤ (26669466959/200000000000 : ℝ)^1557 := by
    have hnat : (439084327 : ℕ)^2069*200000000000^1557 ≤ 26669466959^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439084327 2000000000 26669466959 200000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265009867/10000000000 : ℝ)^2069 ≤ (8527363746279/20000000000000 : ℝ)^1557 := by
    have hnat : (5265009867 : ℕ)^2069*20000000000000^1557 ≤ 8527363746279^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265009867 10000000000 8527363746279 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696907331/5000000000 : ℝ)^2069 ≤ (11007111943461/25000000000000 : ℝ)^1557 := by
    have hnat : (2696907331 : ℕ)^2069*25000000000000^1557 ≤ 11007111943461^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696907331 5000000000 11007111943461 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439084327/2000000000 : ℝ), (5265009867/10000000000 : ℝ), (2696907331/5000000000 : ℝ)] ![(26669466959/200000000000 : ℝ), (8527363746279/20000000000000 : ℝ), (11007111943461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439084327/2000000000 : ℝ)|^2069 ≤ (26669466959/200000000000 : ℝ)^1557
        have hw : |(-439084327/2000000000 : ℝ)|=(439084327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265009867/10000000000 : ℝ)|^2069 ≤ (8527363746279/20000000000000 : ℝ)^1557
        have hw : |(5265009867/10000000000 : ℝ)|=(5265009867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696907331/5000000000 : ℝ)|^2069 ≤ (11007111943461/25000000000000 : ℝ)^1557
        have hw : |(2696907331/5000000000 : ℝ)|=(2696907331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s7_5 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312306877/10000000000 : ℝ)*x 0 + (-2131965297/10000000000 : ℝ)*x 1 + (5393814661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312306877/10000000000 : ℝ)^2069 ≤ (21573268895697/50000000000000 : ℝ)^1557 := by
    have hnat : (5312306877 : ℕ)^2069*50000000000000^1557 ≤ 21573268895697^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312306877 10000000000 21573268895697 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2131965297/10000000000 : ℝ)^2069 ≤ (3206253605819/25000000000000 : ℝ)^1557 := by
    have hnat : (2131965297 : ℕ)^2069*25000000000000^1557 ≤ 3206253605819^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131965297 10000000000 3206253605819 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393814661/10000000000 : ℝ)^2069 ≤ (44028447762997/100000000000000 : ℝ)^1557 := by
    have hnat : (5393814661 : ℕ)^2069*100000000000000^1557 ≤ 44028447762997^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393814661 10000000000 44028447762997 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312306877/10000000000 : ℝ), (-2131965297/10000000000 : ℝ), (5393814661/10000000000 : ℝ)] ![(21573268895697/50000000000000 : ℝ), (3206253605819/25000000000000 : ℝ), (44028447762997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312306877/10000000000 : ℝ)|^2069 ≤ (21573268895697/50000000000000 : ℝ)^1557
        have hw : |(5312306877/10000000000 : ℝ)|=(5312306877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2131965297/10000000000 : ℝ)|^2069 ≤ (3206253605819/25000000000000 : ℝ)^1557
        have hw : |(-2131965297/10000000000 : ℝ)|=(2131965297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393814661/10000000000 : ℝ)|^2069 ≤ (44028447762997/100000000000000 : ℝ)^1557
        have hw : |(5393814661/10000000000 : ℝ)|=(5393814661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s7_6 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312306879/10000000000 : ℝ)*x 0 + (269690733/500000000 : ℝ)*x 1 + (-133247831/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312306879/10000000000 : ℝ)^2069 ≤ (2157326890649/5000000000000 : ℝ)^1557 := by
    have hnat : (5312306879 : ℕ)^2069*5000000000000^1557 ≤ 2157326890649^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312306879 10000000000 2157326890649 5000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269690733/500000000 : ℝ)^2069 ≤ (880568955043/2000000000000 : ℝ)^1557 := by
    have hnat : (269690733 : ℕ)^2069*2000000000000^1557 ≤ 880568955043^1557*500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269690733 500000000 880568955043 2000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133247831/625000000 : ℝ)^2069 ≤ (6412507207641/50000000000000 : ℝ)^1557 := by
    have hnat : (133247831 : ℕ)^2069*50000000000000^1557 ≤ 6412507207641^1557*625000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133247831 625000000 6412507207641 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312306879/10000000000 : ℝ), (269690733/500000000 : ℝ), (-133247831/625000000 : ℝ)] ![(2157326890649/5000000000000 : ℝ), (880568955043/2000000000000 : ℝ), (6412507207641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312306879/10000000000 : ℝ)|^2069 ≤ (2157326890649/5000000000000 : ℝ)^1557
        have hw : |(5312306879/10000000000 : ℝ)|=(5312306879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269690733/500000000 : ℝ)|^2069 ≤ (880568955043/2000000000000 : ℝ)^1557
        have hw : |(269690733/500000000 : ℝ)|=(269690733/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133247831/625000000 : ℝ)|^2069 ≤ (6412507207641/50000000000000 : ℝ)^1557
        have hw : |(-133247831/625000000 : ℝ)|=(133247831/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s7_7 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4373058889/10000000000 : ℝ)*x 0 + (1125391283/2500000000 : ℝ)*x 1 + (1062068361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373058889/10000000000 : ℝ)^2069 ≤ (33316706839263/100000000000000 : ℝ)^1557 := by
    have hnat : (4373058889 : ℕ)^2069*100000000000000^1557 ≤ 33316706839263^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373058889 10000000000 33316706839263 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125391283/2500000000 : ℝ)^2069 ≤ (34623938520279/100000000000000 : ℝ)^1557 := by
    have hnat : (1125391283 : ℕ)^2069*100000000000000^1557 ≤ 34623938520279^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125391283 2500000000 34623938520279 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062068361/2500000000 : ℝ)^2069 ≤ (400741932793/1250000000000 : ℝ)^1557 := by
    have hnat : (1062068361 : ℕ)^2069*1250000000000^1557 ≤ 400741932793^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062068361 2500000000 400741932793 1250000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373058889/10000000000 : ℝ), (1125391283/2500000000 : ℝ), (1062068361/2500000000 : ℝ)] ![(33316706839263/100000000000000 : ℝ), (34623938520279/100000000000000 : ℝ), (400741932793/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373058889/10000000000 : ℝ)|^2069 ≤ (33316706839263/100000000000000 : ℝ)^1557
        have hw : |(4373058889/10000000000 : ℝ)|=(4373058889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125391283/2500000000 : ℝ)|^2069 ≤ (34623938520279/100000000000000 : ℝ)^1557
        have hw : |(1125391283/2500000000 : ℝ)|=(1125391283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062068361/2500000000 : ℝ)|^2069 ≤ (400741932793/1250000000000 : ℝ)^1557
        have hw : |(1062068361/2500000000 : ℝ)|=(1062068361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1083_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11273/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2803/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2253/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2253/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2253/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2253/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2253/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2253/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2253/20000 : ℝ) ^ (8275/2048 : ℝ) ≤ (460621271834299/3125000000000000000 : ℝ) := by
    have hpowers : (2253/20000 : ℝ)^8275 ≤ (460621271834299/3125000000000000000 : ℝ)^2048 := by
      have hnat : (2253 : ℕ)^8275*3125000000000000000^2048 ≤ 460621271834299^2048*20000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2253 20000 460621271834299 3125000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2253/20000 : ℝ)) (X := (460621271834299/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1753/12500 : ℝ) ^ (8275/2048 : ℝ) ≤ (35720094296202213/100000000000000000000 : ℝ) := by
    have hpowers : (1753/12500 : ℝ)^8275 ≤ (35720094296202213/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1753 : ℕ)^8275*100000000000000000000^2048 ≤ 35720094296202213^2048*12500^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1753 12500 35720094296202213 100000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1753/12500 : ℝ)) (X := (35720094296202213/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562960621271834299/1562500000000000000 : ℝ) ≤ (10000729520916341/10000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (1562960621271834299/1562500000000000000 : ℝ)^2048 ≤ (10000729520916341/10000000000000000 : ℝ)^8275 := by
      have hnat : (1562960621271834299 : ℕ)^2048*10000000000000000^8275 ≤ 10000729520916341^8275*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562960621271834299 1562500000000000000 10000729520916341 10000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000729520916341/10000000000000000 : ℝ)) (X := (1562960621271834299/1562500000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050459974994899781/100000000000000000000 : ℝ) ≤ (62507803807727/62500000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (100050459974994899781/100000000000000000000 : ℝ)^2048 ≤ (62507803807727/62500000000000 : ℝ)^8275 := by
      have hnat : (100050459974994899781 : ℕ)^2048*62500000000000^8275 ≤ 62507803807727^8275*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050459974994899781 100000000000000000000 62507803807727 62500000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62507803807727/62500000000000 : ℝ)) (X := (100050459974994899781/100000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035720094296202213/50000000000000000000 : ℝ) ≤ (10001767697556299/10000000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (50035720094296202213/50000000000000000000 : ℝ)^2048 ≤ (10001767697556299/10000000000000000 : ℝ)^8275 := by
      have hnat : (50035720094296202213 : ℕ)^2048*10000000000000000^8275 ≤ 10001767697556299^8275*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035720094296202213 50000000000000000000 10001767697556299 10000000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001767697556299/10000000000000000 : ℝ)) (X := (50035720094296202213/50000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(460621271834299/3125000000000000000 : ℝ) ≤ ((27580317688359057949/27590000000000000000 : ℝ)+2*(519088319979/275900000000000 : ℝ)*(2253/20000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (27580317688359057949/27590000000000000000 : ℝ)+2*(519088319979/275900000000000 : ℝ)*(2253/20000 : ℝ)=(10000729520916341/10000000000000000 : ℝ) by norm_num, show 1+2*(460621271834299/3125000000000000000 : ℝ)=(1562960621271834299/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35720094296202213/100000000000000000000 : ℝ)+(460621271834299/3125000000000000000 : ℝ) ≤ ((27580317688359057949/27590000000000000000 : ℝ)+(519088319979/275900000000000 : ℝ)*((1753/12500 : ℝ)+(2253/20000 : ℝ)))^(8275/2048 : ℝ) := by
    rw [show (27580317688359057949/27590000000000000000 : ℝ)+(519088319979/275900000000000 : ℝ)*((1753/12500 : ℝ)+(2253/20000 : ℝ))=(62507803807727/62500000000000 : ℝ) by norm_num, show 1+(35720094296202213/100000000000000000000 : ℝ)+(460621271834299/3125000000000000000 : ℝ)=(100050459974994899781/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35720094296202213/100000000000000000000 : ℝ) ≤ ((27580317688359057949/27590000000000000000 : ℝ)+2*(519088319979/275900000000000 : ℝ)*(1753/12500 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (27580317688359057949/27590000000000000000 : ℝ)+2*(519088319979/275900000000000 : ℝ)*(1753/12500 : ℝ)=(10001767697556299/10000000000000000 : ℝ) by norm_num, show 1+2*(35720094296202213/100000000000000000000 : ℝ)=(50035720094296202213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27580317688359057949/27590000000000000000 : ℝ)*(X 1 0+X 2 0)+(519088319979/275900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (27580317688359057949/27590000000000000000 : ℝ)) (alpha := (519088319979/275900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27580317688359057949/27590000000000000000 : ℝ)*(X 0 1+X 2 1)+(519088319979/275900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (27580317688359057949/27590000000000000000 : ℝ)) (alpha := (519088319979/275900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27580317688359057949/27590000000000000000 : ℝ)*(X 0 2+X 1 2)+(519088319979/275900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (27580317688359057949/27590000000000000000 : ℝ)) (alpha := (519088319979/275900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-439083319/2000000000 : ℝ)*X 0 0+(5394140667/10000000000 : ℝ)*X 0 1+(2632342517/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344958013/10000000000 : ℝ)*X 1 0+(-90443797/400000000 : ℝ)*X 1 1+(658085629/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344958013/10000000000 : ℝ)*X 2 0+(658085629/1250000000 : ℝ)*X 2 1+(-90443797/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218652449/500000000 : ℝ)*X 0 0+(2123816177/5000000000 : ℝ)*X 0 1+(4502203913/10000000000 : ℝ)*X 0 2+(218652449/500000000 : ℝ)*X 1 0+(2123816177/5000000000 : ℝ)*X 1 1+(4502203913/10000000000 : ℝ)*X 1 2+(218652449/500000000 : ℝ)*X 2 0+(2123816177/5000000000 : ℝ)*X 2 1+(4502203913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-439084327/2000000000 : ℝ)*X 0 0+(5265009867/10000000000 : ℝ)*X 0 1+(2696907331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312306877/10000000000 : ℝ)*X 1 0+(-2131965297/10000000000 : ℝ)*X 1 1+(5393814661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312306879/10000000000 : ℝ)*X 2 0+(269690733/500000000 : ℝ)*X 2 1+(-133247831/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373058889/10000000000 : ℝ)*X 0 0+(1125391283/2500000000 : ℝ)*X 0 1+(1062068361/2500000000 : ℝ)*X 0 2+(4373058889/10000000000 : ℝ)*X 1 0+(1125391283/2500000000 : ℝ)*X 1 1+(1062068361/2500000000 : ℝ)*X 1 2+(4373058889/10000000000 : ℝ)*X 2 0+(1125391283/2500000000 : ℝ)*X 2 1+(1062068361/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5498638874230977726398005029/689750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (796328329/50000000000000 : ℝ)*(base19) + (1478867679/100000000000000 : ℝ)*(base23) + (60819731/100000000000000 : ℝ)*(lower2) + (25374241/12500000000000 : ℝ)*(upper3) + (23673111/20000000000000 : ℝ)*(upper5) + (2913238769140769/50000000000000 : ℝ)*(major0) + (2913238769140769/50000000000000 : ℝ)*(major1) + (2913238769140769/50000000000000 : ℝ)*(major2) + (7724698931972029/100000000000000 : ℝ)*(sp0) + (7724739903847011/100000000000000 : ℝ)*(sp1) + (7724740017635989/100000000000000 : ℝ)*(sp2) + (3928189732174623/100000000000000 : ℝ)*(sp3) + (42564531639/100000000000000 : ℝ)*(sp4) + (23582153769/100000000000000 : ℝ)*(sp7) + (491026664291049/12500000000000 : ℝ)*(f.failure) + (1931185374125917/25000000000000 : ℝ)*(f.sum) + (26459993756707/13795000000000000000000000000 : ℝ)*base65 + (17417023646682477219/1379500000000000000000000000000000 : ℝ)*base68 + (8885360818805977219/1379500000000000000000000000000000 : ℝ)*base70 + (2351733030563477219/1379500000000000000000000000000000 : ℝ)*base72 + (52716542747923/13795000000000000000000000000 : ℝ)*base74 + (32675713401871977219/1379500000000000000000000000000000 : ℝ)*base76 + (2009866325526477219/1379500000000000000000000000000000 : ℝ)*base78 + (11359268463996477219/1379500000000000000000000000000000 : ℝ)*base80 + (7857049917281/1724375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1226479/625000000000000000000 : ℝ)*base90 + (1226479/625000000000000000000 : ℝ)*base92 + (1226479/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5548331157662912178505158933/1379500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36719769/5000000000000 : ℝ)*(base19) + (806310769/100000000000000 : ℝ)*(base23) + (79338149/100000000000000 : ℝ)*(upper3) + (31117153/100000000000000 : ℝ)*(lower4) + (80713017/100000000000000 : ℝ)*(upper5) + (5855851353187087/100000000000000 : ℝ)*(major0) + (5855851353187087/100000000000000 : ℝ)*(major1) + (5855851353187087/100000000000000 : ℝ)*(major2) + (19992437743/100000000000000 : ℝ)*(sp1) + (216872567/1000000000000 : ℝ)*(sp2) + (77636854210907/1000000000000 : ℝ)*(sp4) + (7763664694257577/100000000000000 : ℝ)*(sp5) + (242614466485101/3125000000000 : ℝ)*(sp6) + (987004287804307/25000000000000 : ℝ)*(sp7) + (987004287804307/25000000000000 : ℝ)*(f.failure) + (77636854210907/1000000000000 : ℝ)*(f.sum) + (15524926512467/13795000000000000000000000000 : ℝ)*base66 + (5731343059224804563/2759000000000000000000000000000000 : ℝ)*base67 + (29661789909500804563/2759000000000000000000000000000000 : ℝ)*base69 + (37552406449768804563/2759000000000000000000000000000000 : ℝ)*base71 + (132856771354167/13795000000000000000000000000 : ℝ)*base74 + (61652241031793804563/2759000000000000000000000000000000 : ℝ)*base75 + (10290980339708804563/2759000000000000000000000000000000 : ℝ)*base77 + (20955619226644804563/2759000000000000000000000000000000 : ℝ)*base79 + (3930936328473/13795000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5871797/1250000000000000000000 : ℝ)*base90 + (5871797/1250000000000000000000 : ℝ)*base92 + (5871797/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1083_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1083_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1083_s8_0 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195426497/10000000000 : ℝ)*x 0 + (5394049899/10000000000 : ℝ)*x 1 + (5264769103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195426497/10000000000 : ℝ)^2069 ≤ (1666846590213/12500000000000 : ℝ)^1557 := by
    have hnat : (2195426497 : ℕ)^2069*12500000000000^1557 ≤ 1666846590213^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195426497 10000000000 1666846590213 12500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394049899/10000000000 : ℝ)^2069 ≤ (44030999405489/100000000000000 : ℝ)^1557 := by
    have hnat : (5394049899 : ℕ)^2069*100000000000000^1557 ≤ 44030999405489^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394049899 10000000000 44030999405489 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264769103/10000000000 : ℝ)^2069 ≤ (8526845572107/20000000000000 : ℝ)^1557 := by
    have hnat : (5264769103 : ℕ)^2069*20000000000000^1557 ≤ 8526845572107^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264769103 10000000000 8526845572107 20000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195426497/10000000000 : ℝ), (5394049899/10000000000 : ℝ), (5264769103/10000000000 : ℝ)] ![(1666846590213/12500000000000 : ℝ), (44030999405489/100000000000000 : ℝ), (8526845572107/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195426497/10000000000 : ℝ)|^2069 ≤ (1666846590213/12500000000000 : ℝ)^1557
        have hw : |(-2195426497/10000000000 : ℝ)|=(2195426497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394049899/10000000000 : ℝ)|^2069 ≤ (44030999405489/100000000000000 : ℝ)^1557
        have hw : |(5394049899/10000000000 : ℝ)|=(5394049899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264769103/10000000000 : ℝ)|^2069 ≤ (8526845572107/20000000000000 : ℝ)^1557
        have hw : |(5264769103/10000000000 : ℝ)|=(5264769103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s8_1 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068986943/2000000000 : ℝ)*x 0 + (-565253707/2500000000 : ℝ)*x 1 + (5264769107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068986943/2000000000 : ℝ)^2069 ≤ (43499039091287/100000000000000 : ℝ)^1557 := by
    have hnat : (1068986943 : ℕ)^2069*100000000000000^1557 ≤ 43499039091287^1557*2000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068986943 2000000000 43499039091287 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565253707/2500000000 : ℝ)^2069 ≤ (6933366494597/50000000000000 : ℝ)^1557 := by
    have hnat : (565253707 : ℕ)^2069*50000000000000^1557 ≤ 6933366494597^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565253707 2500000000 6933366494597 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264769107/10000000000 : ℝ)^2069 ≤ (42634227903579/100000000000000 : ℝ)^1557 := by
    have hnat : (5264769107 : ℕ)^2069*100000000000000^1557 ≤ 42634227903579^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264769107 10000000000 42634227903579 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068986943/2000000000 : ℝ), (-565253707/2500000000 : ℝ), (5264769107/10000000000 : ℝ)] ![(43499039091287/100000000000000 : ℝ), (6933366494597/50000000000000 : ℝ), (42634227903579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068986943/2000000000 : ℝ)|^2069 ≤ (43499039091287/100000000000000 : ℝ)^1557
        have hw : |(1068986943/2000000000 : ℝ)|=(1068986943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-565253707/2500000000 : ℝ)|^2069 ≤ (6933366494597/50000000000000 : ℝ)^1557
        have hw : |(-565253707/2500000000 : ℝ)|=(565253707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264769107/10000000000 : ℝ)|^2069 ≤ (42634227903579/100000000000000 : ℝ)^1557
        have hw : |(5264769107/10000000000 : ℝ)|=(5264769107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s8_2 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672467353/5000000000 : ℝ)*x 0 + (1316192277/2500000000 : ℝ)*x 1 + (-1130507419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672467353/5000000000 : ℝ)^2069 ≤ (10874759748489/25000000000000 : ℝ)^1557 := by
    have hnat : (2672467353 : ℕ)^2069*25000000000000^1557 ≤ 10874759748489^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672467353 5000000000 10874759748489 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316192277/2500000000 : ℝ)^2069 ≤ (2131711395717/5000000000000 : ℝ)^1557 := by
    have hnat : (1316192277 : ℕ)^2069*5000000000000^1557 ≤ 2131711395717^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316192277 2500000000 2131711395717 5000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130507419/5000000000 : ℝ)^2069 ≤ (13866733070691/100000000000000 : ℝ)^1557 := by
    have hnat : (1130507419 : ℕ)^2069*100000000000000^1557 ≤ 13866733070691^1557*5000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130507419 5000000000 13866733070691 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672467353/5000000000 : ℝ), (1316192277/2500000000 : ℝ), (-1130507419/5000000000 : ℝ)] ![(10874759748489/25000000000000 : ℝ), (2131711395717/5000000000000 : ℝ), (13866733070691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672467353/5000000000 : ℝ)|^2069 ≤ (10874759748489/25000000000000 : ℝ)^1557
        have hw : |(2672467353/5000000000 : ℝ)|=(2672467353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316192277/2500000000 : ℝ)|^2069 ≤ (2131711395717/5000000000000 : ℝ)^1557
        have hw : |(1316192277/2500000000 : ℝ)|=(1316192277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1130507419/5000000000 : ℝ)|^2069 ≤ (13866733070691/100000000000000 : ℝ)^1557
        have hw : |(-1130507419/5000000000 : ℝ)|=(1130507419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s8_3 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4373053431/10000000000 : ℝ)*x 0 + (530975461/1250000000 : ℝ)*x 1 + (562753927/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373053431/10000000000 : ℝ)^2069 ≤ (3331665158293/10000000000000 : ℝ)^1557 := by
    have hnat : (4373053431 : ℕ)^2069*10000000000000^1557 ≤ 3331665158293^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373053431 10000000000 3331665158293 10000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530975461/1250000000 : ℝ)^2069 ≤ (500853812459/1562500000000 : ℝ)^1557 := by
    have hnat : (530975461 : ℕ)^2069*1562500000000^1557 ≤ 500853812459^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530975461 1250000000 500853812459 1562500000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562753927/1250000000 : ℝ)^2069 ≤ (34628704396047/100000000000000 : ℝ)^1557 := by
    have hnat : (562753927 : ℕ)^2069*100000000000000^1557 ≤ 34628704396047^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562753927 1250000000 34628704396047 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373053431/10000000000 : ℝ), (530975461/1250000000 : ℝ), (562753927/1250000000 : ℝ)] ![(3331665158293/10000000000000 : ℝ), (500853812459/1562500000000 : ℝ), (34628704396047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373053431/10000000000 : ℝ)|^2069 ≤ (3331665158293/10000000000000 : ℝ)^1557
        have hw : |(4373053431/10000000000 : ℝ)|=(4373053431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530975461/1250000000 : ℝ)|^2069 ≤ (500853812459/1562500000000 : ℝ)^1557
        have hw : |(530975461/1250000000 : ℝ)|=(530975461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562753927/1250000000 : ℝ)|^2069 ≤ (34628704396047/100000000000000 : ℝ)^1557
        have hw : |(562753927/1250000000 : ℝ)|=(562753927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s8_4 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-274428939/1250000000 : ℝ)*x 0 + (5265093067/10000000000 : ℝ)*x 1 + (5393724771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274428939/1250000000 : ℝ)^2069 ≤ (13334813198833/100000000000000 : ℝ)^1557 := by
    have hnat : (274428939 : ℕ)^2069*100000000000000^1557 ≤ 13334813198833^1557*1250000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274428939 1250000000 13334813198833 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265093067/10000000000 : ℝ)^2069 ≤ (1065942851473/2500000000000 : ℝ)^1557 := by
    have hnat : (5265093067 : ℕ)^2069*2500000000000^1557 ≤ 1065942851473^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265093067 10000000000 1065942851473 2500000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393724771/10000000000 : ℝ)^2069 ≤ (44027472729753/100000000000000 : ℝ)^1557 := by
    have hnat : (5393724771 : ℕ)^2069*100000000000000^1557 ≤ 44027472729753^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393724771 10000000000 44027472729753 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-274428939/1250000000 : ℝ), (5265093067/10000000000 : ℝ), (5393724771/10000000000 : ℝ)] ![(13334813198833/100000000000000 : ℝ), (1065942851473/2500000000000 : ℝ), (44027472729753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-274428939/1250000000 : ℝ)|^2069 ≤ (13334813198833/100000000000000 : ℝ)^1557
        have hw : |(-274428939/1250000000 : ℝ)|=(274428939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265093067/10000000000 : ℝ)|^2069 ≤ (1065942851473/2500000000000 : ℝ)^1557
        have hw : |(5265093067/10000000000 : ℝ)|=(5265093067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393724771/10000000000 : ℝ)|^2069 ≤ (44027472729753/100000000000000 : ℝ)^1557
        have hw : |(5393724771/10000000000 : ℝ)|=(5393724771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s8_5 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328081923/2500000000 : ℝ)*x 0 + (-2132059169/10000000000 : ℝ)*x 1 + (5393724771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328081923/2500000000 : ℝ)^2069 ≤ (43146762443953/100000000000000 : ℝ)^1557 := by
    have hnat : (1328081923 : ℕ)^2069*100000000000000^1557 ≤ 43146762443953^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328081923 2500000000 43146762443953 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132059169/10000000000 : ℝ)^2069 ≤ (6412882408181/50000000000000 : ℝ)^1557 := by
    have hnat : (2132059169 : ℕ)^2069*50000000000000^1557 ≤ 6412882408181^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132059169 10000000000 6412882408181 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393724771/10000000000 : ℝ)^2069 ≤ (44027472729753/100000000000000 : ℝ)^1557 := by
    have hnat : (5393724771 : ℕ)^2069*100000000000000^1557 ≤ 44027472729753^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393724771 10000000000 44027472729753 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328081923/2500000000 : ℝ), (-2132059169/10000000000 : ℝ), (5393724771/10000000000 : ℝ)] ![(43146762443953/100000000000000 : ℝ), (6412882408181/50000000000000 : ℝ), (44027472729753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328081923/2500000000 : ℝ)|^2069 ≤ (43146762443953/100000000000000 : ℝ)^1557
        have hw : |(1328081923/2500000000 : ℝ)|=(1328081923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132059169/10000000000 : ℝ)|^2069 ≤ (6412882408181/50000000000000 : ℝ)^1557
        have hw : |(-2132059169/10000000000 : ℝ)|=(2132059169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393724771/10000000000 : ℝ)|^2069 ≤ (44027472729753/100000000000000 : ℝ)^1557
        have hw : |(5393724771/10000000000 : ℝ)|=(5393724771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s8_6 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328081923/2500000000 : ℝ)*x 0 + (5393724771/10000000000 : ℝ)*x 1 + (-2132059169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328081923/2500000000 : ℝ)^2069 ≤ (43146762443953/100000000000000 : ℝ)^1557 := by
    have hnat : (1328081923 : ℕ)^2069*100000000000000^1557 ≤ 43146762443953^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328081923 2500000000 43146762443953 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393724771/10000000000 : ℝ)^2069 ≤ (44027472729753/100000000000000 : ℝ)^1557 := by
    have hnat : (5393724771 : ℕ)^2069*100000000000000^1557 ≤ 44027472729753^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393724771 10000000000 44027472729753 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132059169/10000000000 : ℝ)^2069 ≤ (6412882408181/50000000000000 : ℝ)^1557 := by
    have hnat : (2132059169 : ℕ)^2069*50000000000000^1557 ≤ 6412882408181^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132059169 10000000000 6412882408181 50000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328081923/2500000000 : ℝ), (5393724771/10000000000 : ℝ), (-2132059169/10000000000 : ℝ)] ![(43146762443953/100000000000000 : ℝ), (44027472729753/100000000000000 : ℝ), (6412882408181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328081923/2500000000 : ℝ)|^2069 ≤ (43146762443953/100000000000000 : ℝ)^1557
        have hw : |(1328081923/2500000000 : ℝ)|=(1328081923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393724771/10000000000 : ℝ)|^2069 ≤ (44027472729753/100000000000000 : ℝ)^1557
        have hw : |(5393724771/10000000000 : ℝ)|=(5393724771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132059169/10000000000 : ℝ)|^2069 ≤ (6412882408181/50000000000000 : ℝ)^1557
        have hw : |(-2132059169/10000000000 : ℝ)|=(2132059169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1083_s8_7 (p : ℝ) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4373063309/10000000000 : ℝ)*x 0 + (4501394351/10000000000 : ℝ)*x 1 + (1062110761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373063309/10000000000 : ℝ)^2069 ≤ (8329187896747/25000000000000 : ℝ)^1557 := by
    have hnat : (4373063309 : ℕ)^2069*25000000000000^1557 ≤ 8329187896747^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373063309 10000000000 8329187896747 25000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501394351/10000000000 : ℝ)^2069 ≤ (34622193013053/100000000000000 : ℝ)^1557 := by
    have hnat : (4501394351 : ℕ)^2069*100000000000000^1557 ≤ 34622193013053^1557*10000000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501394351 10000000000 34622193013053 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062110761/2500000000 : ℝ)^2069 ≤ (32061055382877/100000000000000 : ℝ)^1557 := by
    have hnat : (1062110761 : ℕ)^2069*100000000000000^1557 ≤ 32061055382877^1557*2500000000^2069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062110761 2500000000 32061055382877 100000000000000 2069 1557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2069/512 : ℝ)) 2069 1557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373063309/10000000000 : ℝ), (4501394351/10000000000 : ℝ), (1062110761/2500000000 : ℝ)] ![(8329187896747/25000000000000 : ℝ), (34622193013053/100000000000000 : ℝ), (32061055382877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373063309/10000000000 : ℝ)|^2069 ≤ (8329187896747/25000000000000 : ℝ)^1557
        have hw : |(4373063309/10000000000 : ℝ)|=(4373063309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501394351/10000000000 : ℝ)|^2069 ≤ (34622193013053/100000000000000 : ℝ)^1557
        have hw : |(4501394351/10000000000 : ℝ)|=(4501394351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062110761/2500000000 : ℝ)|^2069 ≤ (32061055382877/100000000000000 : ℝ)^1557
        have hw : |(1062110761/2500000000 : ℝ)|=(1062110761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1083_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (451/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14013/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2803/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2803/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2803/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2803/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2803/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2803/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11273/100000 : ℝ) ^ (8275/2048 : ℝ) ≤ (923888847347567/6250000000000000000 : ℝ) := by
    have hpowers : (11273/100000 : ℝ)^8275 ≤ (923888847347567/6250000000000000000 : ℝ)^2048 := by
      have hnat : (11273 : ℕ)^8275*6250000000000000000^2048 ≤ 923888847347567^2048*100000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11273 100000 923888847347567 6250000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11273/100000 : ℝ)) (X := (923888847347567/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2803/20000 : ℝ) ^ (8275/2048 : ℝ) ≤ (17813780555005223/50000000000000000000 : ℝ) := by
    have hpowers : (2803/20000 : ℝ)^8275 ≤ (17813780555005223/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2803 : ℕ)^8275*50000000000000000000^2048 ≤ 17813780555005223^2048*20000^8275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2803 20000 17813780555005223 50000000000000000000 8275 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2803/20000 : ℝ)) (X := (17813780555005223/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125923888847347567/3125000000000000000 : ℝ) ≤ (500036580812971/500000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (3125923888847347567/3125000000000000000 : ℝ)^2048 ≤ (500036580812971/500000000000000 : ℝ)^8275 := by
      have hnat : (3125923888847347567 : ℕ)^2048*500000000000000^8275 ≤ 500036580812971^8275*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125923888847347567 3125000000000000000 500036580812971 500000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500036580812971/500000000000000 : ℝ)) (X := (3125923888847347567/3125000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025204891333785759/50000000000000000000 : ℝ) ≤ (156269490116959/156250000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (50025204891333785759/50000000000000000000 : ℝ)^2048 ≤ (156269490116959/156250000000000 : ℝ)^8275 := by
      have hnat : (50025204891333785759 : ℕ)^2048*156250000000000^8275 ≤ 156269490116959^8275*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025204891333785759 50000000000000000000 156269490116959 156250000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156269490116959/156250000000000 : ℝ)) (X := (50025204891333785759/50000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017813780555005223/25000000000000000000 : ℝ) ≤ (2500440779677833/2500000000000000 : ℝ) ^ (8275/2048 : ℝ) := by
    have hpowers : (25017813780555005223/25000000000000000000 : ℝ)^2048 ≤ (2500440779677833/2500000000000000 : ℝ)^8275 := by
      have hnat : (25017813780555005223 : ℕ)^2048*2500000000000000^8275 ≤ 2500440779677833^8275*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017813780555005223 25000000000000000000 2500440779677833 2500000000000000 2048 8275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500440779677833/2500000000000000 : ℝ)) (X := (25017813780555005223/25000000000000000000 : ℝ)) (by norm_num) 8275 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(923888847347567/6250000000000000000 : ℝ) ≤ ((856574311395091427/856875000000000000 : ℝ)+2*(128937806489/68550000000000 : ℝ)*(11273/100000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (856574311395091427/856875000000000000 : ℝ)+2*(128937806489/68550000000000 : ℝ)*(11273/100000 : ℝ)=(500036580812971/500000000000000 : ℝ) by norm_num, show 1+2*(923888847347567/6250000000000000000 : ℝ)=(3125923888847347567/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17813780555005223/50000000000000000000 : ℝ)+(923888847347567/6250000000000000000 : ℝ) ≤ ((856574311395091427/856875000000000000 : ℝ)+(128937806489/68550000000000 : ℝ)*((2803/20000 : ℝ)+(11273/100000 : ℝ)))^(8275/2048 : ℝ) := by
    rw [show (856574311395091427/856875000000000000 : ℝ)+(128937806489/68550000000000 : ℝ)*((2803/20000 : ℝ)+(11273/100000 : ℝ))=(156269490116959/156250000000000 : ℝ) by norm_num, show 1+(17813780555005223/50000000000000000000 : ℝ)+(923888847347567/6250000000000000000 : ℝ)=(50025204891333785759/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17813780555005223/50000000000000000000 : ℝ) ≤ ((856574311395091427/856875000000000000 : ℝ)+2*(128937806489/68550000000000 : ℝ)*(2803/20000 : ℝ))^(8275/2048 : ℝ) := by
    rw [show (856574311395091427/856875000000000000 : ℝ)+2*(128937806489/68550000000000 : ℝ)*(2803/20000 : ℝ)=(2500440779677833/2500000000000000 : ℝ) by norm_num, show 1+2*(17813780555005223/50000000000000000000 : ℝ)=(25017813780555005223/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (856574311395091427/856875000000000000 : ℝ)*(X 1 0+X 2 0)+(128937806489/68550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (856574311395091427/856875000000000000 : ℝ)) (alpha := (128937806489/68550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (856574311395091427/856875000000000000 : ℝ)*(X 0 1+X 2 1)+(128937806489/68550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (856574311395091427/856875000000000000 : ℝ)) (alpha := (128937806489/68550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (856574311395091427/856875000000000000 : ℝ)*(X 0 2+X 1 2)+(128937806489/68550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8275/2048 : ℝ)) (lo := (11273/100000 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (856574311395091427/856875000000000000 : ℝ)) (alpha := (128937806489/68550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2195426497/10000000000 : ℝ)*X 0 0+(5394049899/10000000000 : ℝ)*X 0 1+(5264769103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068986943/2000000000 : ℝ)*X 1 0+(-565253707/2500000000 : ℝ)*X 1 1+(5264769107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672467353/5000000000 : ℝ)*X 2 0+(1316192277/2500000000 : ℝ)*X 2 1+(-1130507419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4373053431/10000000000 : ℝ)*X 0 0+(530975461/1250000000 : ℝ)*X 0 1+(562753927/1250000000 : ℝ)*X 0 2+(4373053431/10000000000 : ℝ)*X 1 0+(530975461/1250000000 : ℝ)*X 1 1+(562753927/1250000000 : ℝ)*X 1 2+(4373053431/10000000000 : ℝ)*X 2 0+(530975461/1250000000 : ℝ)*X 2 1+(562753927/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-274428939/1250000000 : ℝ)*X 0 0+(5265093067/10000000000 : ℝ)*X 0 1+(5393724771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328081923/2500000000 : ℝ)*X 1 0+(-2132059169/10000000000 : ℝ)*X 1 1+(5393724771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328081923/2500000000 : ℝ)*X 2 0+(5393724771/10000000000 : ℝ)*X 2 1+(-2132059169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373063309/10000000000 : ℝ)*X 0 0+(4501394351/10000000000 : ℝ)*X 0 1+(1062110761/2500000000 : ℝ)*X 0 2+(4373063309/10000000000 : ℝ)*X 1 0+(4501394351/10000000000 : ℝ)*X 1 1+(1062110761/2500000000 : ℝ)*X 1 2+(4373063309/10000000000 : ℝ)*X 2 0+(4501394351/10000000000 : ℝ)*X 2 1+(1062110761/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1083_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86507438985114459323448839/14281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1218666083/100000000000000 : ℝ)*(base19) + (1133337621/100000000000000 : ℝ)*(base23) + (1207683/3125000000000 : ℝ)*(lower2) + (15968199/10000000000000 : ℝ)*(upper3) + (21806003/25000000000000 : ℝ)*(upper5) + (5834342162956307/100000000000000 : ℝ)*(major0) + (5834342162956307/100000000000000 : ℝ)*(major1) + (5834342162956307/100000000000000 : ℝ)*(major2) + (3867567935177773/50000000000000 : ℝ)*(sp0) + (3867583629067853/50000000000000 : ℝ)*(sp1) + (966895917933021/12500000000000 : ℝ)*(sp2) + (3933497506978489/100000000000000 : ℝ)*(sp3) + (32606446243/100000000000000 : ℝ)*(sp4) + (18140218543/100000000000000 : ℝ)*(sp7) + (491689455899629/12500000000000 : ℝ)*(f.failure) + (7735168476801789/100000000000000 : ℝ)*(f.sum) + (13367845836197/3427500000000000000000000000 : ℝ)*base66 + (644203225105863/28562500000000000000000000000000 : ℝ)*base67 + (62640321236081637/28562500000000000000000000000000 : ℝ)*base70 + (53527810614394137/28562500000000000000000000000000 : ℝ)*base72 + (6919639024511/6855000000000000000000000000 : ℝ)*base73 + (119992505961519137/28562500000000000000000000000000 : ℝ)*base76 + (156972649771480863/28562500000000000000000000000000 : ℝ)*base77 + (109847971719456637/28562500000000000000000000000000 : ℝ)*base80 + (11685552622307/3427500000000000000000000000 : ℝ)*base82 + (1725659/625000000000000000000 : ℝ)*base90 + (1725659/625000000000000000000 : ℝ)*base92 + (1725659/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10989839073227428232722929/3570312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (114500339/20000000000000 : ℝ)*(base19) + (623380949/100000000000000 : ℝ)*(base23) + (2019917/1000000000000 : ℝ)*(lower1) + (6171833/10000000000000 : ℝ)*(upper3) + (23184551/100000000000000 : ℝ)*(lower4) + (31594339/50000000000000 : ℝ)*(upper5) + (2931859722653477/50000000000000 : ℝ)*(major0) + (2931859722653477/50000000000000 : ℝ)*(major1) + (2931859722653477/50000000000000 : ℝ)*(major2) + (589471527/50000000000000 : ℝ)*(sp2) + (3887058483085677/50000000000000 : ℝ)*(sp4) + (7774116393669659/100000000000000 : ℝ)*(sp5) + (7774115163847353/100000000000000 : ℝ)*(sp6) + (1976660910919319/50000000000000 : ℝ)*(sp7) + (1976660910919319/50000000000000 : ℝ)*(f.failure) + (3887058483085677/50000000000000 : ℝ)*(f.sum) + (6017538227179/3427500000000000000000000000 : ℝ)*base66 + (145575354999298607/14281250000000000000000000000000 : ℝ)*base68 + (125811638091486107/14281250000000000000000000000000 : ℝ)*base70 + (773264653253888893/14281250000000000000000000000000 : ℝ)*base71 + (7275339237773/6855000000000000000000000000 : ℝ)*base74 + (1214600044711329857/14281250000000000000000000000000 : ℝ)*base76 + (131011734496236107/14281250000000000000000000000000 : ℝ)*base78 + (186274836392704857/14281250000000000000000000000000 : ℝ)*base80 + (13251450063353/6855000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base87 + (10406351/2500000000000000000000 : ℝ)*base89 + (10406351/2500000000000000000000 : ℝ)*base91 + (10406351/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1083_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1083_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1083_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1083_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1083_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1083_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8275/2048 : ℝ) ≤ p) (hpb : p ≤ (2069/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74161929/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1083_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1692_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:39:29.903229+00:00
-- url     : https://prove2.me/submissions/7c695024-7c20-4249-87d3-29d4fd6edcb9

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
theorem support_rectangle_w1692_s3_0 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1479860793/10000000000 : ℝ)*x 0 + (5481853421/10000000000 : ℝ)*x 1 + (5135644281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1479860793/10000000000 : ℝ)^5159 ≤ (922003635097/10000000000000 : ℝ)^4135 := by
    have hnat : (1479860793 : ℕ)^5159*10000000000000^4135 ≤ 922003635097^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479860793 10000000000 922003635097 10000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5481853421/10000000000 : ℝ)^5159 ≤ (47236190105749/100000000000000 : ℝ)^4135 := by
    have hnat : (5481853421 : ℕ)^5159*100000000000000^4135 ≤ 47236190105749^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481853421 10000000000 47236190105749 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135644281/10000000000 : ℝ)^5159 ≤ (8708754706071/20000000000000 : ℝ)^4135 := by
    have hnat : (5135644281 : ℕ)^5159*20000000000000^4135 ≤ 8708754706071^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135644281 10000000000 8708754706071 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1479860793/10000000000 : ℝ), (5481853421/10000000000 : ℝ), (5135644281/10000000000 : ℝ)] ![(922003635097/10000000000000 : ℝ), (47236190105749/100000000000000 : ℝ), (8708754706071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1479860793/10000000000 : ℝ)|^5159 ≤ (922003635097/10000000000000 : ℝ)^4135
        have hw : |(-1479860793/10000000000 : ℝ)|=(1479860793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5481853421/10000000000 : ℝ)|^5159 ≤ (47236190105749/100000000000000 : ℝ)^4135
        have hw : |(5481853421/10000000000 : ℝ)|=(5481853421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135644281/10000000000 : ℝ)|^5159 ≤ (8708754706071/20000000000000 : ℝ)^4135
        have hw : |(5135644281/10000000000 : ℝ)|=(5135644281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s3_1 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349551323/10000000000 : ℝ)*x 0 + (-10372893/62500000 : ℝ)*x 1 + (2567822353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349551323/10000000000 : ℝ)^5159 ≤ (229090620421/500000000000 : ℝ)^4135 := by
    have hnat : (5349551323 : ℕ)^5159*500000000000^4135 ≤ 229090620421^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349551323 10000000000 229090620421 500000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10372893/62500000 : ℝ)^5159 ≤ (10638097875561/100000000000000 : ℝ)^4135 := by
    have hnat : (10372893 : ℕ)^5159*100000000000000^4135 ≤ 10638097875561^4135*62500000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10372893 62500000 10638097875561 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567822353/5000000000 : ℝ)^5159 ≤ (43543778026187/100000000000000 : ℝ)^4135 := by
    have hnat : (2567822353 : ℕ)^5159*100000000000000^4135 ≤ 43543778026187^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567822353 5000000000 43543778026187 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349551323/10000000000 : ℝ), (-10372893/62500000 : ℝ), (2567822353/5000000000 : ℝ)] ![(229090620421/500000000000 : ℝ), (10638097875561/100000000000000 : ℝ), (43543778026187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349551323/10000000000 : ℝ)|^5159 ≤ (229090620421/500000000000 : ℝ)^4135
        have hw : |(5349551323/10000000000 : ℝ)|=(5349551323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10372893/62500000 : ℝ)|^5159 ≤ (10638097875561/100000000000000 : ℝ)^4135
        have hw : |(-10372893/62500000 : ℝ)|=(10372893/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567822353/5000000000 : ℝ)|^5159 ≤ (43543778026187/100000000000000 : ℝ)^4135
        have hw : |(2567822353/5000000000 : ℝ)|=(2567822353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s3_2 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267477553/500000000 : ℝ)*x 0 + (256782257/500000000 : ℝ)*x 1 + (-1659662657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267477553/500000000 : ℝ)^5159 ≤ (9163624254763/20000000000000 : ℝ)^4135 := by
    have hnat : (267477553 : ℕ)^5159*20000000000000^4135 ≤ 9163624254763^4135*500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267477553 500000000 9163624254763 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256782257/500000000 : ℝ)^5159 ≤ (1741751304689/4000000000000 : ℝ)^4135 := by
    have hnat : (256782257 : ℕ)^5159*4000000000000^4135 ≤ 1741751304689^4135*500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256782257 500000000 1741751304689 4000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1659662657/10000000000 : ℝ)^5159 ≤ (10638096092201/100000000000000 : ℝ)^4135 := by
    have hnat : (1659662657 : ℕ)^5159*100000000000000^4135 ≤ 10638096092201^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659662657 10000000000 10638096092201 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267477553/500000000 : ℝ), (256782257/500000000 : ℝ), (-1659662657/10000000000 : ℝ)] ![(9163624254763/20000000000000 : ℝ), (1741751304689/4000000000000 : ℝ), (10638096092201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267477553/500000000 : ℝ)|^5159 ≤ (9163624254763/20000000000000 : ℝ)^4135
        have hw : |(267477553/500000000 : ℝ)|=(267477553/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256782257/500000000 : ℝ)|^5159 ≤ (1741751304689/4000000000000 : ℝ)^4135
        have hw : |(256782257/500000000 : ℝ)|=(256782257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1659662657/10000000000 : ℝ)|^5159 ≤ (10638096092201/100000000000000 : ℝ)^4135
        have hw : |(-1659662657/10000000000 : ℝ)|=(1659662657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s3_3 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4128507723/10000000000 : ℝ)*x 0 + (3665819133/10000000000 : ℝ)*x 1 + (36159717/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128507723/10000000000 : ℝ)^5159 ≤ (16581251637813/50000000000000 : ℝ)^4135 := by
    have hnat : (4128507723 : ℕ)^5159*50000000000000^4135 ≤ 16581251637813^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128507723 10000000000 16581251637813 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3665819133/10000000000 : ℝ)^5159 ≤ (28591796355637/100000000000000 : ℝ)^4135 := by
    have hnat : (3665819133 : ℕ)^5159*100000000000000^4135 ≤ 28591796355637^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665819133 10000000000 28591796355637 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36159717/78125000 : ℝ)^5159 ≤ (7649140072627/20000000000000 : ℝ)^4135 := by
    have hnat : (36159717 : ℕ)^5159*20000000000000^4135 ≤ 7649140072627^4135*78125000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36159717 78125000 7649140072627 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128507723/10000000000 : ℝ), (3665819133/10000000000 : ℝ), (36159717/78125000 : ℝ)] ![(16581251637813/50000000000000 : ℝ), (28591796355637/100000000000000 : ℝ), (7649140072627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128507723/10000000000 : ℝ)|^5159 ≤ (16581251637813/50000000000000 : ℝ)^4135
        have hw : |(4128507723/10000000000 : ℝ)|=(4128507723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3665819133/10000000000 : ℝ)|^5159 ≤ (28591796355637/100000000000000 : ℝ)^4135
        have hw : |(3665819133/10000000000 : ℝ)|=(3665819133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36159717/78125000 : ℝ)|^5159 ≤ (7649140072627/20000000000000 : ℝ)^4135
        have hw : |(36159717/78125000 : ℝ)|=(36159717/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s3_4 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1480021353/10000000000 : ℝ)*x 0 + (1284854813/2500000000 : ℝ)*x 1 + (684752773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1480021353/10000000000 : ℝ)^5159 ≤ (4610642219153/50000000000000 : ℝ)^4135 := by
    have hnat : (1480021353 : ℕ)^5159*50000000000000^4135 ≤ 4610642219153^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480021353 10000000000 4610642219153 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284854813/2500000000 : ℝ)^5159 ≤ (43583710423807/100000000000000 : ℝ)^4135 := by
    have hnat : (1284854813 : ℕ)^5159*100000000000000^4135 ≤ 43583710423807^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284854813 2500000000 43583710423807 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684752773/1250000000 : ℝ)^5159 ≤ (2949687820213/6250000000000 : ℝ)^4135 := by
    have hnat : (684752773 : ℕ)^5159*6250000000000^4135 ≤ 2949687820213^4135*1250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684752773 1250000000 2949687820213 6250000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1480021353/10000000000 : ℝ), (1284854813/2500000000 : ℝ), (684752773/1250000000 : ℝ)] ![(4610642219153/50000000000000 : ℝ), (43583710423807/100000000000000 : ℝ), (2949687820213/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1480021353/10000000000 : ℝ)|^5159 ≤ (4610642219153/50000000000000 : ℝ)^4135
        have hw : |(-1480021353/10000000000 : ℝ)|=(1480021353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284854813/2500000000 : ℝ)|^5159 ≤ (43583710423807/100000000000000 : ℝ)^4135
        have hw : |(1284854813/2500000000 : ℝ)|=(1284854813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684752773/1250000000 : ℝ)|^5159 ≤ (2949687820213/6250000000000 : ℝ)^4135
        have hw : |(684752773/1250000000 : ℝ)|=(684752773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s3_5 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256976541/10000000000 : ℝ)*x 0 + (-1317284639/10000000000 : ℝ)*x 1 + (2739011181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256976541/10000000000 : ℝ)^5159 ≤ (44831010791921/100000000000000 : ℝ)^4135 := by
    have hnat : (5256976541 : ℕ)^5159*100000000000000^4135 ≤ 44831010791921^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256976541 10000000000 44831010791921 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1317284639/10000000000 : ℝ)^5159 ≤ (3986991078761/50000000000000 : ℝ)^4135 := by
    have hnat : (1317284639 : ℕ)^5159*50000000000000^4135 ≤ 3986991078761^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317284639 10000000000 3986991078761 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739011181/5000000000 : ℝ)^5159 ≤ (9439001407341/20000000000000 : ℝ)^4135 := by
    have hnat : (2739011181 : ℕ)^5159*20000000000000^4135 ≤ 9439001407341^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739011181 5000000000 9439001407341 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256976541/10000000000 : ℝ), (-1317284639/10000000000 : ℝ), (2739011181/5000000000 : ℝ)] ![(44831010791921/100000000000000 : ℝ), (3986991078761/50000000000000 : ℝ), (9439001407341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256976541/10000000000 : ℝ)|^5159 ≤ (44831010791921/100000000000000 : ℝ)^4135
        have hw : |(5256976541/10000000000 : ℝ)|=(5256976541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1317284639/10000000000 : ℝ)|^5159 ≤ (3986991078761/50000000000000 : ℝ)^4135
        have hw : |(-1317284639/10000000000 : ℝ)|=(1317284639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739011181/5000000000 : ℝ)|^5159 ≤ (9439001407341/20000000000000 : ℝ)^4135
        have hw : |(2739011181/5000000000 : ℝ)|=(2739011181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s3_6 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525697633/1000000000 : ℝ)*x 0 + (2739011297/5000000000 : ℝ)*x 1 + (-658642303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525697633/1000000000 : ℝ)^5159 ≤ (2801938034183/6250000000000 : ℝ)^4135 := by
    have hnat : (525697633 : ℕ)^5159*6250000000000^4135 ≤ 2801938034183^4135*1000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525697633 1000000000 2801938034183 6250000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739011297/5000000000 : ℝ)^5159 ≤ (47195009530439/100000000000000 : ℝ)^4135 := by
    have hnat : (2739011297 : ℕ)^5159*100000000000000^4135 ≤ 47195009530439^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739011297 5000000000 47195009530439 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658642303/5000000000 : ℝ)^5159 ≤ (7973981908293/100000000000000 : ℝ)^4135 := by
    have hnat : (658642303 : ℕ)^5159*100000000000000^4135 ≤ 7973981908293^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658642303 5000000000 7973981908293 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525697633/1000000000 : ℝ), (2739011297/5000000000 : ℝ), (-658642303/5000000000 : ℝ)] ![(2801938034183/6250000000000 : ℝ), (47195009530439/100000000000000 : ℝ), (7973981908293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525697633/1000000000 : ℝ)|^5159 ≤ (2801938034183/6250000000000 : ℝ)^4135
        have hw : |(525697633/1000000000 : ℝ)|=(525697633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739011297/5000000000 : ℝ)|^5159 ≤ (47195009530439/100000000000000 : ℝ)^4135
        have hw : |(2739011297/5000000000 : ℝ)|=(2739011297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-658642303/5000000000 : ℝ)|^5159 ≤ (7973981908293/100000000000000 : ℝ)^4135
        have hw : |(-658642303/5000000000 : ℝ)|=(658642303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s3_7 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4128955117/10000000000 : ℝ)*x 0 + (4617949281/10000000000 : ℝ)*x 1 + (147058789/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128955117/10000000000 : ℝ)^5159 ≤ (8291746753339/25000000000000 : ℝ)^4135 := by
    have hnat : (4128955117 : ℕ)^5159*25000000000000^4135 ≤ 8291746753339^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128955117 10000000000 8291746753339 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4617949281/10000000000 : ℝ)^5159 ≤ (38137537750343/100000000000000 : ℝ)^4135 := by
    have hnat : (4617949281 : ℕ)^5159*100000000000000^4135 ≤ 38137537750343^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4617949281 10000000000 38137537750343 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147058789/400000000 : ℝ)^5159 ≤ (28695475227951/100000000000000 : ℝ)^4135 := by
    have hnat : (147058789 : ℕ)^5159*100000000000000^4135 ≤ 28695475227951^4135*400000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147058789 400000000 28695475227951 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128955117/10000000000 : ℝ), (4617949281/10000000000 : ℝ), (147058789/400000000 : ℝ)] ![(8291746753339/25000000000000 : ℝ), (38137537750343/100000000000000 : ℝ), (28695475227951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128955117/10000000000 : ℝ)|^5159 ≤ (8291746753339/25000000000000 : ℝ)^4135
        have hw : |(4128955117/10000000000 : ℝ)|=(4128955117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4617949281/10000000000 : ℝ)|^5159 ≤ (38137537750343/100000000000000 : ℝ)^4135
        have hw : |(4617949281/10000000000 : ℝ)|=(4617949281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147058789/400000000 : ℝ)|^5159 ≤ (28695475227951/100000000000000 : ℝ)^4135
        have hw : |(147058789/400000000 : ℝ)|=(147058789/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1692_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8621/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (197/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17221/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8621/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1229/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8621/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1229/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8621/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1229/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8621/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1229/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8621/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1229/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8621/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1229/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1229/12500 : ℝ) ^ (5151/1024 : ℝ) ≤ (856471973438689/100000000000000000000 : ℝ) := by
    have hpowers : (1229/12500 : ℝ)^5151 ≤ (856471973438689/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1229 : ℕ)^5151*100000000000000000000^1024 ≤ 856471973438689^1024*12500^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1229 12500 856471973438689 100000000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1229/12500 : ℝ)) (X := (856471973438689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8621/50000 : ℝ) ^ (5151/1024 : ℝ) ≤ (7224321947024077/50000000000000000000 : ℝ) := by
    have hpowers : (8621/50000 : ℝ)^5151 ≤ (7224321947024077/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8621 : ℕ)^5151*50000000000000000000^1024 ≤ 7224321947024077^1024*50000^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8621 50000 7224321947024077 50000000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8621/50000 : ℝ)) (X := (7224321947024077/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000856471973438689/50000000000000000000 : ℝ) ≤ (1250004256558351/1250000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (50000856471973438689/50000000000000000000 : ℝ)^1024 ≤ (1250004256558351/1250000000000000 : ℝ)^5151 := by
      have hnat : (50000856471973438689 : ℕ)^1024*1250000000000000^5151 ≤ 1250004256558351^5151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000856471973438689 50000000000000000000 1250004256558351 1250000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250004256558351/1250000000000000 : ℝ)) (X := (50000856471973438689/50000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015305115867486843/100000000000000000000 : ℝ) ≤ (2500076060366041/2500000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (100015305115867486843/100000000000000000000 : ℝ)^1024 ≤ (2500076060366041/2500000000000000 : ℝ)^5151 := by
      have hnat : (100015305115867486843 : ℕ)^1024*2500000000000000^5151 ≤ 2500076060366041^5151*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015305115867486843 100000000000000000000 2500076060366041 2500000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500076060366041/2500000000000000 : ℝ)) (X := (100015305115867486843/100000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25007224321947024077/25000000000000000000 : ℝ) ≤ (125007180380769/125000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (25007224321947024077/25000000000000000000 : ℝ)^1024 ≤ (125007180380769/125000000000000 : ℝ)^5151 := by
      have hnat : (25007224321947024077 : ℕ)^1024*125000000000000^5151 ≤ 125007180380769^5151*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007224321947024077 25000000000000000000 125007180380769 125000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125007180380769/125000000000000 : ℝ)) (X := (25007224321947024077/25000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(856471973438689/100000000000000000000 : ℝ) ≤ ((4630933708270939931/4631250000000000000 : ℝ)+2*(67547249339/185250000000000 : ℝ)*(1229/12500 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (4630933708270939931/4631250000000000000 : ℝ)+2*(67547249339/185250000000000 : ℝ)*(1229/12500 : ℝ)=(1250004256558351/1250000000000000 : ℝ) by norm_num, show 1+2*(856471973438689/100000000000000000000 : ℝ)=(50000856471973438689/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7224321947024077/50000000000000000000 : ℝ)+(856471973438689/100000000000000000000 : ℝ) ≤ ((4630933708270939931/4631250000000000000 : ℝ)+(67547249339/185250000000000 : ℝ)*((8621/50000 : ℝ)+(1229/12500 : ℝ)))^(5151/1024 : ℝ) := by
    rw [show (4630933708270939931/4631250000000000000 : ℝ)+(67547249339/185250000000000 : ℝ)*((8621/50000 : ℝ)+(1229/12500 : ℝ))=(2500076060366041/2500000000000000 : ℝ) by norm_num, show 1+(7224321947024077/50000000000000000000 : ℝ)+(856471973438689/100000000000000000000 : ℝ)=(100015305115867486843/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7224321947024077/50000000000000000000 : ℝ) ≤ ((4630933708270939931/4631250000000000000 : ℝ)+2*(67547249339/185250000000000 : ℝ)*(8621/50000 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (4630933708270939931/4631250000000000000 : ℝ)+2*(67547249339/185250000000000 : ℝ)*(8621/50000 : ℝ)=(125007180380769/125000000000000 : ℝ) by norm_num, show 1+2*(7224321947024077/50000000000000000000 : ℝ)=(25007224321947024077/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4630933708270939931/4631250000000000000 : ℝ)*(X 1 0+X 2 0)+(67547249339/185250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (1229/12500 : ℝ)) (hi := (8621/50000 : ℝ)) (c := (4630933708270939931/4631250000000000000 : ℝ)) (alpha := (67547249339/185250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4630933708270939931/4631250000000000000 : ℝ)*(X 0 1+X 2 1)+(67547249339/185250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (1229/12500 : ℝ)) (hi := (8621/50000 : ℝ)) (c := (4630933708270939931/4631250000000000000 : ℝ)) (alpha := (67547249339/185250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4630933708270939931/4631250000000000000 : ℝ)*(X 0 2+X 1 2)+(67547249339/185250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (1229/12500 : ℝ)) (hi := (8621/50000 : ℝ)) (c := (4630933708270939931/4631250000000000000 : ℝ)) (alpha := (67547249339/185250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1479860793/10000000000 : ℝ)*X 0 0+(5481853421/10000000000 : ℝ)*X 0 1+(5135644281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349551323/10000000000 : ℝ)*X 1 0+(-10372893/62500000 : ℝ)*X 1 1+(2567822353/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267477553/500000000 : ℝ)*X 2 0+(256782257/500000000 : ℝ)*X 2 1+(-1659662657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4128507723/10000000000 : ℝ)*X 0 0+(3665819133/10000000000 : ℝ)*X 0 1+(36159717/78125000 : ℝ)*X 0 2+(4128507723/10000000000 : ℝ)*X 1 0+(3665819133/10000000000 : ℝ)*X 1 1+(36159717/78125000 : ℝ)*X 1 2+(4128507723/10000000000 : ℝ)*X 2 0+(3665819133/10000000000 : ℝ)*X 2 1+(36159717/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1480021353/10000000000 : ℝ)*X 0 0+(1284854813/2500000000 : ℝ)*X 0 1+(684752773/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256976541/10000000000 : ℝ)*X 1 0+(-1317284639/10000000000 : ℝ)*X 1 1+(2739011181/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525697633/1000000000 : ℝ)*X 2 0+(2739011297/5000000000 : ℝ)*X 2 1+(-658642303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4128955117/10000000000 : ℝ)*X 0 0+(4617949281/10000000000 : ℝ)*X 0 1+(147058789/400000000 : ℝ)*X 0 2+(4128955117/10000000000 : ℝ)*X 1 0+(4617949281/10000000000 : ℝ)*X 1 1+(147058789/400000000 : ℝ)*X 1 2+(4128955117/10000000000 : ℝ)*X 2 0+(4617949281/10000000000 : ℝ)*X 2 1+(147058789/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (255648497371892910715797539/19296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1499149147/100000000000000 : ℝ)*(base19) + (613910199/50000000000000 : ℝ)*(base23) + (60274303/25000000000000 : ℝ)*(upper3) + (13836439/20000000000000 : ℝ)*(upper4) + (10837/4000000000 : ℝ)*(upper5) + (490912216478623/25000000000000 : ℝ)*(major0) + (490912216478623/25000000000000 : ℝ)*(major1) + (490912216478623/25000000000000 : ℝ)*(major2) + (1444221947947839/50000000000000 : ℝ)*(sp0) + (115538409586273/4000000000000 : ℝ)*(sp1) + (1444230255492787/50000000000000 : ℝ)*(sp2) + (519415518123779/50000000000000 : ℝ)*(sp3) + (8921455147/50000000000000 : ℝ)*(sp4) + (4515169407/100000000000000 : ℝ)*(sp7) + (207767110283393/20000000000000 : ℝ)*(f.failure) + (722115434701493/25000000000000 : ℝ)*(f.sum) + (20327757736651/18525000000000000000000000000 : ℝ)*base65 + (1046683744955073737/115781250000000000000000000000000 : ℝ)*base68 + (244888584047261237/115781250000000000000000000000000 : ℝ)*base70 + (257838002605229987/115781250000000000000000000000000 : ℝ)*base72 + (51458135646449/18525000000000000000000000000 : ℝ)*base74 + (108352252402886237/115781250000000000000000000000000 : ℝ)*base76 + (696843332771636237/115781250000000000000000000000000 : ℝ)*base78 + (204631703235386237/115781250000000000000000000000000 : ℝ)*base80 + (13850058610049/18525000000000000000000000000 : ℝ)*base82 + (5966319/1000000000000000000000 : ℝ)*base90 + (5966319/1000000000000000000000 : ℝ)*base92 + (5966319/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104726145624854347240711157/19296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162409763/20000000000000 : ℝ)*(base19) + (730951241/100000000000000 : ℝ)*(base23) + (142227751/50000000000000 : ℝ)*(lower1) + (1090503/12500000000000 : ℝ)*(upper2) + (135319927/100000000000000 : ℝ)*(upper3) + (14581957/20000000000000 : ℝ)*(upper5) + (501932130922553/25000000000000 : ℝ)*(major0) + (501932130922553/25000000000000 : ℝ)*(major1) + (501932130922553/25000000000000 : ℝ)*(major2) + (73979567/6250000000000 : ℝ)*(sp2) + (738325427555753/25000000000000 : ℝ)*(sp4) + (2953300898174197/100000000000000 : ℝ)*(sp5) + (2953299795598699/100000000000000 : ℝ)*(sp6) + (531077578126973/50000000000000 : ℝ)*(sp7) + (531077578126973/50000000000000 : ℝ)*(f.failure) + (738325427555753/25000000000000 : ℝ)*(f.sum) + (8550383936207/9262500000000000000000000000 : ℝ)*base66 + (23572032530026343/115781250000000000000000000000000 : ℝ)*base67 + (75564389228776343/115781250000000000000000000000000 : ℝ)*base69 + (261124151387004907/115781250000000000000000000000000 : ℝ)*base72 + (35508810229339/18525000000000000000000000000 : ℝ)*base74 + (444432440237213843/115781250000000000000000000000000 : ℝ)*base75 + (610437916732838843/115781250000000000000000000000000 : ℝ)*base77 + (133710805304661157/115781250000000000000000000000000 : ℝ)*base80 + (2713178192249/289453125000000000000000000 : ℝ)*base81 + (334541/2500000000000000000000 : ℝ)*base89 + (334541/2500000000000000000000 : ℝ)*base91 + (334541/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1692_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8621/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (197/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17221/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1692_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1692_s4_0 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1479872937/10000000000 : ℝ)*x 0 + (1370451731/2500000000 : ℝ)*x 1 + (5135682611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1479872937/10000000000 : ℝ)^5159 ≤ (2305032687307/25000000000000 : ℝ)^4135 := by
    have hnat : (1479872937 : ℕ)^5159*25000000000000^4135 ≤ 2305032687307^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479872937 10000000000 2305032687307 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370451731/2500000000 : ℝ)^5159 ≤ (23617845115077/50000000000000 : ℝ)^4135 := by
    have hnat : (1370451731 : ℕ)^5159*50000000000000^4135 ≤ 23617845115077^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370451731 2500000000 23617845115077 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135682611/10000000000 : ℝ)^5159 ≤ (21772089500941/50000000000000 : ℝ)^4135 := by
    have hnat : (5135682611 : ℕ)^5159*50000000000000^4135 ≤ 21772089500941^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135682611 10000000000 21772089500941 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1479872937/10000000000 : ℝ), (1370451731/2500000000 : ℝ), (5135682611/10000000000 : ℝ)] ![(2305032687307/25000000000000 : ℝ), (23617845115077/50000000000000 : ℝ), (21772089500941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1479872937/10000000000 : ℝ)|^5159 ≤ (2305032687307/25000000000000 : ℝ)^4135
        have hw : |(-1479872937/10000000000 : ℝ)|=(1479872937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1370451731/2500000000 : ℝ)|^5159 ≤ (23617845115077/50000000000000 : ℝ)^4135
        have hw : |(1370451731/2500000000 : ℝ)|=(1370451731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135682611/10000000000 : ℝ)|^5159 ≤ (21772089500941/50000000000000 : ℝ)^4135
        have hw : |(5135682611/10000000000 : ℝ)|=(5135682611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s4_1 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337384899/2500000000 : ℝ)*x 0 + (-414907367/2500000000 : ℝ)*x 1 + (5135681811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337384899/2500000000 : ℝ)^5159 ≤ (9163599754203/20000000000000 : ℝ)^4135 := by
    have hnat : (1337384899 : ℕ)^5159*20000000000000^4135 ≤ 9163599754203^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337384899 2500000000 9163599754203 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414907367/2500000000 : ℝ)^5159 ≤ (2127566135229/20000000000000 : ℝ)^4135 := by
    have hnat : (414907367 : ℕ)^5159*20000000000000^4135 ≤ 2127566135229^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414907367 2500000000 2127566135229 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135681811/10000000000 : ℝ)^5159 ≤ (10886042634781/25000000000000 : ℝ)^4135 := by
    have hnat : (5135681811 : ℕ)^5159*25000000000000^4135 ≤ 10886042634781^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135681811 10000000000 10886042634781 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337384899/2500000000 : ℝ), (-414907367/2500000000 : ℝ), (5135681811/10000000000 : ℝ)] ![(9163599754203/20000000000000 : ℝ), (2127566135229/20000000000000 : ℝ), (10886042634781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337384899/2500000000 : ℝ)|^5159 ≤ (9163599754203/20000000000000 : ℝ)^4135
        have hw : |(1337384899/2500000000 : ℝ)|=(1337384899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414907367/2500000000 : ℝ)|^5159 ≤ (2127566135229/20000000000000 : ℝ)^4135
        have hw : |(-414907367/2500000000 : ℝ)|=(414907367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135681811/10000000000 : ℝ)|^5159 ≤ (10886042634781/25000000000000 : ℝ)^4135
        have hw : |(5135681811/10000000000 : ℝ)|=(5135681811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s4_2 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349538729/10000000000 : ℝ)*x 0 + (1283920577/2500000000 : ℝ)*x 1 + (-1659629969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349538729/10000000000 : ℝ)^5159 ≤ (45817989506369/100000000000000 : ℝ)^4135 := by
    have hnat : (5349538729 : ℕ)^5159*100000000000000^4135 ≤ 45817989506369^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349538729 10000000000 45817989506369 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283920577/2500000000 : ℝ)^5159 ≤ (10886043949153/25000000000000 : ℝ)^4135 := by
    have hnat : (1283920577 : ℕ)^5159*25000000000000^4135 ≤ 10886043949153^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283920577 2500000000 10886043949153 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1659629969/10000000000 : ℝ)^5159 ≤ (10637834682687/100000000000000 : ℝ)^4135 := by
    have hnat : (1659629969 : ℕ)^5159*100000000000000^4135 ≤ 10637834682687^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659629969 10000000000 10637834682687 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349538729/10000000000 : ℝ), (1283920577/2500000000 : ℝ), (-1659629969/10000000000 : ℝ)] ![(45817989506369/100000000000000 : ℝ), (10886043949153/25000000000000 : ℝ), (10637834682687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349538729/10000000000 : ℝ)|^5159 ≤ (45817989506369/100000000000000 : ℝ)^4135
        have hw : |(5349538729/10000000000 : ℝ)|=(5349538729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283920577/2500000000 : ℝ)|^5159 ≤ (10886043949153/25000000000000 : ℝ)^4135
        have hw : |(1283920577/2500000000 : ℝ)|=(1283920577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1659629969/10000000000 : ℝ)|^5159 ≤ (10637834682687/100000000000000 : ℝ)^4135
        have hw : |(-1659629969/10000000000 : ℝ)|=(1659629969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s4_3 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4128516577/10000000000 : ℝ)*x 0 + (3665933811/10000000000 : ℝ)*x 1 + (4628326923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128516577/10000000000 : ℝ)^5159 ≤ (33162592008357/100000000000000 : ℝ)^4135 := by
    have hnat : (4128516577 : ℕ)^5159*100000000000000^4135 ≤ 33162592008357^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128516577 10000000000 33162592008357 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3665933811/10000000000 : ℝ)^5159 ≤ (28592912299157/100000000000000 : ℝ)^4135 := by
    have hnat : (3665933811 : ℕ)^5159*100000000000000^4135 ≤ 28592912299157^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665933811 10000000000 28592912299157 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4628326923/10000000000 : ℝ)^5159 ≤ (7648899134159/20000000000000 : ℝ)^4135 := by
    have hnat : (4628326923 : ℕ)^5159*20000000000000^4135 ≤ 7648899134159^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4628326923 10000000000 7648899134159 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128516577/10000000000 : ℝ), (3665933811/10000000000 : ℝ), (4628326923/10000000000 : ℝ)] ![(33162592008357/100000000000000 : ℝ), (28592912299157/100000000000000 : ℝ), (7648899134159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128516577/10000000000 : ℝ)|^5159 ≤ (33162592008357/100000000000000 : ℝ)^4135
        have hw : |(4128516577/10000000000 : ℝ)|=(4128516577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3665933811/10000000000 : ℝ)|^5159 ≤ (28592912299157/100000000000000 : ℝ)^4135
        have hw : |(3665933811/10000000000 : ℝ)|=(3665933811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4628326923/10000000000 : ℝ)|^5159 ≤ (7648899134159/20000000000000 : ℝ)^4135
        have hw : |(4628326923/10000000000 : ℝ)|=(4628326923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s4_4 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1480033367/10000000000 : ℝ)*x 0 + (2569727447/5000000000 : ℝ)*x 1 + (5477978413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1480033367/10000000000 : ℝ)^5159 ≤ (9221377828551/100000000000000 : ℝ)^4135 := by
    have hnat : (1480033367 : ℕ)^5159*100000000000000^4135 ≤ 9221377828551^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480033367 10000000000 9221377828551 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569727447/5000000000 : ℝ)^5159 ≤ (43584087529081/100000000000000 : ℝ)^4135 := by
    have hnat : (2569727447 : ℕ)^5159*100000000000000^4135 ≤ 43584087529081^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569727447 5000000000 43584087529081 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477978413/10000000000 : ℝ)^5159 ≤ (11798633658919/25000000000000 : ℝ)^4135 := by
    have hnat : (5477978413 : ℕ)^5159*25000000000000^4135 ≤ 11798633658919^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477978413 10000000000 11798633658919 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1480033367/10000000000 : ℝ), (2569727447/5000000000 : ℝ), (5477978413/10000000000 : ℝ)] ![(9221377828551/100000000000000 : ℝ), (43584087529081/100000000000000 : ℝ), (11798633658919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1480033367/10000000000 : ℝ)|^5159 ≤ (9221377828551/100000000000000 : ℝ)^4135
        have hw : |(-1480033367/10000000000 : ℝ)|=(1480033367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569727447/5000000000 : ℝ)|^5159 ≤ (43584087529081/100000000000000 : ℝ)^4135
        have hw : |(2569727447/5000000000 : ℝ)|=(2569727447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477978413/10000000000 : ℝ)|^5159 ≤ (11798633658919/25000000000000 : ℝ)^4135
        have hw : |(5477978413/10000000000 : ℝ)|=(5477978413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s4_5 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628493297/5000000000 : ℝ)*x 0 + (-1317332891/10000000000 : ℝ)*x 1 + (1369494627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628493297/5000000000 : ℝ)^5159 ≤ (2241555887681/5000000000000 : ℝ)^4135 := by
    have hnat : (2628493297 : ℕ)^5159*5000000000000^4135 ≤ 2241555887681^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628493297 5000000000 2241555887681 5000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1317332891/10000000000 : ℝ)^5159 ≤ (996793322267/12500000000000 : ℝ)^4135 := by
    have hnat : (1317332891 : ℕ)^5159*12500000000000^4135 ≤ 996793322267^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317332891 10000000000 996793322267 12500000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369494627/2500000000 : ℝ)^5159 ≤ (9438907131363/20000000000000 : ℝ)^4135 := by
    have hnat : (1369494627 : ℕ)^5159*20000000000000^4135 ≤ 9438907131363^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369494627 2500000000 9438907131363 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628493297/5000000000 : ℝ), (-1317332891/10000000000 : ℝ), (1369494627/2500000000 : ℝ)] ![(2241555887681/5000000000000 : ℝ), (996793322267/12500000000000 : ℝ), (9438907131363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628493297/5000000000 : ℝ)|^5159 ≤ (2241555887681/5000000000000 : ℝ)^4135
        have hw : |(2628493297/5000000000 : ℝ)|=(2628493297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1317332891/10000000000 : ℝ)|^5159 ≤ (996793322267/12500000000000 : ℝ)^4135
        have hw : |(-1317332891/10000000000 : ℝ)|=(1317332891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369494627/2500000000 : ℝ)|^5159 ≤ (9438907131363/20000000000000 : ℝ)^4135
        have hw : |(1369494627/2500000000 : ℝ)|=(1369494627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s4_6 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256986651/10000000000 : ℝ)*x 0 + (2738988913/5000000000 : ℝ)*x 1 + (-1317333781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256986651/10000000000 : ℝ)^5159 ≤ (44831118360087/100000000000000 : ℝ)^4135 := by
    have hnat : (5256986651 : ℕ)^5159*100000000000000^4135 ≤ 44831118360087^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256986651 10000000000 44831118360087 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738988913/5000000000 : ℝ)^5159 ≤ (4719452832611/10000000000000 : ℝ)^4135 := by
    have hnat : (2738988913 : ℕ)^5159*10000000000000^4135 ≤ 4719452832611^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738988913 5000000000 4719452832611 10000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317333781/10000000000 : ℝ)^5159 ≤ (1993588324961/25000000000000 : ℝ)^4135 := by
    have hnat : (1317333781 : ℕ)^5159*25000000000000^4135 ≤ 1993588324961^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317333781 10000000000 1993588324961 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256986651/10000000000 : ℝ), (2738988913/5000000000 : ℝ), (-1317333781/10000000000 : ℝ)] ![(44831118360087/100000000000000 : ℝ), (4719452832611/10000000000000 : ℝ), (1993588324961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256986651/10000000000 : ℝ)|^5159 ≤ (44831118360087/100000000000000 : ℝ)^4135
        have hw : |(5256986651/10000000000 : ℝ)|=(5256986651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738988913/5000000000 : ℝ)|^5159 ≤ (4719452832611/10000000000000 : ℝ)^4135
        have hw : |(2738988913/5000000000 : ℝ)|=(2738988913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1317333781/10000000000 : ℝ)|^5159 ≤ (1993588324961/25000000000000 : ℝ)^4135
        have hw : |(-1317333781/10000000000 : ℝ)|=(1317333781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s4_7 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2064481693/5000000000 : ℝ)*x 0 + (4617837793/10000000000 : ℝ)*x 1 + (3676579177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064481693/5000000000 : ℝ)^5159 ≤ (1326682795423/4000000000000 : ℝ)^4135 := by
    have hnat : (2064481693 : ℕ)^5159*4000000000000^4135 ≤ 1326682795423^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064481693 5000000000 1326682795423 4000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4617837793/10000000000 : ℝ)^5159 ≤ (38136389014077/100000000000000 : ℝ)^4135 := by
    have hnat : (4617837793 : ℕ)^5159*100000000000000^4135 ≤ 38136389014077^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4617837793 10000000000 38136389014077 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3676579177/10000000000 : ℝ)^5159 ≤ (7174135270503/25000000000000 : ℝ)^4135 := by
    have hnat : (3676579177 : ℕ)^5159*25000000000000^4135 ≤ 7174135270503^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3676579177 10000000000 7174135270503 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2064481693/5000000000 : ℝ), (4617837793/10000000000 : ℝ), (3676579177/10000000000 : ℝ)] ![(1326682795423/4000000000000 : ℝ), (38136389014077/100000000000000 : ℝ), (7174135270503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2064481693/5000000000 : ℝ)|^5159 ≤ (1326682795423/4000000000000 : ℝ)^4135
        have hw : |(2064481693/5000000000 : ℝ)|=(2064481693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4617837793/10000000000 : ℝ)|^5159 ≤ (38136389014077/100000000000000 : ℝ)^4135
        have hw : |(4617837793/10000000000 : ℝ)|=(4617837793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3676579177/10000000000 : ℝ)|^5159 ≤ (7174135270503/25000000000000 : ℝ)^4135
        have hw : |(3676579177/10000000000 : ℝ)|=(3676579177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1692_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17221/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (197/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (9851/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (861/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17221/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (197/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17221/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (197/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17221/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (197/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17221/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (197/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17221/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (197/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17221/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (197/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (197/2000 : ℝ) ^ (5151/1024 : ℝ) ≤ (432194276684863/50000000000000000000 : ℝ) := by
    have hpowers : (197/2000 : ℝ)^5151 ≤ (432194276684863/50000000000000000000 : ℝ)^1024 := by
      have hnat : (197 : ℕ)^5151*50000000000000000000^1024 ≤ 432194276684863^1024*2000^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        197 2000 432194276684863 50000000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (197/2000 : ℝ)) (X := (432194276684863/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17221/100000 : ℝ) ^ (5151/1024 : ℝ) ≤ (3590084767559941/25000000000000000000 : ℝ) := by
    have hpowers : (17221/100000 : ℝ)^5151 ≤ (3590084767559941/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17221 : ℕ)^5151*25000000000000000000^1024 ≤ 3590084767559941^1024*100000^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17221 100000 3590084767559941 25000000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17221/100000 : ℝ)) (X := (3590084767559941/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000432194276684863/25000000000000000000 : ℝ) ≤ (2500008591804977/2500000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (25000432194276684863/25000000000000000000 : ℝ)^1024 ≤ (2500008591804977/2500000000000000 : ℝ)^5151 := by
      have hnat : (25000432194276684863 : ℕ)^1024*2500000000000000^5151 ≤ 2500008591804977^5151*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000432194276684863 25000000000000000000 2500008591804977 2500000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500008591804977/2500000000000000 : ℝ)) (X := (25000432194276684863/25000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10001522472762360949/10000000000000000000 : ℝ) ≤ (125003783044633/125000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (10001522472762360949/10000000000000000000 : ℝ)^1024 ≤ (125003783044633/125000000000000 : ℝ)^5151 := by
      have hnat : (10001522472762360949 : ℕ)^1024*125000000000000^5151 ≤ 125003783044633^5151*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001522472762360949 10000000000000000000 125003783044633 125000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125003783044633/125000000000000 : ℝ)) (X := (10001522472762360949/10000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503590084767559941/12500000000000000000 : ℝ) ≤ (2500142729980343/2500000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (12503590084767559941/12500000000000000000 : ℝ)^1024 ≤ (2500142729980343/2500000000000000 : ℝ)^5151 := by
      have hnat : (12503590084767559941 : ℕ)^1024*2500000000000000^5151 ≤ 2500142729980343^5151*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503590084767559941 12500000000000000000 2500142729980343 2500000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500142729980343/2500000000000000 : ℝ)) (X := (12503590084767559941/12500000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(432194276684863/50000000000000000000 : ℝ) ≤ ((472467745363259753/472500000000000000 : ℝ)+2*(1719720197/4725000000000 : ℝ)*(197/2000 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (472467745363259753/472500000000000000 : ℝ)+2*(1719720197/4725000000000 : ℝ)*(197/2000 : ℝ)=(2500008591804977/2500000000000000 : ℝ) by norm_num, show 1+2*(432194276684863/50000000000000000000 : ℝ)=(25000432194276684863/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3590084767559941/25000000000000000000 : ℝ)+(432194276684863/50000000000000000000 : ℝ) ≤ ((472467745363259753/472500000000000000 : ℝ)+(1719720197/4725000000000 : ℝ)*((17221/100000 : ℝ)+(197/2000 : ℝ)))^(5151/1024 : ℝ) := by
    rw [show (472467745363259753/472500000000000000 : ℝ)+(1719720197/4725000000000 : ℝ)*((17221/100000 : ℝ)+(197/2000 : ℝ))=(125003783044633/125000000000000 : ℝ) by norm_num, show 1+(3590084767559941/25000000000000000000 : ℝ)+(432194276684863/50000000000000000000 : ℝ)=(10001522472762360949/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3590084767559941/25000000000000000000 : ℝ) ≤ ((472467745363259753/472500000000000000 : ℝ)+2*(1719720197/4725000000000 : ℝ)*(17221/100000 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (472467745363259753/472500000000000000 : ℝ)+2*(1719720197/4725000000000 : ℝ)*(17221/100000 : ℝ)=(2500142729980343/2500000000000000 : ℝ) by norm_num, show 1+2*(3590084767559941/25000000000000000000 : ℝ)=(12503590084767559941/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (472467745363259753/472500000000000000 : ℝ)*(X 1 0+X 2 0)+(1719720197/4725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (197/2000 : ℝ)) (hi := (17221/100000 : ℝ)) (c := (472467745363259753/472500000000000000 : ℝ)) (alpha := (1719720197/4725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (472467745363259753/472500000000000000 : ℝ)*(X 0 1+X 2 1)+(1719720197/4725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (197/2000 : ℝ)) (hi := (17221/100000 : ℝ)) (c := (472467745363259753/472500000000000000 : ℝ)) (alpha := (1719720197/4725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (472467745363259753/472500000000000000 : ℝ)*(X 0 2+X 1 2)+(1719720197/4725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (197/2000 : ℝ)) (hi := (17221/100000 : ℝ)) (c := (472467745363259753/472500000000000000 : ℝ)) (alpha := (1719720197/4725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1479872937/10000000000 : ℝ)*X 0 0+(1370451731/2500000000 : ℝ)*X 0 1+(5135682611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337384899/2500000000 : ℝ)*X 1 0+(-414907367/2500000000 : ℝ)*X 1 1+(5135681811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349538729/10000000000 : ℝ)*X 2 0+(1283920577/2500000000 : ℝ)*X 2 1+(-1659629969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4128516577/10000000000 : ℝ)*X 0 0+(3665933811/10000000000 : ℝ)*X 0 1+(4628326923/10000000000 : ℝ)*X 0 2+(4128516577/10000000000 : ℝ)*X 1 0+(3665933811/10000000000 : ℝ)*X 1 1+(4628326923/10000000000 : ℝ)*X 1 2+(4128516577/10000000000 : ℝ)*X 2 0+(3665933811/10000000000 : ℝ)*X 2 1+(4628326923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1480033367/10000000000 : ℝ)*X 0 0+(2569727447/5000000000 : ℝ)*X 0 1+(5477978413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628493297/5000000000 : ℝ)*X 1 0+(-1317332891/10000000000 : ℝ)*X 1 1+(1369494627/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256986651/10000000000 : ℝ)*X 2 0+(2738988913/5000000000 : ℝ)*X 2 1+(-1317333781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2064481693/5000000000 : ℝ)*X 0 0+(4617837793/10000000000 : ℝ)*X 0 1+(3676579177/10000000000 : ℝ)*X 0 2+(2064481693/5000000000 : ℝ)*X 1 0+(4617837793/10000000000 : ℝ)*X 1 1+(3676579177/10000000000 : ℝ)*X 1 2+(2064481693/5000000000 : ℝ)*X 2 0+(4617837793/10000000000 : ℝ)*X 2 1+(3676579177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1042222871737815958448873/109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (472590043/25000000000000 : ℝ)*(base19) + (1307431757/100000000000000 : ℝ)*(base23) + (456407451/100000000000000 : ℝ)*(upper3) + (12270001/20000000000000 : ℝ)*(upper4) + (8359003/100000000000000 : ℝ)*(upper5) + (245515238444627/12500000000000 : ℝ)*(major0) + (245515238444627/12500000000000 : ℝ)*(major1) + (245515238444627/12500000000000 : ℝ)*(major2) + (1444575456899401/50000000000000 : ℝ)*(sp0) + (722288950236779/25000000000000 : ℝ)*(sp1) + (2889156383875531/100000000000000 : ℝ)*(sp2) + (103907998146989/10000000000000 : ℝ)*(sp3) + (3388754243/50000000000000 : ℝ)*(sp4) + (5824707019/100000000000000 : ℝ)*(sp7) + (103908580617691/10000000000000 : ℝ)*(f.failure) + (361144711413411/12500000000000 : ℝ)*(f.sum) + (59172106787/236250000000000000000000000 : ℝ)*base65 + (59680991068815881/5906250000000000000000000000000 : ℝ)*base67 + (51867724075815881/5906250000000000000000000000000 : ℝ)*base69 + (25041291897597131/5906250000000000000000000000000 : ℝ)*base71 + (5220895745903/945000000000000000000000000 : ℝ)*base73 + (36524690278815881/5906250000000000000000000000000 : ℝ)*base75 + (8173426022378381/5906250000000000000000000000000 : ℝ)*base77 + (38506671286815881/5906250000000000000000000000000 : ℝ)*base79 + (3143523447889/472500000000000000000000000 : ℝ)*base81 + (2292747/500000000000000000000 : ℝ)*base89 + (2292747/500000000000000000000 : ℝ)*base91 + (2292747/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31499192582397260078418623/7875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132115889/12500000000000 : ℝ)*(base19) + (62158707/6250000000000 : ℝ)*(base23) + (66956543/50000000000000 : ℝ)*(lower1) + (1296409/10000000000000 : ℝ)*(upper2) + (28115829/20000000000000 : ℝ)*(upper3) + (46128477/50000000000000 : ℝ)*(upper5) + (2008202571843791/100000000000000 : ℝ)*(major0) + (2008202571843791/100000000000000 : ℝ)*(major1) + (2008202571843791/100000000000000 : ℝ)*(major2) + (6763590621/100000000000000 : ℝ)*(sp1) + (59079981337319/2000000000000 : ℝ)*(sp4) + (1476995623174109/50000000000000 : ℝ)*(sp5) + (2953998072326639/100000000000000 : ℝ)*(sp6) + (106240594349171/10000000000000 : ℝ)*(sp7) + (106240594349171/10000000000000 : ℝ)*(f.failure) + (59079981337319/2000000000000 : ℝ)*(f.sum) + (161984360071/472500000000000000000000000 : ℝ)*base66 + (110966070613443623/47250000000000000000000000000000 : ℝ)*base67 + (410830075989056377/47250000000000000000000000000000 : ℝ)*base70 + (56444610392943623/47250000000000000000000000000000 : ℝ)*base71 + (45358322209/118125000000000000000000000 : ℝ)*base74 + (96298923170306377/47250000000000000000000000000000 : ℝ)*base76 + (41796520859306377/47250000000000000000000000000000 : ℝ)*base78 + (489186774423056377/47250000000000000000000000000000 : ℝ)*base80 + (1617535940087/945000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1512093/500000000000000000000 : ℝ)*base90 + (1512093/500000000000000000000 : ℝ)*base92 + (1512093/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1692_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17221/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (197/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9851/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (861/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1692_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1692_box_0 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1146633009/10000000000 : ℝ)*x 0 + (2713477249/5000000000 : ℝ)*x 1 + (5426956417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1146633009/10000000000 : ℝ)^5159 ≤ (1676634354827/25000000000000 : ℝ)^4135 := by
    have hnat : (1146633009 : ℕ)^5159*25000000000000^4135 ≤ 1676634354827^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146633009 10000000000 1676634354827 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713477249/5000000000 : ℝ)^5159 ≤ (1865868839883/4000000000000 : ℝ)^4135 := by
    have hnat : (2713477249 : ℕ)^5159*4000000000000^4135 ≤ 1865868839883^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713477249 5000000000 1865868839883 4000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426956417/10000000000 : ℝ)^5159 ≤ (5830842697043/12500000000000 : ℝ)^4135 := by
    have hnat : (5426956417 : ℕ)^5159*12500000000000^4135 ≤ 5830842697043^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426956417 10000000000 5830842697043 12500000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1146633009/10000000000 : ℝ), (2713477249/5000000000 : ℝ), (5426956417/10000000000 : ℝ)] ![(1676634354827/25000000000000 : ℝ), (1865868839883/4000000000000 : ℝ), (5830842697043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1146633009/10000000000 : ℝ)|^5159 ≤ (1676634354827/25000000000000 : ℝ)^4135
        have hw : |(-1146633009/10000000000 : ℝ)|=(1146633009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713477249/5000000000 : ℝ)|^5159 ≤ (1865868839883/4000000000000 : ℝ)^4135
        have hw : |(2713477249/5000000000 : ℝ)|=(2713477249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426956417/10000000000 : ℝ)|^5159 ≤ (5830842697043/12500000000000 : ℝ)^4135
        have hw : |(5426956417/10000000000 : ℝ)|=(5426956417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_1 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613005027/5000000000 : ℝ)*x 0 + (-17903219/125000000 : ℝ)*x 1 + (5426955729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613005027/5000000000 : ℝ)^5159 ≤ (22250887479161/50000000000000 : ℝ)^4135 := by
    have hnat : (2613005027 : ℕ)^5159*50000000000000^4135 ≤ 22250887479161^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613005027 5000000000 22250887479161 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17903219/125000000 : ℝ)^5159 ≤ (4425745415557/50000000000000 : ℝ)^4135 := by
    have hnat : (17903219 : ℕ)^5159*50000000000000^4135 ≤ 4425745415557^4135*125000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17903219 125000000 4425745415557 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426955729/10000000000 : ℝ)^5159 ≤ (46646734198263/100000000000000 : ℝ)^4135 := by
    have hnat : (5426955729 : ℕ)^5159*100000000000000^4135 ≤ 46646734198263^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426955729 10000000000 46646734198263 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613005027/5000000000 : ℝ), (-17903219/125000000 : ℝ), (5426955729/10000000000 : ℝ)] ![(22250887479161/50000000000000 : ℝ), (4425745415557/50000000000000 : ℝ), (46646734198263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613005027/5000000000 : ℝ)|^5159 ≤ (22250887479161/50000000000000 : ℝ)^4135
        have hw : |(2613005027/5000000000 : ℝ)|=(2613005027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17903219/125000000 : ℝ)|^5159 ≤ (4425745415557/50000000000000 : ℝ)^4135
        have hw : |(-17903219/125000000 : ℝ)|=(17903219/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426955729/10000000000 : ℝ)|^5159 ≤ (46646734198263/100000000000000 : ℝ)^4135
        have hw : |(5426955729/10000000000 : ℝ)|=(5426955729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_2 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226010487/10000000000 : ℝ)*x 0 + (1356738867/2500000000 : ℝ)*x 1 + (-286451457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226010487/10000000000 : ℝ)^5159 ≤ (4450177955861/10000000000000 : ℝ)^4135 := by
    have hnat : (5226010487 : ℕ)^5159*10000000000000^4135 ≤ 4450177955861^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226010487 10000000000 4450177955861 10000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356738867/2500000000 : ℝ)^5159 ≤ (46646731399311/100000000000000 : ℝ)^4135 := by
    have hnat : (1356738867 : ℕ)^5159*100000000000000^4135 ≤ 46646731399311^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356738867 2500000000 46646731399311 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286451457/2000000000 : ℝ)^5159 ≤ (1770297803827/20000000000000 : ℝ)^4135 := by
    have hnat : (286451457 : ℕ)^5159*20000000000000^4135 ≤ 1770297803827^4135*2000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286451457 2000000000 1770297803827 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226010487/10000000000 : ℝ), (1356738867/2500000000 : ℝ), (-286451457/2000000000 : ℝ)] ![(4450177955861/10000000000000 : ℝ), (46646731399311/100000000000000 : ℝ), (1770297803827/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226010487/10000000000 : ℝ)|^5159 ≤ (4450177955861/10000000000000 : ℝ)^4135
        have hw : |(5226010487/10000000000 : ℝ)|=(5226010487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356738867/2500000000 : ℝ)|^5159 ≤ (46646731399311/100000000000000 : ℝ)^4135
        have hw : |(1356738867/2500000000 : ℝ)|=(1356738867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-286451457/2000000000 : ℝ)|^5159 ≤ (1770297803827/20000000000000 : ℝ)^4135
        have hw : |(-286451457/2000000000 : ℝ)|=(286451457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_3 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (902509483/2000000000 : ℝ)*x 0 + (989755861/2500000000 : ℝ)*x 1 + (3959024769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (902509483/2000000000 : ℝ)^5159 ≤ (18527297405557/50000000000000 : ℝ)^4135 := by
    have hnat : (902509483 : ℕ)^5159*50000000000000^4135 ≤ 18527297405557^4135*2000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902509483 2000000000 18527297405557 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989755861/2500000000 : ℝ)^5159 ≤ (31472696017587/100000000000000 : ℝ)^4135 := by
    have hnat : (989755861 : ℕ)^5159*100000000000000^4135 ≤ 31472696017587^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989755861 2500000000 31472696017587 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3959024769/10000000000 : ℝ)^5159 ≤ (15736354579647/50000000000000 : ℝ)^4135 := by
    have hnat : (3959024769 : ℕ)^5159*50000000000000^4135 ≤ 15736354579647^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3959024769 10000000000 15736354579647 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(902509483/2000000000 : ℝ), (989755861/2500000000 : ℝ), (3959024769/10000000000 : ℝ)] ![(18527297405557/50000000000000 : ℝ), (31472696017587/100000000000000 : ℝ), (15736354579647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(902509483/2000000000 : ℝ)|^5159 ≤ (18527297405557/50000000000000 : ℝ)^4135
        have hw : |(902509483/2000000000 : ℝ)|=(902509483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(989755861/2500000000 : ℝ)|^5159 ≤ (31472696017587/100000000000000 : ℝ)^4135
        have hw : |(989755861/2500000000 : ℝ)|=(989755861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3959024769/10000000000 : ℝ)|^5159 ≤ (15736354579647/50000000000000 : ℝ)^4135
        have hw : |(3959024769/10000000000 : ℝ)|=(3959024769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_4 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-458508871/2500000000 : ℝ)*x 0 + (5176356869/10000000000 : ℝ)*x 1 + (5176356551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458508871/2500000000 : ℝ)^5159 ≤ (1205026210067/10000000000000 : ℝ)^4135 := by
    have hnat : (458508871 : ℕ)^5159*10000000000000^4135 ≤ 1205026210067^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458508871 2500000000 1205026210067 10000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176356869/10000000000 : ℝ)^5159 ≤ (1758994825019/4000000000000 : ℝ)^4135 := by
    have hnat : (5176356869 : ℕ)^5159*4000000000000^4135 ≤ 1758994825019^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176356869 10000000000 1758994825019 4000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176356551/10000000000 : ℝ)^5159 ≤ (43974867254951/100000000000000 : ℝ)^4135 := by
    have hnat : (5176356551 : ℕ)^5159*100000000000000^4135 ≤ 43974867254951^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176356551 10000000000 43974867254951 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-458508871/2500000000 : ℝ), (5176356869/10000000000 : ℝ), (5176356551/10000000000 : ℝ)] ![(1205026210067/10000000000000 : ℝ), (1758994825019/4000000000000 : ℝ), (43974867254951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-458508871/2500000000 : ℝ)|^5159 ≤ (1205026210067/10000000000000 : ℝ)^4135
        have hw : |(-458508871/2500000000 : ℝ)|=(458508871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176356869/10000000000 : ℝ)|^5159 ≤ (1758994825019/4000000000000 : ℝ)^4135
        have hw : |(5176356869/10000000000 : ℝ)|=(5176356869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176356551/10000000000 : ℝ)|^5159 ≤ (43974867254951/100000000000000 : ℝ)^4135
        have hw : |(5176356551/10000000000 : ℝ)|=(5176356551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_5 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396709217/10000000000 : ℝ)*x 0 + (-192702051/1250000000 : ℝ)*x 1 + (647044621/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396709217/10000000000 : ℝ)^5159 ≤ (46322596124509/100000000000000 : ℝ)^4135 := by
    have hnat : (5396709217 : ℕ)^5159*100000000000000^4135 ≤ 46322596124509^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396709217 10000000000 46322596124509 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192702051/1250000000 : ℝ)^5159 ≤ (4851266092679/50000000000000 : ℝ)^4135 := by
    have hnat : (192702051 : ℕ)^5159*50000000000000^4135 ≤ 4851266092679^4135*1250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192702051 1250000000 4851266092679 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647044621/1250000000 : ℝ)^5159 ≤ (4397487167479/10000000000000 : ℝ)^4135 := by
    have hnat : (647044621 : ℕ)^5159*10000000000000^4135 ≤ 4397487167479^4135*1250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647044621 1250000000 4397487167479 10000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396709217/10000000000 : ℝ), (-192702051/1250000000 : ℝ), (647044621/1250000000 : ℝ)] ![(46322596124509/100000000000000 : ℝ), (4851266092679/50000000000000 : ℝ), (4397487167479/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396709217/10000000000 : ℝ)|^5159 ≤ (46322596124509/100000000000000 : ℝ)^4135
        have hw : |(5396709217/10000000000 : ℝ)|=(5396709217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192702051/1250000000 : ℝ)|^5159 ≤ (4851266092679/50000000000000 : ℝ)^4135
        have hw : |(-192702051/1250000000 : ℝ)|=(192702051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647044621/1250000000 : ℝ)|^5159 ≤ (4397487167479/10000000000000 : ℝ)^4135
        have hw : |(647044621/1250000000 : ℝ)|=(647044621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_6 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079341899/2000000000 : ℝ)*x 0 + (5176356759/10000000000 : ℝ)*x 1 + (-1541616311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079341899/2000000000 : ℝ)^5159 ≤ (9264519820329/20000000000000 : ℝ)^4135 := by
    have hnat : (1079341899 : ℕ)^5159*20000000000000^4135 ≤ 9264519820329^4135*2000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079341899 2000000000 9264519820329 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176356759/10000000000 : ℝ)^5159 ≤ (43974869459571/100000000000000 : ℝ)^4135 := by
    have hnat : (5176356759 : ℕ)^5159*100000000000000^4135 ≤ 43974869459571^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176356759 10000000000 43974869459571 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1541616311/10000000000 : ℝ)^5159 ≤ (4851265711841/50000000000000 : ℝ)^4135 := by
    have hnat : (1541616311 : ℕ)^5159*50000000000000^4135 ≤ 4851265711841^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541616311 10000000000 4851265711841 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079341899/2000000000 : ℝ), (5176356759/10000000000 : ℝ), (-1541616311/10000000000 : ℝ)] ![(9264519820329/20000000000000 : ℝ), (43974869459571/100000000000000 : ℝ), (4851265711841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079341899/2000000000 : ℝ)|^5159 ≤ (9264519820329/20000000000000 : ℝ)^4135
        have hw : |(1079341899/2000000000 : ℝ)|=(1079341899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176356759/10000000000 : ℝ)|^5159 ≤ (43974869459571/100000000000000 : ℝ)^4135
        have hw : |(5176356759/10000000000 : ℝ)|=(5176356759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1541616311/10000000000 : ℝ)|^5159 ≤ (4851265711841/50000000000000 : ℝ)^4135
        have hw : |(-1541616311/10000000000 : ℝ)|=(1541616311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_7 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3729802513/10000000000 : ℝ)*x 0 + (2174769671/5000000000 : ℝ)*x 1 + (4349538707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3729802513/10000000000 : ℝ)^5159 ≤ (29215762616751/100000000000000 : ℝ)^4135 := by
    have hnat : (3729802513 : ℕ)^5159*100000000000000^4135 ≤ 29215762616751^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729802513 10000000000 29215762616751 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174769671/5000000000 : ℝ)^5159 ≤ (35392121908357/100000000000000 : ℝ)^4135 := by
    have hnat : (2174769671 : ℕ)^5159*100000000000000^4135 ≤ 35392121908357^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174769671 5000000000 35392121908357 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4349538707/10000000000 : ℝ)^5159 ≤ (35392115461811/100000000000000 : ℝ)^4135 := by
    have hnat : (4349538707 : ℕ)^5159*100000000000000^4135 ≤ 35392115461811^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349538707 10000000000 35392115461811 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3729802513/10000000000 : ℝ), (2174769671/5000000000 : ℝ), (4349538707/10000000000 : ℝ)] ![(29215762616751/100000000000000 : ℝ), (35392121908357/100000000000000 : ℝ), (35392115461811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3729802513/10000000000 : ℝ)|^5159 ≤ (29215762616751/100000000000000 : ℝ)^4135
        have hw : |(3729802513/10000000000 : ℝ)|=(3729802513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2174769671/5000000000 : ℝ)|^5159 ≤ (35392121908357/100000000000000 : ℝ)^4135
        have hw : |(2174769671/5000000000 : ℝ)|=(2174769671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4349538707/10000000000 : ℝ)|^5159 ≤ (35392115461811/100000000000000 : ℝ)^4135
        have hw : |(4349538707/10000000000 : ℝ)|=(4349538707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_8 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1686499521/10000000000 : ℝ)*x 0 + (4992354461/10000000000 : ℝ)*x 1 + (1094089351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1686499521/10000000000 : ℝ)^5159 ≤ (2713285482893/25000000000000 : ℝ)^4135 := by
    have hnat : (1686499521 : ℕ)^5159*25000000000000^4135 ≤ 2713285482893^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686499521 10000000000 2713285482893 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992354461/10000000000 : ℝ)^5159 ≤ (42033266180723/100000000000000 : ℝ)^4135 := by
    have hnat : (4992354461 : ℕ)^5159*100000000000000^4135 ≤ 42033266180723^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992354461 10000000000 42033266180723 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094089351/2000000000 : ℝ)^5159 ≤ (47113591871731/100000000000000 : ℝ)^4135 := by
    have hnat : (1094089351 : ℕ)^5159*100000000000000^4135 ≤ 47113591871731^4135*2000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094089351 2000000000 47113591871731 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1686499521/10000000000 : ℝ), (4992354461/10000000000 : ℝ), (1094089351/2000000000 : ℝ)] ![(2713285482893/25000000000000 : ℝ), (42033266180723/100000000000000 : ℝ), (47113591871731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1686499521/10000000000 : ℝ)|^5159 ≤ (2713285482893/25000000000000 : ℝ)^4135
        have hw : |(-1686499521/10000000000 : ℝ)|=(1686499521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992354461/10000000000 : ℝ)|^5159 ≤ (42033266180723/100000000000000 : ℝ)^4135
        have hw : |(4992354461/10000000000 : ℝ)|=(4992354461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094089351/2000000000 : ℝ)|^5159 ≤ (47113591871731/100000000000000 : ℝ)^4135
        have hw : |(1094089351/2000000000 : ℝ)|=(1094089351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_9 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196397247/10000000000 : ℝ)*x 0 + (-353112501/2500000000 : ℝ)*x 1 + (5470446631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196397247/10000000000 : ℝ)^5159 ≤ (44187382999119/100000000000000 : ℝ)^4135 := by
    have hnat : (5196397247 : ℕ)^5159*100000000000000^4135 ≤ 44187382999119^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196397247 10000000000 44187382999119 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353112501/2500000000 : ℝ)^5159 ≤ (4349513220223/50000000000000 : ℝ)^4135 := by
    have hnat : (353112501 : ℕ)^5159*50000000000000^4135 ≤ 4349513220223^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353112501 2500000000 4349513220223 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470446631/10000000000 : ℝ)^5159 ≤ (4711359053933/10000000000000 : ℝ)^4135 := by
    have hnat : (5470446631 : ℕ)^5159*10000000000000^4135 ≤ 4711359053933^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470446631 10000000000 4711359053933 10000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196397247/10000000000 : ℝ), (-353112501/2500000000 : ℝ), (5470446631/10000000000 : ℝ)] ![(44187382999119/100000000000000 : ℝ), (4349513220223/50000000000000 : ℝ), (4711359053933/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196397247/10000000000 : ℝ)|^5159 ≤ (44187382999119/100000000000000 : ℝ)^4135
        have hw : |(5196397247/10000000000 : ℝ)|=(5196397247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-353112501/2500000000 : ℝ)|^5159 ≤ (4349513220223/50000000000000 : ℝ)^4135
        have hw : |(-353112501/2500000000 : ℝ)|=(353112501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470446631/10000000000 : ℝ)|^5159 ≤ (4711359053933/10000000000000 : ℝ)^4135
        have hw : |(5470446631/10000000000 : ℝ)|=(5470446631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_10 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40596853/78125000 : ℝ)*x 0 + (136761167/250000000 : ℝ)*x 1 + (-1412450023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40596853/78125000 : ℝ)^5159 ≤ (22093691165367/50000000000000 : ℝ)^4135 := by
    have hnat : (40596853 : ℕ)^5159*50000000000000^4135 ≤ 22093691165367^4135*78125000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40596853 78125000 22093691165367 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136761167/250000000 : ℝ)^5159 ≤ (47113591065843/100000000000000 : ℝ)^4135 := by
    have hnat : (136761167 : ℕ)^5159*100000000000000^4135 ≤ 47113591065843^4135*250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136761167 250000000 47113591065843 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1412450023/10000000000 : ℝ)^5159 ≤ (4349513293221/50000000000000 : ℝ)^4135 := by
    have hnat : (1412450023 : ℕ)^5159*50000000000000^4135 ≤ 4349513293221^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412450023 10000000000 4349513293221 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40596853/78125000 : ℝ), (136761167/250000000 : ℝ), (-1412450023/10000000000 : ℝ)] ![(22093691165367/50000000000000 : ℝ), (47113591065843/100000000000000 : ℝ), (4349513293221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40596853/78125000 : ℝ)|^5159 ≤ (22093691165367/50000000000000 : ℝ)^4135
        have hw : |(40596853/78125000 : ℝ)|=(40596853/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136761167/250000000 : ℝ)|^5159 ≤ (47113591065843/100000000000000 : ℝ)^4135
        have hw : |(136761167/250000000 : ℝ)|=(136761167/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1412450023/10000000000 : ℝ)|^5159 ≤ (4349513293221/50000000000000 : ℝ)^4135
        have hw : |(-1412450023/10000000000 : ℝ)|=(1412450023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_11 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4643366987/10000000000 : ℝ)*x 0 + (1945536903/5000000000 : ℝ)*x 1 + (778214843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4643366987/10000000000 : ℝ)^5159 ≤ (1199987893501/3125000000000 : ℝ)^4135 := by
    have hnat : (4643366987 : ℕ)^5159*3125000000000^4135 ≤ 1199987893501^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4643366987 10000000000 1199987893501 3125000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1945536903/5000000000 : ℝ)^5159 ≤ (15400095838153/50000000000000 : ℝ)^4135 := by
    have hnat : (1945536903 : ℕ)^5159*50000000000000^4135 ≤ 15400095838153^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945536903 5000000000 15400095838153 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (778214843/2000000000 : ℝ)^5159 ≤ (7700048928881/25000000000000 : ℝ)^4135 := by
    have hnat : (778214843 : ℕ)^5159*25000000000000^4135 ≤ 7700048928881^4135*2000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778214843 2000000000 7700048928881 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4643366987/10000000000 : ℝ), (1945536903/5000000000 : ℝ), (778214843/2000000000 : ℝ)] ![(1199987893501/3125000000000 : ℝ), (15400095838153/50000000000000 : ℝ), (7700048928881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4643366987/10000000000 : ℝ)|^5159 ≤ (1199987893501/3125000000000 : ℝ)^4135
        have hw : |(4643366987/10000000000 : ℝ)|=(4643366987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1945536903/5000000000 : ℝ)|^5159 ≤ (15400095838153/50000000000000 : ℝ)^4135
        have hw : |(1945536903/5000000000 : ℝ)|=(1945536903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(778214843/2000000000 : ℝ)|^5159 ≤ (7700048928881/25000000000000 : ℝ)^4135
        have hw : |(778214843/2000000000 : ℝ)|=(778214843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_12 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1289285593/10000000000 : ℝ)*x 0 + (5601869769/10000000000 : ℝ)*x 1 + (321941721/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1289285593/10000000000 : ℝ)^5159 ≤ (1552616272471/20000000000000 : ℝ)^4135 := by
    have hnat : (1289285593 : ℕ)^5159*20000000000000^4135 ≤ 1552616272471^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289285593 10000000000 1552616272471 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5601869769/10000000000 : ℝ)^5159 ≤ (48529930679161/100000000000000 : ℝ)^4135 := by
    have hnat : (5601869769 : ℕ)^5159*100000000000000^4135 ≤ 48529930679161^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5601869769 10000000000 48529930679161 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321941721/625000000 : ℝ)^5159 ≤ (43706987949821/100000000000000 : ℝ)^4135 := by
    have hnat : (321941721 : ℕ)^5159*100000000000000^4135 ≤ 43706987949821^4135*625000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321941721 625000000 43706987949821 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1289285593/10000000000 : ℝ), (5601869769/10000000000 : ℝ), (321941721/625000000 : ℝ)] ![(1552616272471/20000000000000 : ℝ), (48529930679161/100000000000000 : ℝ), (43706987949821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1289285593/10000000000 : ℝ)|^5159 ≤ (1552616272471/20000000000000 : ℝ)^4135
        have hw : |(-1289285593/10000000000 : ℝ)|=(1289285593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5601869769/10000000000 : ℝ)|^5159 ≤ (48529930679161/100000000000000 : ℝ)^4135
        have hw : |(5601869769/10000000000 : ℝ)|=(5601869769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321941721/625000000 : ℝ)|^5159 ≤ (43706987949821/100000000000000 : ℝ)^4135
        have hw : |(321941721/625000000 : ℝ)|=(321941721/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_13 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5413962641/10000000000 : ℝ)*x 0 + (-776091127/5000000000 : ℝ)*x 1 + (5151067987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413962641/10000000000 : ℝ)^5159 ≤ (23253719119923/50000000000000 : ℝ)^4135 := by
    have hnat : (5413962641 : ℕ)^5159*50000000000000^4135 ≤ 23253719119923^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413962641 10000000000 23253719119923 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776091127/5000000000 : ℝ)^5159 ≤ (9785569028469/100000000000000 : ℝ)^4135 := by
    have hnat : (776091127 : ℕ)^5159*100000000000000^4135 ≤ 9785569028469^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776091127 5000000000 9785569028469 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151067987/10000000000 : ℝ)^5159 ≤ (10926748181059/25000000000000 : ℝ)^4135 := by
    have hnat : (5151067987 : ℕ)^5159*25000000000000^4135 ≤ 10926748181059^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151067987 10000000000 10926748181059 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413962641/10000000000 : ℝ), (-776091127/5000000000 : ℝ), (5151067987/10000000000 : ℝ)] ![(23253719119923/50000000000000 : ℝ), (9785569028469/100000000000000 : ℝ), (10926748181059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413962641/10000000000 : ℝ)|^5159 ≤ (23253719119923/50000000000000 : ℝ)^4135
        have hw : |(5413962641/10000000000 : ℝ)|=(5413962641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-776091127/5000000000 : ℝ)|^5159 ≤ (9785569028469/100000000000000 : ℝ)^4135
        have hw : |(-776091127/5000000000 : ℝ)|=(776091127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151067987/10000000000 : ℝ)|^5159 ≤ (10926748181059/25000000000000 : ℝ)^4135
        have hw : |(5151067987/10000000000 : ℝ)|=(5151067987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_14 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216558557/400000000 : ℝ)*x 0 + (2575532807/5000000000 : ℝ)*x 1 + (-1552183697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216558557/400000000 : ℝ)^5159 ≤ (46507452001233/100000000000000 : ℝ)^4135 := by
    have hnat : (216558557 : ℕ)^5159*100000000000000^4135 ≤ 46507452001233^4135*400000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216558557 400000000 46507452001233 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575532807/5000000000 : ℝ)^5159 ≤ (43706967602979/100000000000000 : ℝ)^4135 := by
    have hnat : (2575532807 : ℕ)^5159*100000000000000^4135 ≤ 43706967602979^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575532807 5000000000 43706967602979 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1552183697/10000000000 : ℝ)^5159 ≤ (9785580378571/100000000000000 : ℝ)^4135 := by
    have hnat : (1552183697 : ℕ)^5159*100000000000000^4135 ≤ 9785580378571^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552183697 10000000000 9785580378571 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216558557/400000000 : ℝ), (2575532807/5000000000 : ℝ), (-1552183697/10000000000 : ℝ)] ![(46507452001233/100000000000000 : ℝ), (43706967602979/100000000000000 : ℝ), (9785580378571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216558557/400000000 : ℝ)|^5159 ≤ (46507452001233/100000000000000 : ℝ)^4135
        have hw : |(216558557/400000000 : ℝ)|=(216558557/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575532807/5000000000 : ℝ)|^5159 ≤ (43706967602979/100000000000000 : ℝ)^4135
        have hw : |(2575532807/5000000000 : ℝ)|=(2575532807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1552183697/10000000000 : ℝ)|^5159 ≤ (9785580378571/100000000000000 : ℝ)^4135
        have hw : |(-1552183697/10000000000 : ℝ)|=(1552183697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_box_15 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1823914021/5000000000 : ℝ)*x 0 + (4388844931/10000000000 : ℝ)*x 1 + (175553683/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823914021/5000000000 : ℝ)^5159 ≤ (28416830380763/100000000000000 : ℝ)^4135 := by
    have hnat : (1823914021 : ℕ)^5159*100000000000000^4135 ≤ 28416830380763^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823914021 5000000000 28416830380763 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4388844931/10000000000 : ℝ)^5159 ≤ (35791599332637/100000000000000 : ℝ)^4135 := by
    have hnat : (4388844931 : ℕ)^5159*100000000000000^4135 ≤ 35791599332637^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388844931 10000000000 35791599332637 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175553683/400000000 : ℝ)^5159 ≤ (7158314054749/20000000000000 : ℝ)^4135 := by
    have hnat : (175553683 : ℕ)^5159*20000000000000^4135 ≤ 7158314054749^4135*400000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175553683 400000000 7158314054749 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1823914021/5000000000 : ℝ), (4388844931/10000000000 : ℝ), (175553683/400000000 : ℝ)] ![(28416830380763/100000000000000 : ℝ), (35791599332637/100000000000000 : ℝ), (7158314054749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1823914021/5000000000 : ℝ)|^5159 ≤ (28416830380763/100000000000000 : ℝ)^4135
        have hw : |(1823914021/5000000000 : ℝ)|=(1823914021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4388844931/10000000000 : ℝ)|^5159 ≤ (35791599332637/100000000000000 : ℝ)^4135
        have hw : |(4388844931/10000000000 : ℝ)|=(4388844931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(175553683/400000000 : ℝ)|^5159 ≤ (7158314054749/20000000000000 : ℝ)^4135
        have hw : |(175553683/400000000 : ℝ)|=(175553683/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1692_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (861/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66589/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(28989/50000 : ℝ) ∧ (647/800 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45081/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (861/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9851/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (861/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9851/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (861/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9851/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (861/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9851/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (861/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9851/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (861/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9851/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9851/100000 : ℝ) ^ (5151/1024 : ℝ) ≤ (108103759531849/12500000000000000000 : ℝ) := by
    have hpowers : (9851/100000 : ℝ)^5151 ≤ (108103759531849/12500000000000000000 : ℝ)^1024 := by
      have hnat : (9851 : ℕ)^5151*12500000000000000000^1024 ≤ 108103759531849^1024*100000^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9851 100000 108103759531849 12500000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9851/100000 : ℝ)) (X := (108103759531849/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (861/5000 : ℝ) ^ (5151/1024 : ℝ) ≤ (358903622247199/2500000000000000000 : ℝ) := by
    have hpowers : (861/5000 : ℝ)^5151 ≤ (358903622247199/2500000000000000000 : ℝ)^1024 := by
      have hnat : (861 : ℕ)^5151*2500000000000000000^1024 ≤ 358903622247199^1024*5000^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        861 5000 358903622247199 2500000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (861/5000 : ℝ)) (X := (358903622247199/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250108103759531849/6250000000000000000 : ℝ) ≤ (2500008596193573/2500000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (6250108103759531849/6250000000000000000 : ℝ)^1024 ≤ (2500008596193573/2500000000000000 : ℝ)^5151 := by
      have hnat : (6250108103759531849 : ℕ)^1024*2500000000000000^5151 ≤ 2500008596193573^5151*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250108103759531849 6250000000000000000 2500008596193573 2500000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500008596193573/2500000000000000 : ℝ)) (X := (6250108103759531849/6250000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125475655467691961/3125000000000000000 : ℝ) ≤ (10000302568978277/10000000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (3125475655467691961/3125000000000000000 : ℝ)^1024 ≤ (10000302568978277/10000000000000000 : ℝ)^5151 := by
      have hnat : (3125475655467691961 : ℕ)^1024*10000000000000000^5151 ≤ 10000302568978277^5151*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125475655467691961 3125000000000000000 10000302568978277 10000000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000302568978277/10000000000000000 : ℝ)) (X := (3125475655467691961/3125000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250358903622247199/1250000000000000000 : ℝ) ≤ (5000285376591131/5000000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (1250358903622247199/1250000000000000000 : ℝ)^1024 ≤ (5000285376591131/5000000000000000 : ℝ)^5151 := by
      have hnat : (1250358903622247199 : ℕ)^1024*5000000000000000^5151 ≤ 5000285376591131^5151*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250358903622247199 1250000000000000000 5000285376591131 5000000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000285376591131/5000000000000000 : ℝ)) (X := (1250358903622247199/1250000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(108103759531849/12500000000000000000 : ℝ) ≤ ((36842484808107422639/36845000000000000000 : ℝ)+2*(53636840797/147380000000000 : ℝ)*(9851/100000 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (36842484808107422639/36845000000000000000 : ℝ)+2*(53636840797/147380000000000 : ℝ)*(9851/100000 : ℝ)=(2500008596193573/2500000000000000 : ℝ) by norm_num, show 1+2*(108103759531849/12500000000000000000 : ℝ)=(6250108103759531849/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(358903622247199/2500000000000000000 : ℝ)+(108103759531849/12500000000000000000 : ℝ) ≤ ((36842484808107422639/36845000000000000000 : ℝ)+(53636840797/147380000000000 : ℝ)*((861/5000 : ℝ)+(9851/100000 : ℝ)))^(5151/1024 : ℝ) := by
    rw [show (36842484808107422639/36845000000000000000 : ℝ)+(53636840797/147380000000000 : ℝ)*((861/5000 : ℝ)+(9851/100000 : ℝ))=(10000302568978277/10000000000000000 : ℝ) by norm_num, show 1+(358903622247199/2500000000000000000 : ℝ)+(108103759531849/12500000000000000000 : ℝ)=(3125475655467691961/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(358903622247199/2500000000000000000 : ℝ) ≤ ((36842484808107422639/36845000000000000000 : ℝ)+2*(53636840797/147380000000000 : ℝ)*(861/5000 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (36842484808107422639/36845000000000000000 : ℝ)+2*(53636840797/147380000000000 : ℝ)*(861/5000 : ℝ)=(5000285376591131/5000000000000000 : ℝ) by norm_num, show 1+2*(358903622247199/2500000000000000000 : ℝ)=(1250358903622247199/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36842484808107422639/36845000000000000000 : ℝ)*(X 1 0+X 2 0)+(53636840797/147380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (9851/100000 : ℝ)) (hi := (861/5000 : ℝ)) (c := (36842484808107422639/36845000000000000000 : ℝ)) (alpha := (53636840797/147380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36842484808107422639/36845000000000000000 : ℝ)*(X 0 1+X 2 1)+(53636840797/147380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (9851/100000 : ℝ)) (hi := (861/5000 : ℝ)) (c := (36842484808107422639/36845000000000000000 : ℝ)) (alpha := (53636840797/147380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36842484808107422639/36845000000000000000 : ℝ)*(X 0 2+X 1 2)+(53636840797/147380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (9851/100000 : ℝ)) (hi := (861/5000 : ℝ)) (c := (36842484808107422639/36845000000000000000 : ℝ)) (alpha := (53636840797/147380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1146633009/10000000000 : ℝ)*X 0 0+(2713477249/5000000000 : ℝ)*X 0 1+(5426956417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2613005027/5000000000 : ℝ)*X 1 0+(-17903219/125000000 : ℝ)*X 1 1+(5426955729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5226010487/10000000000 : ℝ)*X 2 0+(1356738867/2500000000 : ℝ)*X 2 1+(-286451457/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((902509483/2000000000 : ℝ)*X 0 0+(989755861/2500000000 : ℝ)*X 0 1+(3959024769/10000000000 : ℝ)*X 0 2+(902509483/2000000000 : ℝ)*X 1 0+(989755861/2500000000 : ℝ)*X 1 1+(3959024769/10000000000 : ℝ)*X 1 2+(902509483/2000000000 : ℝ)*X 2 0+(989755861/2500000000 : ℝ)*X 2 1+(3959024769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-458508871/2500000000 : ℝ)*X 0 0+(5176356869/10000000000 : ℝ)*X 0 1+(5176356551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5396709217/10000000000 : ℝ)*X 1 0+(-192702051/1250000000 : ℝ)*X 1 1+(647044621/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1079341899/2000000000 : ℝ)*X 2 0+(5176356759/10000000000 : ℝ)*X 2 1+(-1541616311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3729802513/10000000000 : ℝ)*X 0 0+(2174769671/5000000000 : ℝ)*X 0 1+(4349538707/10000000000 : ℝ)*X 0 2+(3729802513/10000000000 : ℝ)*X 1 0+(2174769671/5000000000 : ℝ)*X 1 1+(4349538707/10000000000 : ℝ)*X 1 2+(3729802513/10000000000 : ℝ)*X 2 0+(2174769671/5000000000 : ℝ)*X 2 1+(4349538707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1686499521/10000000000 : ℝ)*X 0 0+(4992354461/10000000000 : ℝ)*X 0 1+(1094089351/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196397247/10000000000 : ℝ)*X 1 0+(-353112501/2500000000 : ℝ)*X 1 1+(5470446631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((40596853/78125000 : ℝ)*X 2 0+(136761167/250000000 : ℝ)*X 2 1+(-1412450023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4643366987/10000000000 : ℝ)*X 0 0+(1945536903/5000000000 : ℝ)*X 0 1+(778214843/2000000000 : ℝ)*X 0 2+(4643366987/10000000000 : ℝ)*X 1 0+(1945536903/5000000000 : ℝ)*X 1 1+(778214843/2000000000 : ℝ)*X 1 2+(4643366987/10000000000 : ℝ)*X 2 0+(1945536903/5000000000 : ℝ)*X 2 1+(778214843/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1289285593/10000000000 : ℝ)*X 0 0+(5601869769/10000000000 : ℝ)*X 0 1+(321941721/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5413962641/10000000000 : ℝ)*X 1 0+(-776091127/5000000000 : ℝ)*X 1 1+(5151067987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((216558557/400000000 : ℝ)*X 2 0+(2575532807/5000000000 : ℝ)*X 2 1+(-1552183697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1823914021/5000000000 : ℝ)*X 0 0+(4388844931/10000000000 : ℝ)*X 0 1+(175553683/400000000 : ℝ)*X 0 2+(1823914021/5000000000 : ℝ)*X 1 0+(4388844931/10000000000 : ℝ)*X 1 1+(175553683/400000000 : ℝ)*X 1 2+(1823914021/5000000000 : ℝ)*X 2 0+(4388844931/10000000000 : ℝ)*X 2 1+(175553683/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66589/100000 : ℝ) ≤ (-38333945207734746747626091752493/57570312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2501467/12500000000000 : ℝ)*(lower0) + (107830239/100000000000000 : ℝ)*(lower2) + (15487687/25000000000000 : ℝ)*(lower4) + (163836935131833/12500000000000 : ℝ)*(major0) + (163836935131833/12500000000000 : ℝ)*(major1) + (163836935131833/12500000000000 : ℝ)*(major2) + (1950182588387047/100000000000000 : ℝ)*(sp4) + (975089819286391/50000000000000 : ℝ)*(sp5) + (487546117475157/25000000000000 : ℝ)*(sp6) + (693391705695153/100000000000000 : ℝ)*(sp7) + (2312703337/100000000000000 : ℝ)*(sp8) + (2631258801/50000000000000 : ℝ)*(sp13) + (107797439/25000000000000 : ℝ)*(sp14) + (1223887241/12500000000000 : ℝ)*(sp15) + (346700748396541/50000000000000 : ℝ)*(f.failure) + (121886556318149/6250000000000 : ℝ)*(f.sum) + (12122722973863/1842250000000000000000000000 : ℝ)*base66 + (1044691395271142287/460562500000000000000000000000000 : ℝ)*base67 + (2175602794101079787/460562500000000000000000000000000 : ℝ)*base69 + (5955826617281545213/460562500000000000000000000000000 : ℝ)*base72 + (16906988082719/3684500000000000000000000000 : ℝ)*base73 + (2205200466423454787/460562500000000000000000000000000 : ℝ)*base75 + (3960094792249954787/460562500000000000000000000000000 : ℝ)*base77 + (475352029978392287/460562500000000000000000000000000 : ℝ)*base79 + (27345569650269/7369000000000000000000000000 : ℝ)*base81 + (5733197/2500000000000000000000 : ℝ)*base89 + (5733197/2500000000000000000000 : ℝ)*base91 + (5733197/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (28989/50000 : ℝ) ≤ (1068138080436416048228150119096923/1842250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (219329327/100000000000000 : ℝ)*(lower0) + (220948673/100000000000000 : ℝ)*(lower1) + (102465023/50000000000000 : ℝ)*(lower3) + (1410317037605481/100000000000000 : ℝ)*(major0) + (1410317037605481/100000000000000 : ℝ)*(major1) + (1410317037605481/100000000000000 : ℝ)*(major2) + (205519681981859/10000000000000 : ℝ)*(sp0) + (2055202501182133/100000000000000 : ℝ)*(sp1) + (2055174253332949/100000000000000 : ℝ)*(sp2) + (746100822214531/100000000000000 : ℝ)*(sp3) + (133268493/50000000000000 : ℝ)*(sp5) + (758183841/20000000000000 : ℝ)*(sp7) + (2851438617/10000000000000 : ℝ)*(sp10) + (5947900529/100000000000000 : ℝ)*(sp12) + (93263076641717/12500000000000 : ℝ)*(f.failure) + (2055202767719119/100000000000000 : ℝ)*(f.sum) + (1386899562263/736900000000000000000000000 : ℝ)*base66 + (2943253990771634359/3684500000000000000000000000000000 : ℝ)*base67 + (36167306630643134359/3684500000000000000000000000000000 : ℝ)*base69 + (6594299673253865641/3684500000000000000000000000000000 : ℝ)*base72 + (12835244170163/7369000000000000000000000000 : ℝ)*base73 + (4472906648323634359/3684500000000000000000000000000000 : ℝ)*base75 + (8408607526919365641/3684500000000000000000000000000000 : ℝ)*base78 + (18617835059292134359/3684500000000000000000000000000000 : ℝ)*base79 + (62308433348187/3684500000000000000000000000 : ℝ)*base82 + (3763189/625000000000000000000 : ℝ)*base89 + (3763189/625000000000000000000 : ℝ)*base91 + (3763189/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (647/800 : ℝ) ≤ (37249217358068015139619846733091/46056250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2720519/12500000000000 : ℝ)*(upper2) + (40820753/100000000000000 : ℝ)*(lower3) + (6133301/100000000000000 : ℝ)*(lower4) + (946171/25000000000000 : ℝ)*(lower5) + (36007032635591/2500000000000 : ℝ)*(major0) + (36007032635591/2500000000000 : ℝ)*(major1) + (36007032635591/2500000000000 : ℝ)*(major2) + (4970848417/100000000000000 : ℝ)*(sp1) + (831562697/50000000000000 : ℝ)*(sp3) + (57247183/25000000000000 : ℝ)*(sp4) + (522911613632589/25000000000000 : ℝ)*(sp8) + (2091641712670671/100000000000000 : ℝ)*(sp9) + (130727917719943/6250000000000 : ℝ)*(sp10) + (152391008829801/20000000000000 : ℝ)*(sp11) + (761956707274399/100000000000000 : ℝ)*(f.failure) + (130727917719943/6250000000000 : ℝ)*(f.sum) + (41880768809209/7369000000000000000000000000 : ℝ)*base66 + (908061086709080351/92112500000000000000000000000000 : ℝ)*base68 + (121378884518167851/92112500000000000000000000000000 : ℝ)*base70 + (27158254273955351/92112500000000000000000000000000 : ℝ)*base72 + (16142770282509/3684500000000000000000000000 : ℝ)*base74 + (378429158343892851/92112500000000000000000000000000 : ℝ)*base76 + (1329575665333367851/92112500000000000000000000000000 : ℝ)*base78 + (301768286212880351/92112500000000000000000000000000 : ℝ)*base80 + (26865859150573/7369000000000000000000000000 : ℝ)*base82 + (21952783/5000000000000000000000 : ℝ)*base89 + (21952783/5000000000000000000000 : ℝ)*base91 + (21952783/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-45081/50000 : ℝ) ≤ (-415239011820194983736213217094587/460562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6290599/10000000000000 : ℝ)*(upper1) + (179049023/50000000000000 : ℝ)*(upper3) + (10119799/20000000000000 : ℝ)*(upper5) + (743805733307489/50000000000000 : ℝ)*(major0) + (743805733307489/50000000000000 : ℝ)*(major1) + (743805733307489/50000000000000 : ℝ)*(major2) + (9392700993/100000000000000 : ℝ)*(sp4) + (8655977189/10000000000000 : ℝ)*(sp5) + (7863422623/3125000000000 : ℝ)*(sp6) + (44562786593/100000000000000 : ℝ)*(sp7) + (138641914865397/6250000000000 : ℝ)*(sp12) + (443638694155091/20000000000000 : ℝ)*(sp13) + (138626775063963/6250000000000 : ℝ)*(sp14) + (19673784343187/2500000000000 : ℝ)*(sp15) + (98374492064259/12500000000000 : ℝ)*(f.failure) + (138642501909209/6250000000000 : ℝ)*(f.sum) + (14457997837283/7369000000000000000000000000 : ℝ)*base66 + (26334677916494656529/1842250000000000000000000000000000 : ℝ)*base68 + (23415468416738406529/1842250000000000000000000000000000 : ℝ)*base70 + (9855640879106406529/1842250000000000000000000000000000 : ℝ)*base72 + (25014960922029/3684500000000000000000000000 : ℝ)*base74 + (31088264266115906529/1842250000000000000000000000000000 : ℝ)*base76 + (3255206666139843471/1842250000000000000000000000000000 : ℝ)*base77 + (6639869093279406529/1842250000000000000000000000000000 : ℝ)*base80 + (3492197765397/1473800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (799597/625000000000000000000 : ℝ)*base90 + (799597/625000000000000000000 : ℝ)*base92 + (799597/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1692_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (861/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66589/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28989/50000 : ℝ) else (647/800 : ℝ) ≤ X j i ∧ X j i ≤ (45081/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1692_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1692_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8621/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66589/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28989/50000 : ℝ) else (647/800 : ℝ) ≤ X j i ∧ X j i ≤ (45081/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1692_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1692_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1692_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8621/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66589/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28989/50000 : ℝ) else (647/800 : ℝ) ≤ X j i ∧ X j i ≤ (45081/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1692_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

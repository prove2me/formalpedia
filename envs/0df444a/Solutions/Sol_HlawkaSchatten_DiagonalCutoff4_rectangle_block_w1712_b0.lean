-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1712_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:53:35.534454+00:00
-- url     : https://prove2.me/submissions/5f26bd98-e041-4688-8002-18f873072801

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
theorem support_rectangle_w1712_s0_0 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1330723677/10000000000 : ℝ)*x 0 + (5693867559/10000000000 : ℝ)*x 1 + (310144283/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1330723677/10000000000 : ℝ)^5319 ≤ (8227270040903/100000000000000 : ℝ)^4295 := by
    have hnat : (1330723677 : ℕ)^5319*100000000000000^4295 ≤ 8227270040903^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330723677 10000000000 8227270040903 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5693867559/10000000000 : ℝ)^5319 ≤ (49784296640067/100000000000000 : ℝ)^4295 := by
    have hnat : (5693867559 : ℕ)^5319*100000000000000^4295 ≤ 49784296640067^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5693867559 10000000000 49784296640067 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310144283/625000000 : ℝ)^5319 ≤ (5248554162993/12500000000000 : ℝ)^4295 := by
    have hnat : (310144283 : ℕ)^5319*12500000000000^4295 ≤ 5248554162993^4295*625000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310144283 625000000 5248554162993 12500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1330723677/10000000000 : ℝ), (5693867559/10000000000 : ℝ), (310144283/625000000 : ℝ)] ![(8227270040903/100000000000000 : ℝ), (49784296640067/100000000000000 : ℝ), (5248554162993/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1330723677/10000000000 : ℝ)|^5319 ≤ (8227270040903/100000000000000 : ℝ)^4295
        have hw : |(-1330723677/10000000000 : ℝ)|=(1330723677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5693867559/10000000000 : ℝ)|^5319 ≤ (49784296640067/100000000000000 : ℝ)^4295
        have hw : |(5693867559/10000000000 : ℝ)|=(5693867559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310144283/625000000 : ℝ)|^5319 ≤ (5248554162993/12500000000000 : ℝ)^4295
        have hw : |(310144283/625000000 : ℝ)|=(310144283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s0_1 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5402881179/10000000000 : ℝ)*x 0 + (-69064153/400000000 : ℝ)*x 1 + (2481154177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402881179/10000000000 : ℝ)^5319 ≤ (46652920250881/100000000000000 : ℝ)^4295 := by
    have hnat : (5402881179 : ℕ)^5319*100000000000000^4295 ≤ 46652920250881^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402881179 10000000000 46652920250881 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69064153/400000000 : ℝ)^5319 ≤ (5679324123619/50000000000000 : ℝ)^4295 := by
    have hnat : (69064153 : ℕ)^5319*50000000000000^4295 ≤ 5679324123619^4295*400000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69064153 400000000 5679324123619 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2481154177/5000000000 : ℝ)^5319 ≤ (41988431480627/100000000000000 : ℝ)^4295 := by
    have hnat : (2481154177 : ℕ)^5319*100000000000000^4295 ≤ 41988431480627^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2481154177 5000000000 41988431480627 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402881179/10000000000 : ℝ), (-69064153/400000000 : ℝ), (2481154177/5000000000 : ℝ)] ![(46652920250881/100000000000000 : ℝ), (5679324123619/50000000000000 : ℝ), (41988431480627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402881179/10000000000 : ℝ)|^5319 ≤ (46652920250881/100000000000000 : ℝ)^4295
        have hw : |(5402881179/10000000000 : ℝ)|=(5402881179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69064153/400000000 : ℝ)|^5319 ≤ (5679324123619/50000000000000 : ℝ)^4295
        have hw : |(-69064153/400000000 : ℝ)|=(69064153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2481154177/5000000000 : ℝ)|^5319 ≤ (41988431480627/100000000000000 : ℝ)^4295
        have hw : |(2481154177/5000000000 : ℝ)|=(2481154177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s0_2 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675360139/1250000000 : ℝ)*x 0 + (4962308431/10000000000 : ℝ)*x 1 + (-863301907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675360139/1250000000 : ℝ)^5319 ≤ (9330583906883/20000000000000 : ℝ)^4295 := by
    have hnat : (675360139 : ℕ)^5319*20000000000000^4295 ≤ 9330583906883^4295*1250000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675360139 1250000000 9330583906883 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4962308431/10000000000 : ℝ)^5319 ≤ (41988432287497/100000000000000 : ℝ)^4295 := by
    have hnat : (4962308431 : ℕ)^5319*100000000000000^4295 ≤ 41988432287497^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4962308431 10000000000 41988432287497 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863301907/5000000000 : ℝ)^5319 ≤ (567932407881/5000000000000 : ℝ)^4295 := by
    have hnat : (863301907 : ℕ)^5319*5000000000000^4295 ≤ 567932407881^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863301907 5000000000 567932407881 5000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675360139/1250000000 : ℝ), (4962308431/10000000000 : ℝ), (-863301907/5000000000 : ℝ)] ![(9330583906883/20000000000000 : ℝ), (41988432287497/100000000000000 : ℝ), (567932407881/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675360139/1250000000 : ℝ)|^5319 ≤ (9330583906883/20000000000000 : ℝ)^4295
        have hw : |(675360139/1250000000 : ℝ)|=(675360139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4962308431/10000000000 : ℝ)|^5319 ≤ (41988432287497/100000000000000 : ℝ)^4295
        have hw : |(4962308431/10000000000 : ℝ)|=(4962308431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-863301907/5000000000 : ℝ)|^5319 ≤ (567932407881/5000000000000 : ℝ)^4295
        have hw : |(-863301907/5000000000 : ℝ)|=(863301907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s0_3 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4037895133/10000000000 : ℝ)*x 0 + (122409701/400000000 : ℝ)*x 1 + (1297720143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4037895133/10000000000 : ℝ)^5319 ≤ (32527882617289/100000000000000 : ℝ)^4295 := by
    have hnat : (4037895133 : ℕ)^5319*100000000000000^4295 ≤ 32527882617289^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037895133 10000000000 32527882617289 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122409701/400000000 : ℝ)^5319 ≤ (1442219741977/6250000000000 : ℝ)^4295 := by
    have hnat : (122409701 : ℕ)^5319*6250000000000^4295 ≤ 1442219741977^4295*400000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122409701 400000000 1442219741977 6250000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297720143/2500000000 : ℝ)^5319 ≤ (44396601495993/100000000000000 : ℝ)^4295 := by
    have hnat : (1297720143 : ℕ)^5319*100000000000000^4295 ≤ 44396601495993^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297720143 2500000000 44396601495993 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4037895133/10000000000 : ℝ), (122409701/400000000 : ℝ), (1297720143/2500000000 : ℝ)] ![(32527882617289/100000000000000 : ℝ), (1442219741977/6250000000000 : ℝ), (44396601495993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4037895133/10000000000 : ℝ)|^5319 ≤ (32527882617289/100000000000000 : ℝ)^4295
        have hw : |(4037895133/10000000000 : ℝ)|=(4037895133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122409701/400000000 : ℝ)|^5319 ≤ (1442219741977/6250000000000 : ℝ)^4295
        have hw : |(122409701/400000000 : ℝ)|=(122409701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297720143/2500000000 : ℝ)|^5319 ≤ (44396601495993/100000000000000 : ℝ)^4295
        have hw : |(1297720143/2500000000 : ℝ)|=(1297720143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s0_4 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-166545371/1250000000 : ℝ)*x 0 + (2490123201/5000000000 : ℝ)*x 1 + (5675334283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166545371/1250000000 : ℝ)^5319 ≤ (8239823242299/100000000000000 : ℝ)^4295 := by
    have hnat : (166545371 : ℕ)^5319*100000000000000^4295 ≤ 8239823242299^4295*1250000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166545371 1250000000 8239823242299 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2490123201/5000000000 : ℝ)^5319 ≤ (42176482132421/100000000000000 : ℝ)^4295 := by
    have hnat : (2490123201 : ℕ)^5319*100000000000000^4295 ≤ 42176482132421^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490123201 5000000000 42176482132421 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5675334283/10000000000 : ℝ)^5319 ≤ (12395923650163/25000000000000 : ℝ)^4295 := by
    have hnat : (5675334283 : ℕ)^5319*25000000000000^4295 ≤ 12395923650163^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675334283 10000000000 12395923650163 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-166545371/1250000000 : ℝ), (2490123201/5000000000 : ℝ), (5675334283/10000000000 : ℝ)] ![(8239823242299/100000000000000 : ℝ), (42176482132421/100000000000000 : ℝ), (12395923650163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-166545371/1250000000 : ℝ)|^5319 ≤ (8239823242299/100000000000000 : ℝ)^4295
        have hw : |(-166545371/1250000000 : ℝ)|=(166545371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2490123201/5000000000 : ℝ)|^5319 ≤ (42176482132421/100000000000000 : ℝ)^4295
        have hw : |(2490123201/5000000000 : ℝ)|=(2490123201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5675334283/10000000000 : ℝ)|^5319 ≤ (12395923650163/25000000000000 : ℝ)^4295
        have hw : |(5675334283/10000000000 : ℝ)|=(5675334283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s0_5 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301189199/2500000000 : ℝ)*x 0 + (-506788889/5000000000 : ℝ)*x 1 + (5675333863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301189199/2500000000 : ℝ)^5319 ≤ (44543624432659/100000000000000 : ℝ)^4295 := by
    have hnat : (1301189199 : ℕ)^5319*100000000000000^4295 ≤ 44543624432659^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301189199 2500000000 44543624432659 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506788889/5000000000 : ℝ)^5319 ≤ (2936342744253/50000000000000 : ℝ)^4295 := by
    have hnat : (506788889 : ℕ)^5319*50000000000000^4295 ≤ 2936342744253^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506788889 5000000000 2936342744253 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5675333863/10000000000 : ℝ)^5319 ≤ (12395922514097/25000000000000 : ℝ)^4295 := by
    have hnat : (5675333863 : ℕ)^5319*25000000000000^4295 ≤ 12395922514097^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675333863 10000000000 12395922514097 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301189199/2500000000 : ℝ), (-506788889/5000000000 : ℝ), (5675333863/10000000000 : ℝ)] ![(44543624432659/100000000000000 : ℝ), (2936342744253/50000000000000 : ℝ), (12395922514097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301189199/2500000000 : ℝ)|^5319 ≤ (44543624432659/100000000000000 : ℝ)^4295
        have hw : |(1301189199/2500000000 : ℝ)|=(1301189199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-506788889/5000000000 : ℝ)|^5319 ≤ (2936342744253/50000000000000 : ℝ)^4295
        have hw : |(-506788889/5000000000 : ℝ)|=(506788889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5675333863/10000000000 : ℝ)|^5319 ≤ (12395922514097/25000000000000 : ℝ)^4295
        have hw : |(5675333863/10000000000 : ℝ)|=(5675333863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s0_6 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5204756531/10000000000 : ℝ)*x 0 + (1418833543/2500000000 : ℝ)*x 1 + (-202715541/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5204756531/10000000000 : ℝ)^5319 ≤ (5567952703001/12500000000000 : ℝ)^4295 := by
    have hnat : (5204756531 : ℕ)^5319*12500000000000^4295 ≤ 5567952703001^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204756531 10000000000 5567952703001 12500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1418833543/2500000000 : ℝ)^5319 ≤ (12395923349917/25000000000000 : ℝ)^4295 := by
    have hnat : (1418833543 : ℕ)^5319*25000000000000^4295 ≤ 12395923349917^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418833543 2500000000 12395923349917 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202715541/2000000000 : ℝ)^5319 ≤ (5872684964701/100000000000000 : ℝ)^4295 := by
    have hnat : (202715541 : ℕ)^5319*100000000000000^4295 ≤ 5872684964701^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202715541 2000000000 5872684964701 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5204756531/10000000000 : ℝ), (1418833543/2500000000 : ℝ), (-202715541/2000000000 : ℝ)] ![(5567952703001/12500000000000 : ℝ), (12395923349917/25000000000000 : ℝ), (5872684964701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5204756531/10000000000 : ℝ)|^5319 ≤ (5567952703001/12500000000000 : ℝ)^4295
        have hw : |(5204756531/10000000000 : ℝ)|=(5204756531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1418833543/2500000000 : ℝ)|^5319 ≤ (12395923349917/25000000000000 : ℝ)^4295
        have hw : |(1418833543/2500000000 : ℝ)|=(1418833543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-202715541/2000000000 : ℝ)|^5319 ≤ (5872684964701/100000000000000 : ℝ)^4295
        have hw : |(-202715541/2000000000 : ℝ)|=(202715541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s0_7 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (808533323/2000000000 : ℝ)*x 0 + (5138636383/10000000000 : ℝ)*x 1 + (311421859/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808533323/2000000000 : ℝ)^5319 ≤ (32575490846123/100000000000000 : ℝ)^4295 := by
    have hnat : (808533323 : ℕ)^5319*100000000000000^4295 ≤ 32575490846123^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808533323 2000000000 32575490846123 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138636383/10000000000 : ℝ)^5319 ≤ (43843899807169/100000000000000 : ℝ)^4295 := by
    have hnat : (5138636383 : ℕ)^5319*100000000000000^4295 ≤ 43843899807169^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138636383 10000000000 43843899807169 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311421859/1000000000 : ℝ)^5319 ≤ (23580609332637/100000000000000 : ℝ)^4295 := by
    have hnat : (311421859 : ℕ)^5319*100000000000000^4295 ≤ 23580609332637^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311421859 1000000000 23580609332637 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(808533323/2000000000 : ℝ), (5138636383/10000000000 : ℝ), (311421859/1000000000 : ℝ)] ![(32575490846123/100000000000000 : ℝ), (43843899807169/100000000000000 : ℝ), (23580609332637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(808533323/2000000000 : ℝ)|^5319 ≤ (32575490846123/100000000000000 : ℝ)^4295
        have hw : |(808533323/2000000000 : ℝ)|=(808533323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138636383/10000000000 : ℝ)|^5319 ≤ (43843899807169/100000000000000 : ℝ)^4295
        have hw : |(5138636383/10000000000 : ℝ)|=(5138636383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311421859/1000000000 : ℝ)|^5319 ≤ (23580609332637/100000000000000 : ℝ)^4295
        have hw : |(311421859/1000000000 : ℝ)|=(311421859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1712_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6109/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21839/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5311/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5311 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5311*1^1024 ≤ 0^1024*1^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5311/1024 : ℝ) ≤ (43156361532178627/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5311 ≤ (43156361532178627/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5311*5000000000000000000^1024 ≤ 43156361532178627^1024*5^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 43156361532178627 5000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (43156361532178627/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5311 := by
      have hnat : (1 : ℕ)^1024*1^5311 ≤ 1^5311*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5043156361532178627/5000000000000000000 : ℝ) ≤ (2504146014347649/2500000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (5043156361532178627/5000000000000000000 : ℝ)^1024 ≤ (2504146014347649/2500000000000000 : ℝ)^5311 := by
      have hnat : (5043156361532178627 : ℕ)^1024*2500000000000000^5311 ≤ 2504146014347649^5311*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5043156361532178627 5000000000000000000 2504146014347649 2500000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504146014347649/2500000000000000 : ℝ)) (X := (5043156361532178627/5000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2543156361532178627/2500000000000000000 : ℝ) ≤ (1254146014347649/1250000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (2543156361532178627/2500000000000000000 : ℝ)^1024 ≤ (1254146014347649/1250000000000000 : ℝ)^5311 := by
      have hnat : (2543156361532178627 : ℕ)^1024*1250000000000000^5311 ≤ 1254146014347649^5311*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2543156361532178627 2500000000000000000 1254146014347649 1250000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254146014347649/1250000000000000 : ℝ)) (X := (2543156361532178627/2500000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4146014347649/1000000000000000 : ℝ)*(0 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4146014347649/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43156361532178627/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4146014347649/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5311/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4146014347649/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2504146014347649/2500000000000000 : ℝ) by norm_num, show 1+(43156361532178627/5000000000000000000 : ℝ)+(0 : ℝ)=(5043156361532178627/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43156361532178627/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4146014347649/1000000000000000 : ℝ)*(2/5 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4146014347649/1000000000000000 : ℝ)*(2/5 : ℝ)=(1254146014347649/1250000000000000 : ℝ) by norm_num, show 1+2*(43156361532178627/5000000000000000000 : ℝ)=(2543156361532178627/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4146014347649/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4146014347649/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4146014347649/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4146014347649/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4146014347649/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4146014347649/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1330723677/10000000000 : ℝ)*X 0 0+(5693867559/10000000000 : ℝ)*X 0 1+(310144283/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5402881179/10000000000 : ℝ)*X 1 0+(-69064153/400000000 : ℝ)*X 1 1+(2481154177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((675360139/1250000000 : ℝ)*X 2 0+(4962308431/10000000000 : ℝ)*X 2 1+(-863301907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4037895133/10000000000 : ℝ)*X 0 0+(122409701/400000000 : ℝ)*X 0 1+(1297720143/2500000000 : ℝ)*X 0 2+(4037895133/10000000000 : ℝ)*X 1 0+(122409701/400000000 : ℝ)*X 1 1+(1297720143/2500000000 : ℝ)*X 1 2+(4037895133/10000000000 : ℝ)*X 2 0+(122409701/400000000 : ℝ)*X 2 1+(1297720143/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-166545371/1250000000 : ℝ)*X 0 0+(2490123201/5000000000 : ℝ)*X 0 1+(5675334283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1301189199/2500000000 : ℝ)*X 1 0+(-506788889/5000000000 : ℝ)*X 1 1+(5675333863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5204756531/10000000000 : ℝ)*X 2 0+(1418833543/2500000000 : ℝ)*X 2 1+(-202715541/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((808533323/2000000000 : ℝ)*X 0 0+(5138636383/10000000000 : ℝ)*X 0 1+(311421859/1000000000 : ℝ)*X 0 2+(808533323/2000000000 : ℝ)*X 1 0+(5138636383/10000000000 : ℝ)*X 1 1+(311421859/1000000000 : ℝ)*X 1 2+(808533323/2000000000 : ℝ)*X 2 0+(5138636383/10000000000 : ℝ)*X 2 1+(311421859/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (427512824326715930547/195312500000000000000000000 : ℝ) := by norm_num
    linear_combination (32950217/50000000000000 : ℝ)*(base1) + (44354107/12500000000000 : ℝ)*(base19) + (337881649/100000000000000 : ℝ)*(base23) + (38581287/100000000000000 : ℝ)*(upper3) + (39519327/100000000000000 : ℝ)*(upper5) + (7173006492767/781250000000 : ℝ)*(major0) + (7173006492767/781250000000 : ℝ)*(major1) + (7173006492767/781250000000 : ℝ)*(major2) + (273388963544907/20000000000000 : ℝ)*(sp0) + (683472785331903/50000000000000 : ℝ)*(sp1) + (341736396903753/25000000000000 : ℝ)*(sp2) + (469343284206459/100000000000000 : ℝ)*(sp3) + (14670907/1250000000000 : ℝ)*(sp4) + (156791301/50000000000000 : ℝ)*(sp7) + (93868732737899/20000000000000 : ℝ)*(f.failure) + (1366945925496661/100000000000000 : ℝ)*(f.sum) + (5001830621493/1562500000000000000000000000 : ℝ)*base66 + (8616157849809/1562500000000000000000000000 : ℝ)*base68 + (1927788270217/781250000000000000000000000 : ℝ)*base70 + (36488368277743/3125000000000000000000000000 : ℝ)*base72 + (9917400583611/3125000000000000000000000000 : ℝ)*base74 + (2331463935523/195312500000000000000000000 : ℝ)*base76 + (28640074746493/3125000000000000000000000000 : ℝ)*base78 + (20759743783993/3125000000000000000000000000 : ℝ)*base80 + (821070030421/195312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1291807/250000000000000000000 : ℝ)*base89 + (1291807/250000000000000000000 : ℝ)*base91 + (1291807/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6662298879543707787/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1961060663/100000000000000 : ℝ)*(base19) + (2073572487/100000000000000 : ℝ)*(base23) + (86214369/100000000000000 : ℝ)*(upper2) + (299400153/100000000000000 : ℝ)*(upper3) + (154011567/50000000000000 : ℝ)*(upper5) + (966317807281409/100000000000000 : ℝ)*(major0) + (966317807281409/100000000000000 : ℝ)*(major1) + (966317807281409/100000000000000 : ℝ)*(major2) + (3423924667/50000000000000 : ℝ)*(sp1) + (73762929/1000000000000 : ℝ)*(sp2) + (719333165802919/50000000000000 : ℝ)*(sp4) + (1438657522695841/100000000000000 : ℝ)*(sp5) + (1438656881740451/100000000000000 : ℝ)*(sp6) + (493969060880347/100000000000000 : ℝ)*(sp7) + (493969060880347/100000000000000 : ℝ)*(f.failure) + (719333165802919/50000000000000 : ℝ)*(f.sum) + (202901889507441/50000000000000000000000000000 : ℝ)*base65 + (574481322857441/100000000000000000000000000000 : ℝ)*base67 + (680702187842559/100000000000000000000000000000 : ℝ)*base70 + (287811262142559/100000000000000000000000000000 : ℝ)*base72 + (197780247907441/50000000000000000000000000000 : ℝ)*base73 + (248077774342559/100000000000000000000000000000 : ℝ)*base76 + (12501731957441/100000000000000000000000000000 : ℝ)*base77 + (226392336742559/100000000000000000000000000000 : ℝ)*base80 + (124046958192559/50000000000000000000000000000 : ℝ)*base82 + (1506129/1250000000000000000000 : ℝ)*base90 + (1506129/1250000000000000000000 : ℝ)*base92 + (1506129/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1712_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6109/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21839/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1712_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1712_s1_0 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1401409299/10000000000 : ℝ)*x 0 + (5482978823/10000000000 : ℝ)*x 1 + (5126640829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1401409299/10000000000 : ℝ)^5319 ≤ (4385930922273/50000000000000 : ℝ)^4295 := by
    have hnat : (1401409299 : ℕ)^5319*50000000000000^4295 ≤ 4385930922273^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401409299 10000000000 4385930922273 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482978823/10000000000 : ℝ)^5319 ≤ (11877738293111/25000000000000 : ℝ)^4295 := by
    have hnat : (5482978823 : ℕ)^5319*25000000000000^4295 ≤ 11877738293111^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482978823 10000000000 11877738293111 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5126640829/10000000000 : ℝ)^5319 ≤ (2732324060473/6250000000000 : ℝ)^4295 := by
    have hnat : (5126640829 : ℕ)^5319*6250000000000^4295 ≤ 2732324060473^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126640829 10000000000 2732324060473 6250000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1401409299/10000000000 : ℝ), (5482978823/10000000000 : ℝ), (5126640829/10000000000 : ℝ)] ![(4385930922273/50000000000000 : ℝ), (11877738293111/25000000000000 : ℝ), (2732324060473/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1401409299/10000000000 : ℝ)|^5319 ≤ (4385930922273/50000000000000 : ℝ)^4295
        have hw : |(-1401409299/10000000000 : ℝ)|=(1401409299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482978823/10000000000 : ℝ)|^5319 ≤ (11877738293111/25000000000000 : ℝ)^4295
        have hw : |(5482978823/10000000000 : ℝ)|=(5482978823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5126640829/10000000000 : ℝ)|^5319 ≤ (2732324060473/6250000000000 : ℝ)^4295
        have hw : |(5126640829/10000000000 : ℝ)|=(5126640829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s1_1 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336676843/2500000000 : ℝ)*x 0 + (-1586670637/10000000000 : ℝ)*x 1 + (2563319917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336676843/2500000000 : ℝ)^5319 ≤ (46052971622201/100000000000000 : ℝ)^4295 := by
    have hnat : (1336676843 : ℕ)^5319*100000000000000^4295 ≤ 46052971622201^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336676843 2500000000 46052971622201 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1586670637/10000000000 : ℝ)^5319 ≤ (2557463475931/25000000000000 : ℝ)^4295 := by
    have hnat : (1586670637 : ℕ)^5319*25000000000000^4295 ≤ 2557463475931^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586670637 10000000000 2557463475931 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2563319917/5000000000 : ℝ)^5319 ≤ (43717174459831/100000000000000 : ℝ)^4295 := by
    have hnat : (2563319917 : ℕ)^5319*100000000000000^4295 ≤ 43717174459831^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563319917 5000000000 43717174459831 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336676843/2500000000 : ℝ), (-1586670637/10000000000 : ℝ), (2563319917/5000000000 : ℝ)] ![(46052971622201/100000000000000 : ℝ), (2557463475931/25000000000000 : ℝ), (43717174459831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336676843/2500000000 : ℝ)|^5319 ≤ (46052971622201/100000000000000 : ℝ)^4295
        have hw : |(1336676843/2500000000 : ℝ)|=(1336676843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1586670637/10000000000 : ℝ)|^5319 ≤ (2557463475931/25000000000000 : ℝ)^4295
        have hw : |(-1586670637/10000000000 : ℝ)|=(1586670637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2563319917/5000000000 : ℝ)|^5319 ≤ (43717174459831/100000000000000 : ℝ)^4295
        have hw : |(2563319917/5000000000 : ℝ)|=(2563319917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s1_2 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346705999/10000000000 : ℝ)*x 0 + (5126641/10000000 : ℝ)*x 1 + (-1586670929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346705999/10000000000 : ℝ)^5319 ≤ (46052956976553/100000000000000 : ℝ)^4295 := by
    have hnat : (5346705999 : ℕ)^5319*100000000000000^4295 ≤ 46052956976553^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346705999 10000000000 46052956976553 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126641/10000000 : ℝ)^5319 ≤ (2185859338671/5000000000000 : ℝ)^4295 := by
    have hnat : (5126641 : ℕ)^5319*5000000000000^4295 ≤ 2185859338671^4295*10000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126641 10000000 2185859338671 5000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586670929/10000000000 : ℝ)^5319 ≤ (1278732029401/12500000000000 : ℝ)^4295 := by
    have hnat : (1586670929 : ℕ)^5319*12500000000000^4295 ≤ 1278732029401^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586670929 10000000000 1278732029401 12500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346705999/10000000000 : ℝ), (5126641/10000000 : ℝ), (-1586670929/10000000000 : ℝ)] ![(46052956976553/100000000000000 : ℝ), (2185859338671/5000000000000 : ℝ), (1278732029401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346705999/10000000000 : ℝ)|^5319 ≤ (46052956976553/100000000000000 : ℝ)^4295
        have hw : |(5346705999/10000000000 : ℝ)|=(5346705999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126641/10000000 : ℝ)|^5319 ≤ (2185859338671/5000000000000 : ℝ)^4295
        have hw : |(5126641/10000000 : ℝ)|=(5126641/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1586670929/10000000000 : ℝ)|^5319 ≤ (1278732029401/12500000000000 : ℝ)^4295
        have hw : |(-1586670929/10000000000 : ℝ)|=(1586670929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s1_3 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4099464841/10000000000 : ℝ)*x 0 + (1800604611/5000000000 : ℝ)*x 1 + (9278057/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4099464841/10000000000 : ℝ)^5319 ≤ (6628645994651/20000000000000 : ℝ)^4295 := by
    have hnat : (4099464841 : ℕ)^5319*20000000000000^4295 ≤ 6628645994651^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4099464841 10000000000 6628645994651 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1800604611/5000000000 : ℝ)^5319 ≤ (28229176269027/100000000000000 : ℝ)^4295 := by
    have hnat : (1800604611 : ℕ)^5319*100000000000000^4295 ≤ 28229176269027^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800604611 5000000000 28229176269027 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9278057/20000000 : ℝ)^5319 ≤ (38627593746529/100000000000000 : ℝ)^4295 := by
    have hnat : (9278057 : ℕ)^5319*100000000000000^4295 ≤ 38627593746529^4295*20000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9278057 20000000 38627593746529 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4099464841/10000000000 : ℝ), (1800604611/5000000000 : ℝ), (9278057/20000000 : ℝ)] ![(6628645994651/20000000000000 : ℝ), (28229176269027/100000000000000 : ℝ), (38627593746529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4099464841/10000000000 : ℝ)|^5319 ≤ (6628645994651/20000000000000 : ℝ)^4295
        have hw : |(4099464841/10000000000 : ℝ)|=(4099464841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1800604611/5000000000 : ℝ)|^5319 ≤ (28229176269027/100000000000000 : ℝ)^4295
        have hw : |(1800604611/5000000000 : ℝ)|=(1800604611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9278057/20000000 : ℝ)|^5319 ≤ (38627593746529/100000000000000 : ℝ)^4295
        have hw : |(9278057/20000000 : ℝ)|=(9278057/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s1_4 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-140159829/1000000000 : ℝ)*x 0 + (1282725809/2500000000 : ℝ)*x 1 + (5478646817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140159829/1000000000 : ℝ)^5319 ≤ (8773326858343/100000000000000 : ℝ)^4295 := by
    have hnat : (140159829 : ℕ)^5319*100000000000000^4295 ≤ 8773326858343^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140159829 1000000000 8773326858343 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282725809/2500000000 : ℝ)^5319 ≤ (8752440549391/20000000000000 : ℝ)^4295 := by
    have hnat : (1282725809 : ℕ)^5319*20000000000000^4295 ≤ 8752440549391^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282725809 2500000000 8752440549391 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478646817/10000000000 : ℝ)^5319 ≤ (47464470388319/100000000000000 : ℝ)^4295 := by
    have hnat : (5478646817 : ℕ)^5319*100000000000000^4295 ≤ 47464470388319^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478646817 10000000000 47464470388319 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-140159829/1000000000 : ℝ), (1282725809/2500000000 : ℝ), (5478646817/10000000000 : ℝ)] ![(8773326858343/100000000000000 : ℝ), (8752440549391/20000000000000 : ℝ), (47464470388319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-140159829/1000000000 : ℝ)|^5319 ≤ (8773326858343/100000000000000 : ℝ)^4295
        have hw : |(-140159829/1000000000 : ℝ)|=(140159829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282725809/2500000000 : ℝ)|^5319 ≤ (8752440549391/20000000000000 : ℝ)^4295
        have hw : |(1282725809/2500000000 : ℝ)|=(1282725809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478646817/10000000000 : ℝ)|^5319 ≤ (47464470388319/100000000000000 : ℝ)^4295
        have hw : |(5478646817/10000000000 : ℝ)|=(5478646817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s1_5 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251286461/10000000000 : ℝ)*x 0 + (-1234664091/10000000000 : ℝ)*x 1 + (2739323241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251286461/10000000000 : ℝ)^5319 ≤ (4503730200331/10000000000000 : ℝ)^4295 := by
    have hnat : (5251286461 : ℕ)^5319*10000000000000^4295 ≤ 4503730200331^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251286461 10000000000 4503730200331 10000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1234664091/10000000000 : ℝ)^5319 ≤ (1499646236741/20000000000000 : ℝ)^4295 := by
    have hnat : (1234664091 : ℕ)^5319*20000000000000^4295 ≤ 1499646236741^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234664091 10000000000 1499646236741 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739323241/5000000000 : ℝ)^5319 ≤ (296652917463/625000000000 : ℝ)^4295 := by
    have hnat : (2739323241 : ℕ)^5319*625000000000^4295 ≤ 296652917463^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739323241 5000000000 296652917463 625000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251286461/10000000000 : ℝ), (-1234664091/10000000000 : ℝ), (2739323241/5000000000 : ℝ)] ![(4503730200331/10000000000000 : ℝ), (1499646236741/20000000000000 : ℝ), (296652917463/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251286461/10000000000 : ℝ)|^5319 ≤ (4503730200331/10000000000000 : ℝ)^4295
        have hw : |(5251286461/10000000000 : ℝ)|=(5251286461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1234664091/10000000000 : ℝ)|^5319 ≤ (1499646236741/20000000000000 : ℝ)^4295
        have hw : |(-1234664091/10000000000 : ℝ)|=(1234664091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739323241/5000000000 : ℝ)|^5319 ≤ (296652917463/625000000000 : ℝ)^4295
        have hw : |(2739323241/5000000000 : ℝ)|=(2739323241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s1_6 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262564333/500000000 : ℝ)*x 0 + (1369661533/2500000000 : ℝ)*x 1 + (-123466431/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262564333/500000000 : ℝ)^5319 ≤ (703707876827/1562500000000 : ℝ)^4295 := by
    have hnat : (262564333 : ℕ)^5319*1562500000000^4295 ≤ 703707876827^4295*500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262564333 500000000 703707876827 1562500000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369661533/2500000000 : ℝ)^5319 ≤ (9492892607781/20000000000000 : ℝ)^4295 := by
    have hnat : (1369661533 : ℕ)^5319*20000000000000^4295 ≤ 9492892607781^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369661533 2500000000 9492892607781 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123466431/1000000000 : ℝ)^5319 ≤ (7498232830809/100000000000000 : ℝ)^4295 := by
    have hnat : (123466431 : ℕ)^5319*100000000000000^4295 ≤ 7498232830809^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123466431 1000000000 7498232830809 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262564333/500000000 : ℝ), (1369661533/2500000000 : ℝ), (-123466431/1000000000 : ℝ)] ![(703707876827/1562500000000 : ℝ), (9492892607781/20000000000000 : ℝ), (7498232830809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262564333/500000000 : ℝ)|^5319 ≤ (703707876827/1562500000000 : ℝ)^4295
        have hw : |(262564333/500000000 : ℝ)|=(262564333/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369661533/2500000000 : ℝ)|^5319 ≤ (9492892607781/20000000000000 : ℝ)^4295
        have hw : |(1369661533/2500000000 : ℝ)|=(1369661533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-123466431/1000000000 : ℝ)|^5319 ≤ (7498232830809/100000000000000 : ℝ)^4295
        have hw : |(-123466431/1000000000 : ℝ)|=(123466431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s1_7 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (512501489/1250000000 : ℝ)*x 0 + (4626613091/10000000000 : ℝ)*x 1 + (361382359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512501489/1250000000 : ℝ)^5319 ≤ (33148707507339/100000000000000 : ℝ)^4295 := by
    have hnat : (512501489 : ℕ)^5319*100000000000000^4295 ≤ 33148707507339^4295*1250000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512501489 1250000000 33148707507339 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4626613091/10000000000 : ℝ)^5319 ≤ (38499608533551/100000000000000 : ℝ)^4295 := by
    have hnat : (4626613091 : ℕ)^5319*100000000000000^4295 ≤ 38499608533551^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4626613091 10000000000 38499608533551 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361382359/1000000000 : ℝ)^5319 ≤ (3543960493717/12500000000000 : ℝ)^4295 := by
    have hnat : (361382359 : ℕ)^5319*12500000000000^4295 ≤ 3543960493717^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361382359 1000000000 3543960493717 12500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(512501489/1250000000 : ℝ), (4626613091/10000000000 : ℝ), (361382359/1000000000 : ℝ)] ![(33148707507339/100000000000000 : ℝ), (38499608533551/100000000000000 : ℝ), (3543960493717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(512501489/1250000000 : ℝ)|^5319 ≤ (33148707507339/100000000000000 : ℝ)^4295
        have hw : |(512501489/1250000000 : ℝ)|=(512501489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4626613091/10000000000 : ℝ)|^5319 ≤ (38499608533551/100000000000000 : ℝ)^4295
        have hw : |(4626613091/10000000000 : ℝ)|=(4626613091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(361382359/1000000000 : ℝ)|^5319 ≤ (3543960493717/12500000000000 : ℝ)^4295
        have hw : |(361382359/1000000000 : ℝ)|=(361382359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1712_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9767/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8689/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6109/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6109/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6109/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6109/100000 : ℝ) ^ (5311/1024 : ℝ) ≤ (12628320887403/25000000000000000000 : ℝ) := by
    have hpowers : (6109/100000 : ℝ)^5311 ≤ (12628320887403/25000000000000000000 : ℝ)^1024 := by
      have hnat : (6109 : ℕ)^5311*25000000000000000000^1024 ≤ 12628320887403^1024*100000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6109 100000 12628320887403 25000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6109/100000 : ℝ)) (X := (12628320887403/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21839/100000 : ℝ) ^ (5311/1024 : ℝ) ≤ (7480750288224671/20000000000000000000 : ℝ) := by
    have hpowers : (21839/100000 : ℝ)^5311 ≤ (7480750288224671/20000000000000000000 : ℝ)^1024 := by
      have hnat : (21839 : ℕ)^5311*20000000000000000000^1024 ≤ 7480750288224671^1024*100000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21839 100000 7480750288224671 20000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21839/100000 : ℝ)) (X := (7480750288224671/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500012628320887403/12500000000000000000 : ℝ) ≤ (10000001947865987/10000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (12500012628320887403/12500000000000000000 : ℝ)^1024 ≤ (10000001947865987/10000000000000000 : ℝ)^5311 := by
      have hnat : (12500012628320887403 : ℕ)^1024*10000000000000000^5311 ≤ 10000001947865987^5311*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500012628320887403 12500000000000000000 10000001947865987 10000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001947865987/10000000000000000 : ℝ)) (X := (12500012628320887403/12500000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037454264724672967/100000000000000000000 : ℝ) ≤ (5000361018365341/5000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (100037454264724672967/100000000000000000000 : ℝ)^1024 ≤ (5000361018365341/5000000000000000 : ℝ)^5311 := by
      have hnat : (100037454264724672967 : ℕ)^1024*5000000000000000^5311 ≤ 5000361018365341^5311*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037454264724672967 100000000000000000000 5000361018365341 5000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000361018365341/5000000000000000 : ℝ)) (X := (100037454264724672967/100000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007480750288224671/10000000000000000000 : ℝ) ≤ (10001442125595377/10000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (10007480750288224671/10000000000000000000 : ℝ)^1024 ≤ (10001442125595377/10000000000000000 : ℝ)^5311 := by
      have hnat : (10007480750288224671 : ℕ)^1024*10000000000000000^5311 ≤ 10001442125595377^5311*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007480750288224671 10000000000000000000 10001442125595377 10000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001442125595377/10000000000000000 : ℝ)) (X := (10007480750288224671/10000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12628320887403/25000000000000000000 : ℝ) ≤ ((39322808148545783/39325000000000000 : ℝ)+2*(144017772939/314600000000000 : ℝ)*(6109/100000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (39322808148545783/39325000000000000 : ℝ)+2*(144017772939/314600000000000 : ℝ)*(6109/100000 : ℝ)=(10000001947865987/10000000000000000 : ℝ) by norm_num, show 1+2*(12628320887403/25000000000000000000 : ℝ)=(12500012628320887403/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7480750288224671/20000000000000000000 : ℝ)+(12628320887403/25000000000000000000 : ℝ) ≤ ((39322808148545783/39325000000000000 : ℝ)+(144017772939/314600000000000 : ℝ)*((21839/100000 : ℝ)+(6109/100000 : ℝ)))^(5311/1024 : ℝ) := by
    rw [show (39322808148545783/39325000000000000 : ℝ)+(144017772939/314600000000000 : ℝ)*((21839/100000 : ℝ)+(6109/100000 : ℝ))=(5000361018365341/5000000000000000 : ℝ) by norm_num, show 1+(7480750288224671/20000000000000000000 : ℝ)+(12628320887403/25000000000000000000 : ℝ)=(100037454264724672967/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7480750288224671/20000000000000000000 : ℝ) ≤ ((39322808148545783/39325000000000000 : ℝ)+2*(144017772939/314600000000000 : ℝ)*(21839/100000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (39322808148545783/39325000000000000 : ℝ)+2*(144017772939/314600000000000 : ℝ)*(21839/100000 : ℝ)=(10001442125595377/10000000000000000 : ℝ) by norm_num, show 1+2*(7480750288224671/20000000000000000000 : ℝ)=(10007480750288224671/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39322808148545783/39325000000000000 : ℝ)*(X 1 0+X 2 0)+(144017772939/314600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (6109/100000 : ℝ)) (hi := (21839/100000 : ℝ)) (c := (39322808148545783/39325000000000000 : ℝ)) (alpha := (144017772939/314600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39322808148545783/39325000000000000 : ℝ)*(X 0 1+X 2 1)+(144017772939/314600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (6109/100000 : ℝ)) (hi := (21839/100000 : ℝ)) (c := (39322808148545783/39325000000000000 : ℝ)) (alpha := (144017772939/314600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39322808148545783/39325000000000000 : ℝ)*(X 0 2+X 1 2)+(144017772939/314600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (6109/100000 : ℝ)) (hi := (21839/100000 : ℝ)) (c := (39322808148545783/39325000000000000 : ℝ)) (alpha := (144017772939/314600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1401409299/10000000000 : ℝ)*X 0 0+(5482978823/10000000000 : ℝ)*X 0 1+(5126640829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336676843/2500000000 : ℝ)*X 1 0+(-1586670637/10000000000 : ℝ)*X 1 1+(2563319917/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346705999/10000000000 : ℝ)*X 2 0+(5126641/10000000 : ℝ)*X 2 1+(-1586670929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4099464841/10000000000 : ℝ)*X 0 0+(1800604611/5000000000 : ℝ)*X 0 1+(9278057/20000000 : ℝ)*X 0 2+(4099464841/10000000000 : ℝ)*X 1 0+(1800604611/5000000000 : ℝ)*X 1 1+(9278057/20000000 : ℝ)*X 1 2+(4099464841/10000000000 : ℝ)*X 2 0+(1800604611/5000000000 : ℝ)*X 2 1+(9278057/20000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-140159829/1000000000 : ℝ)*X 0 0+(1282725809/2500000000 : ℝ)*X 0 1+(5478646817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251286461/10000000000 : ℝ)*X 1 0+(-1234664091/10000000000 : ℝ)*X 1 1+(2739323241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262564333/500000000 : ℝ)*X 2 0+(1369661533/2500000000 : ℝ)*X 2 1+(-123466431/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((512501489/1250000000 : ℝ)*X 0 0+(4626613091/10000000000 : ℝ)*X 0 1+(361382359/1000000000 : ℝ)*X 0 2+(512501489/1250000000 : ℝ)*X 1 0+(4626613091/10000000000 : ℝ)*X 1 1+(361382359/1000000000 : ℝ)*X 1 2+(512501489/1250000000 : ℝ)*X 2 0+(4626613091/10000000000 : ℝ)*X 2 1+(361382359/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94947248016133117315569/9453125000000000000000000000 : ℝ) := by norm_num
    linear_combination (454109087/50000000000000 : ℝ)*(base19) + (384786441/100000000000000 : ℝ)*(base23) + (14151999/25000000000000 : ℝ)*(lower2) + (25410833/20000000000000 : ℝ)*(upper3) + (162053697/100000000000000 : ℝ)*(lower4) + (942473052387263/50000000000000 : ℝ)*(major0) + (942473052387263/50000000000000 : ℝ)*(major1) + (942473052387263/50000000000000 : ℝ)*(major2) + (280633097655843/10000000000000 : ℝ)*(sp0) + (350791387529071/12500000000000 : ℝ)*(sp1) + (1403165811832151/50000000000000 : ℝ)*(sp2) + (38542382453979/4000000000000 : ℝ)*(sp3) + (128986539/12500000000000 : ℝ)*(sp4) + (152474309/50000000000000 : ℝ)*(sp7) + (963559866298093/100000000000000 : ℝ)*(f.failure) + (1403166004225371/50000000000000 : ℝ)*(f.sum) + (10367041170377/1966250000000000000000000000 : ℝ)*base66 + (6371111200322027/983125000000000000000000000000 : ℝ)*base67 + (776167191739527/983125000000000000000000000000 : ℝ)*base69 + (1298461330966951/491562500000000000000000000000 : ℝ)*base71 + (9200050332323/7865000000000000000000000000 : ℝ)*base74 + (771050676943277/983125000000000000000000000000 : ℝ)*base75 + (249723959179413/245781250000000000000000000000 : ℝ)*base77 + (425362167111723/983125000000000000000000000000 : ℝ)*base80 + (34946510779173/7865000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (766951/1250000000000000000000 : ℝ)*base90 + (766951/1250000000000000000000 : ℝ)*base92 + (766951/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3903705546090579171273/357500000000000000000000000 : ℝ) := by norm_num
    linear_combination (559643059/25000000000000 : ℝ)*(base19) + (2527162009/100000000000000 : ℝ)*(base23) + (26145269/25000000000000 : ℝ)*(upper2) + (151916129/50000000000000 : ℝ)*(upper3) + (93655881/25000000000000 : ℝ)*(upper5) + (120720437127081/6250000000000 : ℝ)*(major0) + (120720437127081/6250000000000 : ℝ)*(major1) + (120720437127081/6250000000000 : ℝ)*(major2) + (17385183963/100000000000000 : ℝ)*(sp1) + (4077545129/25000000000000 : ℝ)*(sp2) + (718920553670169/25000000000000 : ℝ)*(sp4) + (718915647731119/25000000000000 : ℝ)*(sp5) + (2875663377338151/100000000000000 : ℝ)*(sp6) + (987371409404041/100000000000000 : ℝ)*(sp7) + (987371409404041/100000000000000 : ℝ)*(f.failure) + (718920553670169/25000000000000 : ℝ)*(f.sum) + (334970766591/89375000000000000000000000 : ℝ)*base66 + (681915538760653/89375000000000000000000000000 : ℝ)*base68 + (118833383199361/44687500000000000000000000000 : ℝ)*base69 + (9382558517/5455017089843750000000000 : ℝ)*base72 + (261777019663/44687500000000000000000000 : ℝ)*base74 + (160855813267493/22343750000000000000000000000 : ℝ)*base75 + (102835695897191/11171875000000000000000000000 : ℝ)*base78 + (125688544596847/89375000000000000000000000000 : ℝ)*base79 + (64992397891/22343750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8340613/1250000000000000000000 : ℝ)*base89 + (8340613/1250000000000000000000 : ℝ)*base91 + (8340613/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1712_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6109/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8689/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1712_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1712_s2_0 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-175594327/1250000000 : ℝ)*x 0 + (5469246751/10000000000 : ℝ)*x 1 + (5138131213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175594327/1250000000 : ℝ)^5319 ≤ (549862557079/6250000000000 : ℝ)^4295 := by
    have hnat : (175594327 : ℕ)^5319*6250000000000^4295 ≤ 549862557079^4295*1250000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175594327 1250000000 549862557079 6250000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469246751/10000000000 : ℝ)^5319 ≤ (9472727408203/20000000000000 : ℝ)^4295 := by
    have hnat : (5469246751 : ℕ)^5319*20000000000000^4295 ≤ 9472727408203^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469246751 10000000000 9472727408203 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138131213/10000000000 : ℝ)^5319 ≤ (1095964050709/2500000000000 : ℝ)^4295 := by
    have hnat : (5138131213 : ℕ)^5319*2500000000000^4295 ≤ 1095964050709^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138131213 10000000000 1095964050709 2500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-175594327/1250000000 : ℝ), (5469246751/10000000000 : ℝ), (5138131213/10000000000 : ℝ)] ![(549862557079/6250000000000 : ℝ), (9472727408203/20000000000000 : ℝ), (1095964050709/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-175594327/1250000000 : ℝ)|^5319 ≤ (549862557079/6250000000000 : ℝ)^4295
        have hw : |(-175594327/1250000000 : ℝ)|=(175594327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469246751/10000000000 : ℝ)|^5319 ≤ (9472727408203/20000000000000 : ℝ)^4295
        have hw : |(5469246751/10000000000 : ℝ)|=(5469246751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138131213/10000000000 : ℝ)|^5319 ≤ (1095964050709/2500000000000 : ℝ)^4295
        have hw : |(5138131213/10000000000 : ℝ)|=(5138131213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s2_1 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (333936427/625000000 : ℝ)*x 0 + (-197054421/1250000000 : ℝ)*x 1 + (5138131147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333936427/625000000 : ℝ)^5319 ≤ (23006622820353/50000000000000 : ℝ)^4295 := by
    have hnat : (333936427 : ℕ)^5319*50000000000000^4295 ≤ 23006622820353^4295*625000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333936427 625000000 23006622820353 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197054421/1250000000 : ℝ)^5319 ≤ (10148193018099/100000000000000 : ℝ)^4295 := by
    have hnat : (197054421 : ℕ)^5319*100000000000000^4295 ≤ 10148193018099^4295*1250000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197054421 1250000000 10148193018099 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138131147/10000000000 : ℝ)^5319 ≤ (2739910083187/6250000000000 : ℝ)^4295 := by
    have hnat : (5138131147 : ℕ)^5319*6250000000000^4295 ≤ 2739910083187^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138131147 10000000000 2739910083187 6250000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333936427/625000000 : ℝ), (-197054421/1250000000 : ℝ), (5138131147/10000000000 : ℝ)] ![(23006622820353/50000000000000 : ℝ), (10148193018099/100000000000000 : ℝ), (2739910083187/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333936427/625000000 : ℝ)|^5319 ≤ (23006622820353/50000000000000 : ℝ)^4295
        have hw : |(333936427/625000000 : ℝ)|=(333936427/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197054421/1250000000 : ℝ)|^5319 ≤ (10148193018099/100000000000000 : ℝ)^4295
        have hw : |(-197054421/1250000000 : ℝ)|=(197054421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138131147/10000000000 : ℝ)|^5319 ≤ (2739910083187/6250000000000 : ℝ)^4295
        have hw : |(5138131147/10000000000 : ℝ)|=(5138131147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s2_2 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5342982841/10000000000 : ℝ)*x 0 + (5138131179/10000000000 : ℝ)*x 1 + (-788217657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342982841/10000000000 : ℝ)^5319 ≤ (11503311434173/25000000000000 : ℝ)^4295 := by
    have hnat : (5342982841 : ℕ)^5319*25000000000000^4295 ≤ 11503311434173^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342982841 10000000000 11503311434173 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138131179/10000000000 : ℝ)^5319 ≤ (4383856166911/10000000000000 : ℝ)^4295 := by
    have hnat : (5138131179 : ℕ)^5319*10000000000000^4295 ≤ 4383856166911^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138131179 10000000000 4383856166911 10000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788217657/5000000000 : ℝ)^5319 ≤ (10148192587599/100000000000000 : ℝ)^4295 := by
    have hnat : (788217657 : ℕ)^5319*100000000000000^4295 ≤ 10148192587599^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788217657 5000000000 10148192587599 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342982841/10000000000 : ℝ), (5138131179/10000000000 : ℝ), (-788217657/5000000000 : ℝ)] ![(11503311434173/25000000000000 : ℝ), (4383856166911/10000000000000 : ℝ), (10148192587599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342982841/10000000000 : ℝ)|^5319 ≤ (11503311434173/25000000000000 : ℝ)^4295
        have hw : |(5342982841/10000000000 : ℝ)|=(5342982841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138131179/10000000000 : ℝ)|^5319 ≤ (4383856166911/10000000000000 : ℝ)^4295
        have hw : |(5138131179/10000000000 : ℝ)|=(5138131179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-788217657/5000000000 : ℝ)|^5319 ≤ (10148192587599/100000000000000 : ℝ)^4295
        have hw : |(-788217657/5000000000 : ℝ)|=(788217657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s2_3 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (820411641/2000000000 : ℝ)*x 0 + (3637709949/10000000000 : ℝ)*x 1 + (2301035759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (820411641/2000000000 : ℝ)^5319 ≤ (33169197507259/100000000000000 : ℝ)^4295 := by
    have hnat : (820411641 : ℕ)^5319*100000000000000^4295 ≤ 33169197507259^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820411641 2000000000 33169197507259 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3637709949/10000000000 : ℝ)^5319 ≤ (7145985419837/25000000000000 : ℝ)^4295 := by
    have hnat : (3637709949 : ℕ)^5319*25000000000000^4295 ≤ 7145985419837^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3637709949 10000000000 7145985419837 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2301035759/5000000000 : ℝ)^5319 ≤ (19123430399279/50000000000000 : ℝ)^4295 := by
    have hnat : (2301035759 : ℕ)^5319*50000000000000^4295 ≤ 19123430399279^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301035759 5000000000 19123430399279 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(820411641/2000000000 : ℝ), (3637709949/10000000000 : ℝ), (2301035759/5000000000 : ℝ)] ![(33169197507259/100000000000000 : ℝ), (7145985419837/25000000000000 : ℝ), (19123430399279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(820411641/2000000000 : ℝ)|^5319 ≤ (33169197507259/100000000000000 : ℝ)^4295
        have hw : |(820411641/2000000000 : ℝ)|=(820411641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3637709949/10000000000 : ℝ)|^5319 ≤ (7145985419837/25000000000000 : ℝ)^4295
        have hw : |(3637709949/10000000000 : ℝ)|=(3637709949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2301035759/5000000000 : ℝ)|^5319 ≤ (19123430399279/50000000000000 : ℝ)^4295
        have hw : |(2301035759/5000000000 : ℝ)|=(2301035759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s2_4 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-140490511/1000000000 : ℝ)*x 0 + (2570907041/5000000000 : ℝ)*x 1 + (273275443/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140490511/1000000000 : ℝ)^5319 ≤ (137483877607/1562500000000 : ℝ)^4295 := by
    have hnat : (140490511 : ℕ)^5319*1562500000000^4295 ≤ 137483877607^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140490511 1000000000 137483877607 1562500000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570907041/5000000000 : ℝ)^5319 ≤ (43877479202971/100000000000000 : ℝ)^4295 := by
    have hnat : (2570907041 : ℕ)^5319*100000000000000^4295 ≤ 43877479202971^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570907041 5000000000 43877479202971 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273275443/500000000 : ℝ)^5319 ≤ (23661776311077/50000000000000 : ℝ)^4295 := by
    have hnat : (273275443 : ℕ)^5319*50000000000000^4295 ≤ 23661776311077^4295*500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273275443 500000000 23661776311077 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-140490511/1000000000 : ℝ), (2570907041/5000000000 : ℝ), (273275443/500000000 : ℝ)] ![(137483877607/1562500000000 : ℝ), (43877479202971/100000000000000 : ℝ), (23661776311077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-140490511/1000000000 : ℝ)|^5319 ≤ (137483877607/1562500000000 : ℝ)^4295
        have hw : |(-140490511/1000000000 : ℝ)|=(140490511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570907041/5000000000 : ℝ)|^5319 ≤ (43877479202971/100000000000000 : ℝ)^4295
        have hw : |(2570907041/5000000000 : ℝ)|=(2570907041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273275443/500000000 : ℝ)|^5319 ≤ (23661776311077/50000000000000 : ℝ)^4295
        have hw : |(273275443/500000000 : ℝ)|=(273275443/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s2_5 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254347239/10000000000 : ℝ)*x 0 + (-1249058007/10000000000 : ℝ)*x 1 + (683188559/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254347239/10000000000 : ℝ)^5319 ≤ (45069813388931/100000000000000 : ℝ)^4295 := by
    have hnat : (5254347239 : ℕ)^5319*100000000000000^4295 ≤ 45069813388931^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254347239 10000000000 45069813388931 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249058007/10000000000 : ℝ)^5319 ≤ (3803319071431/50000000000000 : ℝ)^4295 := by
    have hnat : (1249058007 : ℕ)^5319*50000000000000^4295 ≤ 3803319071431^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249058007 10000000000 3803319071431 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683188559/1250000000 : ℝ)^5319 ≤ (5915443557707/12500000000000 : ℝ)^4295 := by
    have hnat : (683188559 : ℕ)^5319*12500000000000^4295 ≤ 5915443557707^4295*1250000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683188559 1250000000 5915443557707 12500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254347239/10000000000 : ℝ), (-1249058007/10000000000 : ℝ), (683188559/1250000000 : ℝ)] ![(45069813388931/100000000000000 : ℝ), (3803319071431/50000000000000 : ℝ), (5915443557707/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254347239/10000000000 : ℝ)|^5319 ≤ (45069813388931/100000000000000 : ℝ)^4295
        have hw : |(5254347239/10000000000 : ℝ)|=(5254347239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1249058007/10000000000 : ℝ)|^5319 ≤ (3803319071431/50000000000000 : ℝ)^4295
        have hw : |(-1249058007/10000000000 : ℝ)|=(1249058007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683188559/1250000000 : ℝ)|^5319 ≤ (5915443557707/12500000000000 : ℝ)^4295
        have hw : |(683188559/1250000000 : ℝ)|=(683188559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s2_6 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254347371/10000000000 : ℝ)*x 0 + (5465508009/10000000000 : ℝ)*x 1 + (-624529239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254347371/10000000000 : ℝ)^5319 ≤ (45069814791123/100000000000000 : ℝ)^4295 := by
    have hnat : (5254347371 : ℕ)^5319*100000000000000^4295 ≤ 45069814791123^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254347371 10000000000 45069814791123 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465508009/10000000000 : ℝ)^5319 ≤ (23661771748469/50000000000000 : ℝ)^4295 := by
    have hnat : (5465508009 : ℕ)^5319*50000000000000^4295 ≤ 23661771748469^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465508009 10000000000 23661771748469 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624529239/5000000000 : ℝ)^5319 ≤ (3803320847533/50000000000000 : ℝ)^4295 := by
    have hnat : (624529239 : ℕ)^5319*50000000000000^4295 ≤ 3803320847533^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624529239 5000000000 3803320847533 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254347371/10000000000 : ℝ), (5465508009/10000000000 : ℝ), (-624529239/5000000000 : ℝ)] ![(45069814791123/100000000000000 : ℝ), (23661771748469/50000000000000 : ℝ), (3803320847533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254347371/10000000000 : ℝ)|^5319 ≤ (45069814791123/100000000000000 : ℝ)^4295
        have hw : |(5254347371/10000000000 : ℝ)|=(5254347371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465508009/10000000000 : ℝ)|^5319 ≤ (23661771748469/50000000000000 : ℝ)^4295
        have hw : |(5465508009/10000000000 : ℝ)|=(5465508009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-624529239/5000000000 : ℝ)|^5319 ≤ (3803320847533/50000000000000 : ℝ)^4295
        have hw : |(-624529239/5000000000 : ℝ)|=(624529239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s2_7 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (205124839/500000000 : ℝ)*x 0 + (1147835991/2500000000 : ℝ)*x 1 + (1824298877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205124839/500000000 : ℝ)^5319 ≤ (6634717875247/20000000000000 : ℝ)^4295 := by
    have hnat : (205124839 : ℕ)^5319*20000000000000^4295 ≤ 6634717875247^4295*500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205124839 500000000 6634717875247 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147835991/2500000000 : ℝ)^5319 ≤ (38136481102447/100000000000000 : ℝ)^4295 := by
    have hnat : (1147835991 : ℕ)^5319*100000000000000^4295 ≤ 38136481102447^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147835991 2500000000 38136481102447 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1824298877/5000000000 : ℝ)^5319 ≤ (448280148637/1562500000000 : ℝ)^4295 := by
    have hnat : (1824298877 : ℕ)^5319*1562500000000^4295 ≤ 448280148637^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824298877 5000000000 448280148637 1562500000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(205124839/500000000 : ℝ), (1147835991/2500000000 : ℝ), (1824298877/5000000000 : ℝ)] ![(6634717875247/20000000000000 : ℝ), (38136481102447/100000000000000 : ℝ), (448280148637/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(205124839/500000000 : ℝ)|^5319 ≤ (6634717875247/20000000000000 : ℝ)^4295
        have hw : |(205124839/500000000 : ℝ)|=(205124839/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1147835991/2500000000 : ℝ)|^5319 ≤ (38136481102447/100000000000000 : ℝ)^4295
        have hw : |(1147835991/2500000000 : ℝ)|=(1147835991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1824298877/5000000000 : ℝ)|^5319 ≤ (448280148637/1562500000000 : ℝ)^4295
        have hw : |(1824298877/5000000000 : ℝ)|=(1824298877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1712_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8689/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10017/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17089/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8689/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8689/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8689/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8689/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8689/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8689/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9767/100000 : ℝ) ^ (5311/1024 : ℝ) ≤ (575934006589139/100000000000000000000 : ℝ) := by
    have hpowers : (9767/100000 : ℝ)^5311 ≤ (575934006589139/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9767 : ℕ)^5311*100000000000000000000^1024 ≤ 575934006589139^1024*100000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9767 100000 575934006589139 100000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9767/100000 : ℝ)) (X := (575934006589139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8689/50000 : ℝ) ^ (5311/1024 : ℝ) ≤ (5717565093021403/50000000000000000000 : ℝ) := by
    have hpowers : (8689/50000 : ℝ)^5311 ≤ (5717565093021403/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8689 : ℕ)^5311*50000000000000000000^1024 ≤ 5717565093021403^1024*50000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8689 50000 5717565093021403 50000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8689/50000 : ℝ)) (X := (5717565093021403/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000575934006589139/50000000000000000000 : ℝ) ≤ (1250002776095279/1250000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (50000575934006589139/50000000000000000000 : ℝ)^1024 ≤ (1250002776095279/1250000000000000 : ℝ)^5311 := by
      have hnat : (50000575934006589139 : ℕ)^1024*1250000000000000^5311 ≤ 1250002776095279^5311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000575934006589139 50000000000000000000 1250002776095279 1250000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002776095279/1250000000000000 : ℝ)) (X := (50000575934006589139/50000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002402212838526389/20000000000000000000 : ℝ) ≤ (400009262838299/400000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (20002402212838526389/20000000000000000000 : ℝ)^1024 ≤ (400009262838299/400000000000000 : ℝ)^5311 := by
      have hnat : (20002402212838526389 : ℕ)^1024*400000000000000^5311 ≤ 400009262838299^5311*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002402212838526389 20000000000000000000 400009262838299 400000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400009262838299/400000000000000 : ℝ)) (X := (20002402212838526389/20000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005717565093021403/25000000000000000000 : ℝ) ≤ (5000220466576359/5000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (25005717565093021403/25000000000000000000 : ℝ)^1024 ≤ (5000220466576359/5000000000000000 : ℝ)^5311 := by
      have hnat : (25005717565093021403 : ℕ)^1024*5000000000000000^5311 ≤ 5000220466576359^5311*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005717565093021403 25000000000000000000 5000220466576359 5000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000220466576359/5000000000000000 : ℝ)) (X := (25005717565093021403/25000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(575934006589139/100000000000000000000 : ℝ) ≤ ((7610607934976747099/7611000000000000000 : ℝ)+2*(209362195243/761100000000000 : ℝ)*(9767/100000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (7610607934976747099/7611000000000000000 : ℝ)+2*(209362195243/761100000000000 : ℝ)*(9767/100000 : ℝ)=(1250002776095279/1250000000000000 : ℝ) by norm_num, show 1+2*(575934006589139/100000000000000000000 : ℝ)=(50000575934006589139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5717565093021403/50000000000000000000 : ℝ)+(575934006589139/100000000000000000000 : ℝ) ≤ ((7610607934976747099/7611000000000000000 : ℝ)+(209362195243/761100000000000 : ℝ)*((8689/50000 : ℝ)+(9767/100000 : ℝ)))^(5311/1024 : ℝ) := by
    rw [show (7610607934976747099/7611000000000000000 : ℝ)+(209362195243/761100000000000 : ℝ)*((8689/50000 : ℝ)+(9767/100000 : ℝ))=(400009262838299/400000000000000 : ℝ) by norm_num, show 1+(5717565093021403/50000000000000000000 : ℝ)+(575934006589139/100000000000000000000 : ℝ)=(20002402212838526389/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5717565093021403/50000000000000000000 : ℝ) ≤ ((7610607934976747099/7611000000000000000 : ℝ)+2*(209362195243/761100000000000 : ℝ)*(8689/50000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (7610607934976747099/7611000000000000000 : ℝ)+2*(209362195243/761100000000000 : ℝ)*(8689/50000 : ℝ)=(5000220466576359/5000000000000000 : ℝ) by norm_num, show 1+2*(5717565093021403/50000000000000000000 : ℝ)=(25005717565093021403/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7610607934976747099/7611000000000000000 : ℝ)*(X 1 0+X 2 0)+(209362195243/761100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (9767/100000 : ℝ)) (hi := (8689/50000 : ℝ)) (c := (7610607934976747099/7611000000000000000 : ℝ)) (alpha := (209362195243/761100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7610607934976747099/7611000000000000000 : ℝ)*(X 0 1+X 2 1)+(209362195243/761100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (9767/100000 : ℝ)) (hi := (8689/50000 : ℝ)) (c := (7610607934976747099/7611000000000000000 : ℝ)) (alpha := (209362195243/761100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7610607934976747099/7611000000000000000 : ℝ)*(X 0 2+X 1 2)+(209362195243/761100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (9767/100000 : ℝ)) (hi := (8689/50000 : ℝ)) (c := (7610607934976747099/7611000000000000000 : ℝ)) (alpha := (209362195243/761100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-175594327/1250000000 : ℝ)*X 0 0+(5469246751/10000000000 : ℝ)*X 0 1+(5138131213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((333936427/625000000 : ℝ)*X 1 0+(-197054421/1250000000 : ℝ)*X 1 1+(5138131147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5342982841/10000000000 : ℝ)*X 2 0+(5138131179/10000000000 : ℝ)*X 2 1+(-788217657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((820411641/2000000000 : ℝ)*X 0 0+(3637709949/10000000000 : ℝ)*X 0 1+(2301035759/5000000000 : ℝ)*X 0 2+(820411641/2000000000 : ℝ)*X 1 0+(3637709949/10000000000 : ℝ)*X 1 1+(2301035759/5000000000 : ℝ)*X 1 2+(820411641/2000000000 : ℝ)*X 2 0+(3637709949/10000000000 : ℝ)*X 2 1+(2301035759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-140490511/1000000000 : ℝ)*X 0 0+(2570907041/5000000000 : ℝ)*X 0 1+(273275443/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254347239/10000000000 : ℝ)*X 1 0+(-1249058007/10000000000 : ℝ)*X 1 1+(683188559/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254347371/10000000000 : ℝ)*X 2 0+(5465508009/10000000000 : ℝ)*X 2 1+(-624529239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((205124839/500000000 : ℝ)*X 0 0+(1147835991/2500000000 : ℝ)*X 0 1+(1824298877/5000000000 : ℝ)*X 0 2+(205124839/500000000 : ℝ)*X 1 0+(1147835991/2500000000 : ℝ)*X 1 1+(1824298877/5000000000 : ℝ)*X 1 2+(205124839/500000000 : ℝ)*X 2 0+(1147835991/2500000000 : ℝ)*X 2 1+(1824298877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187973755228095263454942603/15856250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (812276231/50000000000000 : ℝ)*(base19) + (1489070797/100000000000000 : ℝ)*(base23) + (18776433/25000000000000 : ℝ)*(lower2) + (130741883/50000000000000 : ℝ)*(upper3) + (6132013/3125000000000 : ℝ)*(upper5) + (253568207248699/12500000000000 : ℝ)*(major0) + (253568207248699/12500000000000 : ℝ)*(major1) + (253568207248699/12500000000000 : ℝ)*(major2) + (755027326400557/25000000000000 : ℝ)*(sp0) + (377515401388957/12500000000000 : ℝ)*(sp1) + (75503083664833/2500000000000 : ℝ)*(sp2) + (259240099897659/25000000000000 : ℝ)*(sp3) + (1553006189/10000000000000 : ℝ)*(sp4) + (1421390537/25000000000000 : ℝ)*(sp7) + (64810380322049/6250000000000 : ℝ)*(f.failure) + (1510062417832059/50000000000000 : ℝ)*(f.sum) + (20427744130763/4756875000000000000000000000 : ℝ)*base66 + (82067800810901933/31712500000000000000000000000000 : ℝ)*base68 + (196277216069901933/31712500000000000000000000000000 : ℝ)*base70 + (312501391401101933/31712500000000000000000000000000 : ℝ)*base72 + (19648895752171/9513750000000000000000000000 : ℝ)*base74 + (88323472873851933/31712500000000000000000000000000 : ℝ)*base76 + (151469512852801933/31712500000000000000000000000000 : ℝ)*base78 + (50489383544201933/31712500000000000000000000000000 : ℝ)*base80 + (8945166798743/4756875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (987757/78125000000000000000 : ℝ)*base89 + (987757/78125000000000000000 : ℝ)*base91 + (987757/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1064218104729099223844282739/126850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (250233837/25000000000000 : ℝ)*(base19) + (567302073/50000000000000 : ℝ)*(base23) + (26407771/100000000000000 : ℝ)*(upper3) + (87618171/100000000000000 : ℝ)*(lower4) + (56081611/20000000000000 : ℝ)*(upper5) + (2075031575913213/100000000000000 : ℝ)*(major0) + (2075031575913213/100000000000000 : ℝ)*(major1) + (2075031575913213/100000000000000 : ℝ)*(major2) + (4697933241/50000000000000 : ℝ)*(sp1) + (2833818743/100000000000000 : ℝ)*(sp2) + (308933379202301/10000000000000 : ℝ)*(sp4) + (1544661697610589/50000000000000 : ℝ)*(sp5) + (77233245590003/2500000000000 : ℝ)*(sp6) + (66295567509423/6250000000000 : ℝ)*(sp7) + (66295567509423/6250000000000 : ℝ)*(f.failure) + (308933379202301/10000000000000 : ℝ)*(f.sum) + (37634515566353/12685000000000000000000000000 : ℝ)*base65 + (193635561507303029/253700000000000000000000000000000 : ℝ)*base67 + (773910252257303029/253700000000000000000000000000000 : ℝ)*base69 + (3584488171401503029/253700000000000000000000000000000 : ℝ)*base71 + (14011330304797/12685000000000000000000000000 : ℝ)*base74 + (3713921259558303029/253700000000000000000000000000000 : ℝ)*base75 + (2285136014528603029/253700000000000000000000000000000 : ℝ)*base77 + (2722968174906403029/253700000000000000000000000000000 : ℝ)*base79 + (35730224719403/12685000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (545511/78125000000000000000 : ℝ)*base90 + (545511/78125000000000000000 : ℝ)*base92 + (545511/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1712_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8689/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17089/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1712_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1712_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17089/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1712_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1712_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1712_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17089/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1712_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

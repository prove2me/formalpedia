-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1677_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:54.803843+00:00
-- url     : https://prove2.me/submissions/c6adfb36-5561-4a49-b881-8575a4028770

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
theorem support_rectangle_w1677_s0_0 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-179960487/1250000000 : ℝ)*x 0 + (1442255927/2500000000 : ℝ)*x 1 + (4921998651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179960487/1250000000 : ℝ)^5039 ≤ (878190189033/10000000000000 : ℝ)^4015 := by
    have hnat : (179960487 : ℕ)^5039*10000000000000^4015 ≤ 878190189033^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179960487 1250000000 878190189033 10000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1442255927/2500000000 : ℝ)^5039 ≤ (50138692401421/100000000000000 : ℝ)^4015 := by
    have hnat : (1442255927 : ℕ)^5039*100000000000000^4015 ≤ 50138692401421^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442255927 2500000000 50138692401421 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4921998651/10000000000 : ℝ)^5039 ≤ (20539702845043/50000000000000 : ℝ)^4015 := by
    have hnat : (4921998651 : ℕ)^5039*50000000000000^4015 ≤ 20539702845043^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4921998651 10000000000 20539702845043 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179960487/1250000000 : ℝ), (1442255927/2500000000 : ℝ), (4921998651/10000000000 : ℝ)] ![(878190189033/10000000000000 : ℝ), (50138692401421/100000000000000 : ℝ), (20539702845043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179960487/1250000000 : ℝ)|^5039 ≤ (878190189033/10000000000000 : ℝ)^4015
        have hw : |(-179960487/1250000000 : ℝ)|=(179960487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1442255927/2500000000 : ℝ)|^5039 ≤ (50138692401421/100000000000000 : ℝ)^4015
        have hw : |(1442255927/2500000000 : ℝ)|=(1442255927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4921998651/10000000000 : ℝ)|^5039 ≤ (20539702845043/50000000000000 : ℝ)^4015
        have hw : |(4921998651/10000000000 : ℝ)|=(4921998651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s0_1 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5428285757/10000000000 : ℝ)*x 0 + (-1903719917/10000000000 : ℝ)*x 1 + (1230499869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5428285757/10000000000 : ℝ)^5039 ≤ (23225235693261/50000000000000 : ℝ)^4015 := by
    have hnat : (5428285757 : ℕ)^5039*50000000000000^4015 ≤ 23225235693261^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428285757 10000000000 23225235693261 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1903719917/10000000000 : ℝ)^5039 ≤ (2494022850951/20000000000000 : ℝ)^4015 := by
    have hnat : (1903719917 : ℕ)^5039*20000000000000^4015 ≤ 2494022850951^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903719917 10000000000 2494022850951 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1230499869/2500000000 : ℝ)^5039 ≤ (41079414331711/100000000000000 : ℝ)^4015 := by
    have hnat : (1230499869 : ℕ)^5039*100000000000000^4015 ≤ 41079414331711^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230499869 2500000000 41079414331711 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5428285757/10000000000 : ℝ), (-1903719917/10000000000 : ℝ), (1230499869/2500000000 : ℝ)] ![(23225235693261/50000000000000 : ℝ), (2494022850951/20000000000000 : ℝ), (41079414331711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5428285757/10000000000 : ℝ)|^5039 ≤ (23225235693261/50000000000000 : ℝ)^4015
        have hw : |(5428285757/10000000000 : ℝ)|=(5428285757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1903719917/10000000000 : ℝ)|^5039 ≤ (2494022850951/20000000000000 : ℝ)^4015
        have hw : |(-1903719917/10000000000 : ℝ)|=(1903719917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1230499869/2500000000 : ℝ)|^5039 ≤ (41079414331711/100000000000000 : ℝ)^4015
        have hw : |(1230499869/2500000000 : ℝ)|=(1230499869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s0_2 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5428287079/10000000000 : ℝ)*x 0 + (984399713/2000000000 : ℝ)*x 1 + (-1903719351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5428287079/10000000000 : ℝ)^5039 ≤ (11612621396053/25000000000000 : ℝ)^4015 := by
    have hnat : (5428287079 : ℕ)^5039*25000000000000^4015 ≤ 11612621396053^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428287079 10000000000 11612621396053 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984399713/2000000000 : ℝ)^5039 ≤ (20539702394631/50000000000000 : ℝ)^4015 := by
    have hnat : (984399713 : ℕ)^5039*50000000000000^4015 ≤ 20539702394631^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984399713 2000000000 20539702394631 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1903719351/10000000000 : ℝ)^5039 ≤ (3117527400413/25000000000000 : ℝ)^4015 := by
    have hnat : (1903719351 : ℕ)^5039*25000000000000^4015 ≤ 3117527400413^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903719351 10000000000 3117527400413 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5428287079/10000000000 : ℝ), (984399713/2000000000 : ℝ), (-1903719351/10000000000 : ℝ)] ![(11612621396053/25000000000000 : ℝ), (20539702394631/50000000000000 : ℝ), (3117527400413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5428287079/10000000000 : ℝ)|^5039 ≤ (11612621396053/25000000000000 : ℝ)^4015
        have hw : |(5428287079/10000000000 : ℝ)|=(5428287079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(984399713/2000000000 : ℝ)|^5039 ≤ (20539702394631/50000000000000 : ℝ)^4015
        have hw : |(984399713/2000000000 : ℝ)|=(984399713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1903719351/10000000000 : ℝ)|^5039 ≤ (3117527400413/25000000000000 : ℝ)^4015
        have hw : |(-1903719351/10000000000 : ℝ)|=(1903719351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s0_3 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4068077113/10000000000 : ℝ)*x 0 + (3040902279/10000000000 : ℝ)*x 1 + (1328155669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4068077113/10000000000 : ℝ)^5039 ≤ (32341964146271/100000000000000 : ℝ)^4015 := by
    have hnat : (4068077113 : ℕ)^5039*100000000000000^4015 ≤ 32341964146271^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4068077113 10000000000 32341964146271 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3040902279/10000000000 : ℝ)^5039 ≤ (4489268220137/20000000000000 : ℝ)^4015 := by
    have hnat : (3040902279 : ℕ)^5039*20000000000000^4015 ≤ 4489268220137^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3040902279 10000000000 4489268220137 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1328155669/2500000000 : ℝ)^5039 ≤ (9042338946219/20000000000000 : ℝ)^4015 := by
    have hnat : (1328155669 : ℕ)^5039*20000000000000^4015 ≤ 9042338946219^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328155669 2500000000 9042338946219 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4068077113/10000000000 : ℝ), (3040902279/10000000000 : ℝ), (1328155669/2500000000 : ℝ)] ![(32341964146271/100000000000000 : ℝ), (4489268220137/20000000000000 : ℝ), (9042338946219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4068077113/10000000000 : ℝ)|^5039 ≤ (32341964146271/100000000000000 : ℝ)^4015
        have hw : |(4068077113/10000000000 : ℝ)|=(4068077113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3040902279/10000000000 : ℝ)|^5039 ≤ (4489268220137/20000000000000 : ℝ)^4015
        have hw : |(3040902279/10000000000 : ℝ)|=(3040902279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1328155669/2500000000 : ℝ)|^5039 ≤ (9042338946219/20000000000000 : ℝ)^4015
        have hw : |(1328155669/2500000000 : ℝ)|=(1328155669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s0_4 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-288390517/2000000000 : ℝ)*x 0 + (154485551/312500000 : ℝ)*x 1 + (5746724429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (288390517/2000000000 : ℝ)^5039 ≤ (8799273595009/100000000000000 : ℝ)^4015 := by
    have hnat : (288390517 : ℕ)^5039*100000000000000^4015 ≤ 8799273595009^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288390517 2000000000 8799273595009 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154485551/312500000 : ℝ)^5039 ≤ (1032628643911/2500000000000 : ℝ)^4015 := by
    have hnat : (154485551 : ℕ)^5039*2500000000000^4015 ≤ 1032628643911^4015*312500000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154485551 312500000 1032628643911 2500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5746724429/10000000000 : ℝ)^5039 ≤ (9979116126823/20000000000000 : ℝ)^4015 := by
    have hnat : (5746724429 : ℕ)^5039*20000000000000^4015 ≤ 9979116126823^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5746724429 10000000000 9979116126823 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-288390517/2000000000 : ℝ), (154485551/312500000 : ℝ), (5746724429/10000000000 : ℝ)] ![(8799273595009/100000000000000 : ℝ), (1032628643911/2500000000000 : ℝ), (9979116126823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-288390517/2000000000 : ℝ)|^5039 ≤ (8799273595009/100000000000000 : ℝ)^4015
        have hw : |(-288390517/2000000000 : ℝ)|=(288390517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(154485551/312500000 : ℝ)|^5039 ≤ (1032628643911/2500000000000 : ℝ)^4015
        have hw : |(154485551/312500000 : ℝ)|=(154485551/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5746724429/10000000000 : ℝ)|^5039 ≤ (9979116126823/20000000000000 : ℝ)^4015
        have hw : |(5746724429/10000000000 : ℝ)|=(5746724429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s0_5 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598934209/5000000000 : ℝ)*x 0 + (-539497791/5000000000 : ℝ)*x 1 + (2873360999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598934209/5000000000 : ℝ)^5039 ≤ (43989430736791/100000000000000 : ℝ)^4015 := by
    have hnat : (2598934209 : ℕ)^5039*100000000000000^4015 ≤ 43989430736791^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598934209 5000000000 43989430736791 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539497791/5000000000 : ℝ)^5039 ≤ (61150151037/1000000000000 : ℝ)^4015 := by
    have hnat : (539497791 : ℕ)^5039*1000000000000^4015 ≤ 61150151037^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539497791 5000000000 61150151037 1000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2873360999/5000000000 : ℝ)^5039 ≤ (24947777071951/50000000000000 : ℝ)^4015 := by
    have hnat : (2873360999 : ℕ)^5039*50000000000000^4015 ≤ 24947777071951^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2873360999 5000000000 24947777071951 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598934209/5000000000 : ℝ), (-539497791/5000000000 : ℝ), (2873360999/5000000000 : ℝ)] ![(43989430736791/100000000000000 : ℝ), (61150151037/1000000000000 : ℝ), (24947777071951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598934209/5000000000 : ℝ)|^5039 ≤ (43989430736791/100000000000000 : ℝ)^4015
        have hw : |(2598934209/5000000000 : ℝ)|=(2598934209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539497791/5000000000 : ℝ)|^5039 ≤ (61150151037/1000000000000 : ℝ)^4015
        have hw : |(-539497791/5000000000 : ℝ)|=(539497791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2873360999/5000000000 : ℝ)|^5039 ≤ (24947777071951/50000000000000 : ℝ)^4015
        have hw : |(2873360999/5000000000 : ℝ)|=(2873360999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s0_6 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197868283/10000000000 : ℝ)*x 0 + (718340167/1250000000 : ℝ)*x 1 + (-539498399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197868283/10000000000 : ℝ)^5039 ≤ (21994714651451/50000000000000 : ℝ)^4015 := by
    have hnat : (5197868283 : ℕ)^5039*50000000000000^4015 ≤ 21994714651451^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197868283 10000000000 21994714651451 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718340167/1250000000 : ℝ)^5039 ≤ (12473886732549/25000000000000 : ℝ)^4015 := by
    have hnat : (718340167 : ℕ)^5039*25000000000000^4015 ≤ 12473886732549^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718340167 1250000000 12473886732549 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539498399/5000000000 : ℝ)^5039 ≤ (1528755938197/25000000000000 : ℝ)^4015 := by
    have hnat : (539498399 : ℕ)^5039*25000000000000^4015 ≤ 1528755938197^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539498399 5000000000 1528755938197 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197868283/10000000000 : ℝ), (718340167/1250000000 : ℝ), (-539498399/5000000000 : ℝ)] ![(21994714651451/50000000000000 : ℝ), (12473886732549/25000000000000 : ℝ), (1528755938197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197868283/10000000000 : ℝ)|^5039 ≤ (21994714651451/50000000000000 : ℝ)^4015
        have hw : |(5197868283/10000000000 : ℝ)|=(5197868283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(718340167/1250000000 : ℝ)|^5039 ≤ (12473886732549/25000000000000 : ℝ)^4015
        have hw : |(718340167/1250000000 : ℝ)|=(718340167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539498399/5000000000 : ℝ)|^5039 ≤ (1528755938197/25000000000000 : ℝ)^4015
        have hw : |(-539498399/5000000000 : ℝ)|=(539498399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s0_7 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4074159187/10000000000 : ℝ)*x 0 + (1050970787/2000000000 : ℝ)*x 1 + (3100711141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4074159187/10000000000 : ℝ)^5039 ≤ (16201330800847/50000000000000 : ℝ)^4015 := by
    have hnat : (4074159187 : ℕ)^5039*50000000000000^4015 ≤ 16201330800847^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4074159187 10000000000 16201330800847 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050970787/2000000000 : ℝ)^5039 ≤ (44595540754319/100000000000000 : ℝ)^4015 := by
    have hnat : (1050970787 : ℕ)^5039*100000000000000^4015 ≤ 44595540754319^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050970787 2000000000 44595540754319 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3100711141/10000000000 : ℝ)^5039 ≤ (23001797631389/100000000000000 : ℝ)^4015 := by
    have hnat : (3100711141 : ℕ)^5039*100000000000000^4015 ≤ 23001797631389^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3100711141 10000000000 23001797631389 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4074159187/10000000000 : ℝ), (1050970787/2000000000 : ℝ), (3100711141/10000000000 : ℝ)] ![(16201330800847/50000000000000 : ℝ), (44595540754319/100000000000000 : ℝ), (23001797631389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4074159187/10000000000 : ℝ)|^5039 ≤ (16201330800847/50000000000000 : ℝ)^4015
        have hw : |(4074159187/10000000000 : ℝ)|=(4074159187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050970787/2000000000 : ℝ)|^5039 ≤ (44595540754319/100000000000000 : ℝ)^4015
        have hw : |(1050970787/2000000000 : ℝ)|=(1050970787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3100711141/10000000000 : ℝ)|^5039 ≤ (23001797631389/100000000000000 : ℝ)^4015
        have hw : |(3100711141/10000000000 : ℝ)|=(3100711141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1677_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4987/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11573/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5031/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5031 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5031*1^1024 ≤ 0^1024*1^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5031/1024 : ℝ) ≤ (221777015654933267/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5031 ≤ (221777015654933267/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5031*20000000000000000000^1024 ≤ 221777015654933267^1024*5^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 221777015654933267 20000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (221777015654933267/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5031 := by
      have hnat : (1 : ℕ)^1024*1^5031 ≤ 1^5031*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20221777015654933267/20000000000000000000 : ℝ) ≤ (5011235510694651/5000000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (20221777015654933267/20000000000000000000 : ℝ)^1024 ≤ (5011235510694651/5000000000000000 : ℝ)^5031 := by
      have hnat : (20221777015654933267 : ℕ)^1024*5000000000000000^5031 ≤ 5011235510694651^5031*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20221777015654933267 20000000000000000000 5011235510694651 5000000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011235510694651/5000000000000000 : ℝ)) (X := (20221777015654933267/20000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10221777015654933267/10000000000000000000 : ℝ) ≤ (2511235510694651/2500000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (10221777015654933267/10000000000000000000 : ℝ)^1024 ≤ (2511235510694651/2500000000000000 : ℝ)^5031 := by
      have hnat : (10221777015654933267 : ℕ)^1024*2500000000000000^5031 ≤ 2511235510694651^5031*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10221777015654933267 10000000000000000000 2511235510694651 2500000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511235510694651/2500000000000000 : ℝ)) (X := (10221777015654933267/10000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11235510694651/2000000000000000 : ℝ)*(0 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11235510694651/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(221777015654933267/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11235510694651/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5031/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11235510694651/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5011235510694651/5000000000000000 : ℝ) by norm_num, show 1+(221777015654933267/20000000000000000000 : ℝ)+(0 : ℝ)=(20221777015654933267/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(221777015654933267/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11235510694651/2000000000000000 : ℝ)*(2/5 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11235510694651/2000000000000000 : ℝ)*(2/5 : ℝ)=(2511235510694651/2500000000000000 : ℝ) by norm_num, show 1+2*(221777015654933267/20000000000000000000 : ℝ)=(10221777015654933267/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11235510694651/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11235510694651/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11235510694651/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11235510694651/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11235510694651/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11235510694651/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-179960487/1250000000 : ℝ)*X 0 0+(1442255927/2500000000 : ℝ)*X 0 1+(4921998651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5428285757/10000000000 : ℝ)*X 1 0+(-1903719917/10000000000 : ℝ)*X 1 1+(1230499869/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5428287079/10000000000 : ℝ)*X 2 0+(984399713/2000000000 : ℝ)*X 2 1+(-1903719351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4068077113/10000000000 : ℝ)*X 0 0+(3040902279/10000000000 : ℝ)*X 0 1+(1328155669/2500000000 : ℝ)*X 0 2+(4068077113/10000000000 : ℝ)*X 1 0+(3040902279/10000000000 : ℝ)*X 1 1+(1328155669/2500000000 : ℝ)*X 1 2+(4068077113/10000000000 : ℝ)*X 2 0+(3040902279/10000000000 : ℝ)*X 2 1+(1328155669/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-288390517/2000000000 : ℝ)*X 0 0+(154485551/312500000 : ℝ)*X 0 1+(5746724429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2598934209/5000000000 : ℝ)*X 1 0+(-539497791/5000000000 : ℝ)*X 1 1+(2873360999/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5197868283/10000000000 : ℝ)*X 2 0+(718340167/1250000000 : ℝ)*X 2 1+(-539498399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4074159187/10000000000 : ℝ)*X 0 0+(1050970787/2000000000 : ℝ)*X 0 1+(3100711141/10000000000 : ℝ)*X 0 2+(4074159187/10000000000 : ℝ)*X 1 0+(1050970787/2000000000 : ℝ)*X 1 1+(3100711141/10000000000 : ℝ)*X 1 2+(4074159187/10000000000 : ℝ)*X 2 0+(1050970787/2000000000 : ℝ)*X 2 1+(3100711141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120652320265995048602073/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122961551/100000000000000 : ℝ)*(base1) + (899615463/50000000000000 : ℝ)*(base19) + (2086757517/100000000000000 : ℝ)*(base23) + (4301541/4000000000000 : ℝ)*(upper3) + (14968989/4000000000000 : ℝ)*(upper5) + (202602692492459/25000000000000 : ℝ)*(major0) + (202602692492459/25000000000000 : ℝ)*(major1) + (202602692492459/25000000000000 : ℝ)*(major2) + (23612192322679/2000000000000 : ℝ)*(sp0) + (1180617915405661/100000000000000 : ℝ)*(sp1) + (118061762787907/10000000000000 : ℝ)*(sp2) + (440198442454519/100000000000000 : ℝ)*(sp3) + (2555366047/25000000000000 : ℝ)*(sp4) + (2938147489/100000000000000 : ℝ)*(sp7) + (440201503563559/100000000000000 : ℝ)*(f.failure) + (1180619714636587/100000000000000 : ℝ)*(f.sum) + (26155171386809/25000000000000000000000000000 : ℝ)*base65 + (175787202463191/50000000000000000000000000000 : ℝ)*base68 + (68706774386809/50000000000000000000000000000 : ℝ)*base69 + (18905395786809/50000000000000000000000000000 : ℝ)*base71 + (26393722161809/25000000000000000000000000000 : ℝ)*base73 + (266587402313191/50000000000000000000000000000 : ℝ)*base76 + (249697911863191/50000000000000000000000000000 : ℝ)*base78 + (283863459163191/50000000000000000000000000000 : ℝ)*base80 + (132595063561809/25000000000000000000000000000 : ℝ)*base81 + (9692031/2000000000000000000000 : ℝ)*base90 + (9692031/2000000000000000000000 : ℝ)*base92 + (9692031/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (574735512634021960181187/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168170359/12500000000000 : ℝ)*(base19) + (59257887/4000000000000 : ℝ)*(base23) + (230067021/100000000000000 : ℝ)*(base39) + (413153/1250000000000 : ℝ)*(upper2) + (52762681/20000000000000 : ℝ)*(upper5) + (427315195832607/50000000000000 : ℝ)*(major0) + (427315195832607/50000000000000 : ℝ)*(major1) + (854630161598193/100000000000000 : ℝ)*(major2) + (1634192837/50000000000000 : ℝ)*(sp1) + (975341/195312500000 : ℝ)*(sp2) + (124503950314899/10000000000000 : ℝ)*(sp4) + (311258722350111/25000000000000 : ℝ)*(sp5) + (249007550478849/20000000000000 : ℝ)*(sp6) + (14506901829247/3125000000000 : ℝ)*(sp7) + (14506901829247/3125000000000 : ℝ)*(f.failure) + (1245039733216011/100000000000000 : ℝ)*(f.sum) + (318505369335957/200000000000000000000000000000 : ℝ)*base65 + (201622992365643/200000000000000000000000000000 : ℝ)*base67 + (568276568885157/100000000000000000000000000000 : ℝ)*base69 + (1003663204765643/200000000000000000000000000000 : ℝ)*base71 + (252847405864043/200000000000000000000000000000 : ℝ)*base74 + (558276846285157/100000000000000000000000000000 : ℝ)*base75 + (204107071185157/100000000000000000000000000000 : ℝ)*base77 + (9600517714843/100000000000000000000000000000 : ℝ)*base80 + (87147428185157/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (673223/62500000000000000000 : ℝ)*base90 + (673223/62500000000000000000 : ℝ)*base92 + (673223/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1677_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11573/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1677_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1677_s1_0 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61337979/400000000 : ℝ)*x 0 + (5521351249/10000000000 : ℝ)*x 1 + (5108496637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61337979/400000000 : ℝ)^5039 ≤ (9505603445483/100000000000000 : ℝ)^4015 := by
    have hnat : (61337979 : ℕ)^5039*100000000000000^4015 ≤ 9505603445483^4015*400000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61337979 400000000 9505603445483 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5521351249/10000000000 : ℝ)^5039 ≤ (23726064584349/50000000000000 : ℝ)^4015 := by
    have hnat : (5521351249 : ℕ)^5039*50000000000000^4015 ≤ 23726064584349^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521351249 10000000000 23726064584349 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5108496637/10000000000 : ℝ)^5039 ≤ (21521133680599/50000000000000 : ℝ)^4015 := by
    have hnat : (5108496637 : ℕ)^5039*50000000000000^4015 ≤ 21521133680599^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5108496637 10000000000 21521133680599 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61337979/400000000 : ℝ), (5521351249/10000000000 : ℝ), (5108496637/10000000000 : ℝ)] ![(9505603445483/100000000000000 : ℝ), (23726064584349/50000000000000 : ℝ), (21521133680599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61337979/400000000 : ℝ)|^5039 ≤ (9505603445483/100000000000000 : ℝ)^4015
        have hw : |(-61337979/400000000 : ℝ)|=(61337979/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5521351249/10000000000 : ℝ)|^5039 ≤ (23726064584349/50000000000000 : ℝ)^4015
        have hw : |(5521351249/10000000000 : ℝ)|=(5521351249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5108496637/10000000000 : ℝ)|^5039 ≤ (21521133680599/50000000000000 : ℝ)^4015
        have hw : |(5108496637/10000000000 : ℝ)|=(5108496637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s1_1 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340573239/2500000000 : ℝ)*x 0 + (-1749407301/10000000000 : ℝ)*x 1 + (1021699321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340573239/2500000000 : ℝ)^5039 ≤ (22871420124387/50000000000000 : ℝ)^4015 := by
    have hnat : (1340573239 : ℕ)^5039*50000000000000^4015 ≤ 22871420124387^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340573239 2500000000 22871420124387 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1749407301/10000000000 : ℝ)^5039 ≤ (11214892712593/100000000000000 : ℝ)^4015 := by
    have hnat : (1749407301 : ℕ)^5039*100000000000000^4015 ≤ 11214892712593^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749407301 10000000000 11214892712593 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021699321/2000000000 : ℝ)^5039 ≤ (43042267022813/100000000000000 : ℝ)^4015 := by
    have hnat : (1021699321 : ℕ)^5039*100000000000000^4015 ≤ 43042267022813^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021699321 2000000000 43042267022813 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340573239/2500000000 : ℝ), (-1749407301/10000000000 : ℝ), (1021699321/2000000000 : ℝ)] ![(22871420124387/50000000000000 : ℝ), (11214892712593/100000000000000 : ℝ), (43042267022813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340573239/2500000000 : ℝ)|^5039 ≤ (22871420124387/50000000000000 : ℝ)^4015
        have hw : |(1340573239/2500000000 : ℝ)|=(1340573239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1749407301/10000000000 : ℝ)|^5039 ≤ (11214892712593/100000000000000 : ℝ)^4015
        have hw : |(-1749407301/10000000000 : ℝ)|=(1749407301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1021699321/2000000000 : ℝ)|^5039 ≤ (43042267022813/100000000000000 : ℝ)^4015
        have hw : |(1021699321/2000000000 : ℝ)|=(1021699321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s1_2 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134057313/250000000 : ℝ)*x 0 + (39910133/78125000 : ℝ)*x 1 + (-1749407331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134057313/250000000 : ℝ)^5039 ≤ (22871417790457/50000000000000 : ℝ)^4015 := by
    have hnat : (134057313 : ℕ)^5039*50000000000000^4015 ≤ 22871417790457^4015*250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134057313 250000000 22871417790457 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39910133/78125000 : ℝ)^5039 ≤ (43042271453539/100000000000000 : ℝ)^4015 := by
    have hnat : (39910133 : ℕ)^5039*100000000000000^4015 ≤ 43042271453539^4015*78125000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39910133 78125000 43042271453539 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1749407331/10000000000 : ℝ)^5039 ≤ (2803723238491/25000000000000 : ℝ)^4015 := by
    have hnat : (1749407331 : ℕ)^5039*25000000000000^4015 ≤ 2803723238491^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749407331 10000000000 2803723238491 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134057313/250000000 : ℝ), (39910133/78125000 : ℝ), (-1749407331/10000000000 : ℝ)] ![(22871417790457/50000000000000 : ℝ), (43042271453539/100000000000000 : ℝ), (2803723238491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134057313/250000000 : ℝ)|^5039 ≤ (22871417790457/50000000000000 : ℝ)^4015
        have hw : |(134057313/250000000 : ℝ)|=(134057313/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39910133/78125000 : ℝ)|^5039 ≤ (43042271453539/100000000000000 : ℝ)^4015
        have hw : |(39910133/78125000 : ℝ)|=(39910133/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1749407331/10000000000 : ℝ)|^5039 ≤ (2803723238491/25000000000000 : ℝ)^4015
        have hw : |(-1749407331/10000000000 : ℝ)|=(1749407331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s1_3 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4143818901/10000000000 : ℝ)*x 0 + (4519679/12500000 : ℝ)*x 1 + (1180754617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4143818901/10000000000 : ℝ)^5039 ≤ (8274872199549/25000000000000 : ℝ)^4015 := by
    have hnat : (4143818901 : ℕ)^5039*25000000000000^4015 ≤ 8274872199549^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143818901 10000000000 8274872199549 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519679/12500000 : ℝ)^5039 ≤ (6973626969633/25000000000000 : ℝ)^4015 := by
    have hnat : (4519679 : ℕ)^5039*25000000000000^4015 ≤ 6973626969633^4015*12500000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519679 12500000 6973626969633 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1180754617/2500000000 : ℝ)^5039 ≤ (39006003310367/100000000000000 : ℝ)^4015 := by
    have hnat : (1180754617 : ℕ)^5039*100000000000000^4015 ≤ 39006003310367^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180754617 2500000000 39006003310367 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4143818901/10000000000 : ℝ), (4519679/12500000 : ℝ), (1180754617/2500000000 : ℝ)] ![(8274872199549/25000000000000 : ℝ), (6973626969633/25000000000000 : ℝ), (39006003310367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4143818901/10000000000 : ℝ)|^5039 ≤ (8274872199549/25000000000000 : ℝ)^4015
        have hw : |(4143818901/10000000000 : ℝ)|=(4143818901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519679/12500000 : ℝ)|^5039 ≤ (6973626969633/25000000000000 : ℝ)^4015
        have hw : |(4519679/12500000 : ℝ)|=(4519679/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1180754617/2500000000 : ℝ)|^5039 ≤ (39006003310367/100000000000000 : ℝ)^4015
        have hw : |(1180754617/2500000000 : ℝ)|=(1180754617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s1_4 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-383427161/2500000000 : ℝ)*x 0 + (5113592291/10000000000 : ℝ)*x 1 + (5516167413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (383427161/2500000000 : ℝ)^5039 ≤ (9507619774697/100000000000000 : ℝ)^4015 := by
    have hnat : (383427161 : ℕ)^5039*100000000000000^4015 ≤ 9507619774697^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383427161 2500000000 9507619774697 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5113592291/10000000000 : ℝ)^5039 ≤ (43096158330451/100000000000000 : ℝ)^4015 := by
    have hnat : (5113592291 : ℕ)^5039*100000000000000^4015 ≤ 43096158330451^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113592291 10000000000 43096158330451 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5516167413/10000000000 : ℝ)^5039 ≤ (23698110943419/50000000000000 : ℝ)^4015 := by
    have hnat : (5516167413 : ℕ)^5039*50000000000000^4015 ≤ 23698110943419^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516167413 10000000000 23698110943419 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-383427161/2500000000 : ℝ), (5113592291/10000000000 : ℝ), (5516167413/10000000000 : ℝ)] ![(9507619774697/100000000000000 : ℝ), (43096158330451/100000000000000 : ℝ), (23698110943419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-383427161/2500000000 : ℝ)|^5039 ≤ (9507619774697/100000000000000 : ℝ)^4015
        have hw : |(-383427161/2500000000 : ℝ)|=(383427161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5113592291/10000000000 : ℝ)|^5039 ≤ (43096158330451/100000000000000 : ℝ)^4015
        have hw : |(5113592291/10000000000 : ℝ)|=(5113592291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5516167413/10000000000 : ℝ)|^5039 ≤ (23698110943419/50000000000000 : ℝ)^4015
        have hw : |(5516167413/10000000000 : ℝ)|=(5516167413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s1_5 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251994077/10000000000 : ℝ)*x 0 + (-33543457/250000000 : ℝ)*x 1 + (551616827/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251994077/10000000000 : ℝ)^5039 ≤ (2785317661029/6250000000000 : ℝ)^4015 := by
    have hnat : (5251994077 : ℕ)^5039*6250000000000^4015 ≤ 2785317661029^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251994077 10000000000 2785317661029 6250000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33543457/250000000 : ℝ)^5039 ≤ (8038686281031/100000000000000 : ℝ)^4015 := by
    have hnat : (33543457 : ℕ)^5039*100000000000000^4015 ≤ 8038686281031^4015*250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33543457 250000000 8038686281031 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551616827/1000000000 : ℝ)^5039 ≤ (47396231128411/100000000000000 : ℝ)^4015 := by
    have hnat : (551616827 : ℕ)^5039*100000000000000^4015 ≤ 47396231128411^4015*1000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551616827 1000000000 47396231128411 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251994077/10000000000 : ℝ), (-33543457/250000000 : ℝ), (551616827/1000000000 : ℝ)] ![(2785317661029/6250000000000 : ℝ), (8038686281031/100000000000000 : ℝ), (47396231128411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251994077/10000000000 : ℝ)|^5039 ≤ (2785317661029/6250000000000 : ℝ)^4015
        have hw : |(5251994077/10000000000 : ℝ)|=(5251994077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33543457/250000000 : ℝ)|^5039 ≤ (8038686281031/100000000000000 : ℝ)^4015
        have hw : |(-33543457/250000000 : ℝ)|=(33543457/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551616827/1000000000 : ℝ)|^5039 ≤ (47396231128411/100000000000000 : ℝ)^4015
        have hw : |(551616827/1000000000 : ℝ)|=(551616827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s1_6 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210079811/400000000 : ℝ)*x 0 + (551616791/1000000000 : ℝ)*x 1 + (-13417371/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210079811/400000000 : ℝ)^5039 ≤ (44565095334567/100000000000000 : ℝ)^4015 := by
    have hnat : (210079811 : ℕ)^5039*100000000000000^4015 ≤ 44565095334567^4015*400000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210079811 400000000 44565095334567 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551616791/1000000000 : ℝ)^5039 ≤ (47396227246303/100000000000000 : ℝ)^4015 := by
    have hnat : (551616791 : ℕ)^5039*100000000000000^4015 ≤ 47396227246303^4015*1000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551616791 1000000000 47396227246303 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13417371/100000000 : ℝ)^5039 ≤ (4019338704143/50000000000000 : ℝ)^4015 := by
    have hnat : (13417371 : ℕ)^5039*50000000000000^4015 ≤ 4019338704143^4015*100000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13417371 100000000 4019338704143 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210079811/400000000 : ℝ), (551616791/1000000000 : ℝ), (-13417371/100000000 : ℝ)] ![(44565095334567/100000000000000 : ℝ), (47396227246303/100000000000000 : ℝ), (4019338704143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210079811/400000000 : ℝ)|^5039 ≤ (44565095334567/100000000000000 : ℝ)^4015
        have hw : |(210079811/400000000 : ℝ)|=(210079811/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551616791/1000000000 : ℝ)|^5039 ≤ (47396227246303/100000000000000 : ℝ)^4015
        have hw : |(551616791/1000000000 : ℝ)|=(551616791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13417371/100000000 : ℝ)|^5039 ≤ (4019338704143/50000000000000 : ℝ)^4015
        have hw : |(-13417371/100000000 : ℝ)|=(13417371/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s1_7 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2072256337/5000000000 : ℝ)*x 0 + (941869897/2000000000 : ℝ)*x 1 + (3629645433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072256337/5000000000 : ℝ)^5039 ≤ (33106443940081/100000000000000 : ℝ)^4015 := by
    have hnat : (2072256337 : ℕ)^5039*100000000000000^4015 ≤ 33106443940081^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072256337 5000000000 33106443940081 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941869897/2000000000 : ℝ)^5039 ≤ (7772875239987/20000000000000 : ℝ)^4015 := by
    have hnat : (941869897 : ℕ)^5039*20000000000000^4015 ≤ 7772875239987^4015*2000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941869897 2000000000 7772875239987 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3629645433/10000000000 : ℝ)^5039 ≤ (2802917983879/10000000000000 : ℝ)^4015 := by
    have hnat : (3629645433 : ℕ)^5039*10000000000000^4015 ≤ 2802917983879^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3629645433 10000000000 2802917983879 10000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072256337/5000000000 : ℝ), (941869897/2000000000 : ℝ), (3629645433/10000000000 : ℝ)] ![(33106443940081/100000000000000 : ℝ), (7772875239987/20000000000000 : ℝ), (2802917983879/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072256337/5000000000 : ℝ)|^5039 ≤ (33106443940081/100000000000000 : ℝ)^4015
        have hw : |(2072256337/5000000000 : ℝ)|=(2072256337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(941869897/2000000000 : ℝ)|^5039 ≤ (7772875239987/20000000000000 : ℝ)^4015
        have hw : |(941869897/2000000000 : ℝ)|=(941869897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3629645433/10000000000 : ℝ)|^5039 ≤ (2802917983879/10000000000000 : ℝ)^4015
        have hw : |(3629645433/10000000000 : ℝ)|=(3629645433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1677_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11573/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2291/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3587/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11573/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11573/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11573/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11573/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11573/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11573/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4987/100000 : ℝ) ^ (5031/1024 : ℝ) ≤ (40028831410321/100000000000000000000 : ℝ) := by
    have hpowers : (4987/100000 : ℝ)^5031 ≤ (40028831410321/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4987 : ℕ)^5031*100000000000000000000^1024 ≤ 40028831410321^1024*100000^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4987 100000 40028831410321 100000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4987/100000 : ℝ)) (X := (40028831410321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11573/50000 : ℝ) ^ (5031/1024 : ℝ) ≤ (75442439114090527/100000000000000000000 : ℝ) := by
    have hpowers : (11573/50000 : ℝ)^5031 ≤ (75442439114090527/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11573 : ℕ)^5031*100000000000000000000^1024 ≤ 75442439114090527^1024*50000^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11573 50000 75442439114090527 100000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11573/50000 : ℝ)) (X := (75442439114090527/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000040028831410321/50000000000000000000 : ℝ) ≤ (10000001629477651/10000000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (50000040028831410321/50000000000000000000 : ℝ)^1024 ≤ (10000001629477651/10000000000000000 : ℝ)^5031 := by
      have hnat : (50000040028831410321 : ℕ)^1024*10000000000000000^5031 ≤ 10000001629477651^5031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000040028831410321 50000000000000000000 10000001629477651 10000000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001629477651/10000000000000000 : ℝ)) (X := (50000040028831410321/50000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6254717654246593803/6250000000000000000 : ℝ) ≤ (2000307178785539/2000000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (6254717654246593803/6250000000000000000 : ℝ)^1024 ≤ (2000307178785539/2000000000000000 : ℝ)^5031 := by
      have hnat : (6254717654246593803 : ℕ)^1024*2000000000000000^5031 ≤ 2000307178785539^5031*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254717654246593803 6250000000000000000 2000307178785539 2000000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000307178785539/2000000000000000 : ℝ)) (X := (6254717654246593803/6250000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50075442439114090527/50000000000000000000 : ℝ) ≤ (10003070158377739/10000000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (50075442439114090527/50000000000000000000 : ℝ)^1024 ≤ (10003070158377739/10000000000000000 : ℝ)^5031 := by
      have hnat : (50075442439114090527 : ℕ)^1024*10000000000000000^5031 ≤ 10003070158377739^5031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50075442439114090527 50000000000000000000 10003070158377739 10000000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003070158377739/10000000000000000 : ℝ)) (X := (50075442439114090527/50000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(40028831410321/100000000000000000000 : ℝ) ≤ ((60524908945353308551/60530000000000000000 : ℝ)+2*(127855370837/151325000000000 : ℝ)*(4987/100000 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (60524908945353308551/60530000000000000000 : ℝ)+2*(127855370837/151325000000000 : ℝ)*(4987/100000 : ℝ)=(10000001629477651/10000000000000000 : ℝ) by norm_num, show 1+2*(40028831410321/100000000000000000000 : ℝ)=(50000040028831410321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(75442439114090527/100000000000000000000 : ℝ)+(40028831410321/100000000000000000000 : ℝ) ≤ ((60524908945353308551/60530000000000000000 : ℝ)+(127855370837/151325000000000 : ℝ)*((11573/50000 : ℝ)+(4987/100000 : ℝ)))^(5031/1024 : ℝ) := by
    rw [show (60524908945353308551/60530000000000000000 : ℝ)+(127855370837/151325000000000 : ℝ)*((11573/50000 : ℝ)+(4987/100000 : ℝ))=(2000307178785539/2000000000000000 : ℝ) by norm_num, show 1+(75442439114090527/100000000000000000000 : ℝ)+(40028831410321/100000000000000000000 : ℝ)=(6254717654246593803/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(75442439114090527/100000000000000000000 : ℝ) ≤ ((60524908945353308551/60530000000000000000 : ℝ)+2*(127855370837/151325000000000 : ℝ)*(11573/50000 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (60524908945353308551/60530000000000000000 : ℝ)+2*(127855370837/151325000000000 : ℝ)*(11573/50000 : ℝ)=(10003070158377739/10000000000000000 : ℝ) by norm_num, show 1+2*(75442439114090527/100000000000000000000 : ℝ)=(50075442439114090527/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60524908945353308551/60530000000000000000 : ℝ)*(X 1 0+X 2 0)+(127855370837/151325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (4987/100000 : ℝ)) (hi := (11573/50000 : ℝ)) (c := (60524908945353308551/60530000000000000000 : ℝ)) (alpha := (127855370837/151325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60524908945353308551/60530000000000000000 : ℝ)*(X 0 1+X 2 1)+(127855370837/151325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (4987/100000 : ℝ)) (hi := (11573/50000 : ℝ)) (c := (60524908945353308551/60530000000000000000 : ℝ)) (alpha := (127855370837/151325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60524908945353308551/60530000000000000000 : ℝ)*(X 0 2+X 1 2)+(127855370837/151325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (4987/100000 : ℝ)) (hi := (11573/50000 : ℝ)) (c := (60524908945353308551/60530000000000000000 : ℝ)) (alpha := (127855370837/151325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-61337979/400000000 : ℝ)*X 0 0+(5521351249/10000000000 : ℝ)*X 0 1+(5108496637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340573239/2500000000 : ℝ)*X 1 0+(-1749407301/10000000000 : ℝ)*X 1 1+(1021699321/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((134057313/250000000 : ℝ)*X 2 0+(39910133/78125000 : ℝ)*X 2 1+(-1749407331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4143818901/10000000000 : ℝ)*X 0 0+(4519679/12500000 : ℝ)*X 0 1+(1180754617/2500000000 : ℝ)*X 0 2+(4143818901/10000000000 : ℝ)*X 1 0+(4519679/12500000 : ℝ)*X 1 1+(1180754617/2500000000 : ℝ)*X 1 2+(4143818901/10000000000 : ℝ)*X 2 0+(4519679/12500000 : ℝ)*X 2 1+(1180754617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-383427161/2500000000 : ℝ)*X 0 0+(5113592291/10000000000 : ℝ)*X 0 1+(5516167413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251994077/10000000000 : ℝ)*X 1 0+(-33543457/250000000 : ℝ)*X 1 1+(551616827/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((210079811/400000000 : ℝ)*X 2 0+(551616791/1000000000 : ℝ)*X 2 1+(-13417371/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2072256337/5000000000 : ℝ)*X 0 0+(941869897/2000000000 : ℝ)*X 0 1+(3629645433/10000000000 : ℝ)*X 0 2+(2072256337/5000000000 : ℝ)*X 1 0+(941869897/2000000000 : ℝ)*X 1 1+(3629645433/10000000000 : ℝ)*X 1 2+(2072256337/5000000000 : ℝ)*X 2 0+(941869897/2000000000 : ℝ)*X 2 1+(3629645433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2153738819381617458140214327/189156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (762211/50000000000000 : ℝ)*(base1) + (1726148153/100000000000000 : ℝ)*(base19) + (764601833/50000000000000 : ℝ)*(base23) + (15815007/6250000000000 : ℝ)*(upper3) + (51365411/25000000000000 : ℝ)*(upper5) + (103916208034553/6250000000000 : ℝ)*(major0) + (103916208034553/6250000000000 : ℝ)*(major1) + (103916208034553/6250000000000 : ℝ)*(major2) + (605543848353593/25000000000000 : ℝ)*(sp0) + (48443759220091/2000000000000 : ℝ)*(sp1) + (2422188157949037/100000000000000 : ℝ)*(sp2) + (903123097809273/100000000000000 : ℝ)*(sp3) + (14295262753/100000000000000 : ℝ)*(sp4) + (1098216989/20000000000000 : ℝ)*(sp7) + (903128590418639/100000000000000 : ℝ)*(f.failure) + (2422189687152703/100000000000000 : ℝ)*(f.sum) + (88532861276711/30265000000000000000000000000 : ℝ)*base66 + (2913499296666487297/378312500000000000000000000000000 : ℝ)*base68 + (2504093377790112297/378312500000000000000000000000000 : ℝ)*base70 + (2061171458818424797/378312500000000000000000000000000 : ℝ)*base72 + (164924962779271/30265000000000000000000000000 : ℝ)*base74 + (1136046448117674797/378312500000000000000000000000000 : ℝ)*base76 + (1492701482088424797/378312500000000000000000000000000 : ℝ)*base78 + (1657947500620299797/378312500000000000000000000000000 : ℝ)*base80 + (79334477527963/15132500000000000000000000000 : ℝ)*base82 + (14212249/2000000000000000000000 : ℝ)*base89 + (14212249/2000000000000000000000 : ℝ)*base91 + (14212249/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (561429268217051062051533339/121060000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (293489243/100000000000000 : ℝ)*(base23) + (1270463/10000000000000 : ℝ)*(lower2) + (26610011/12500000000000 : ℝ)*(upper3) + (16989441/10000000000000 : ℝ)*(upper4) + (187881859/50000000000000 : ℝ)*(upper5) + (68203913112463/4000000000000 : ℝ)*(major0) + (68203913112463/4000000000000 : ℝ)*(major1) + (68203913112463/4000000000000 : ℝ)*(major2) + (3549902857/100000000000000 : ℝ)*(sp2) + (31838891/12500000000000 : ℝ)*(sp3) + (1242007515701971/50000000000000 : ℝ)*(sp4) + (1242007515701971/50000000000000 : ℝ)*(sp5) + (1242005594005921/50000000000000 : ℝ)*(sp6) + (926180214921021/100000000000000 : ℝ)*(sp7) + (926180469632149/100000000000000 : ℝ)*(f.failure) + (1242007515701971/50000000000000 : ℝ)*(f.sum) + (14177175796291/3026500000000000000000000000 : ℝ)*base66 + (289133513467868887/242120000000000000000000000000000 : ℝ)*base68 + (459110502716188887/242120000000000000000000000000000 : ℝ)*base70 + (263714309701051113/242120000000000000000000000000000 : ℝ)*base71 + (3016179563459/1210600000000000000000000000 : ℝ)*base73 + (922329231259468887/242120000000000000000000000000000 : ℝ)*base76 + (1409589663990331113/242120000000000000000000000000000 : ℝ)*base77 + (2539826959839788887/242120000000000000000000000000000 : ℝ)*base80 + (1275035901573/605300000000000000000000000 : ℝ)*base81 + (509341/2000000000000000000000 : ℝ)*base90 + (509341/2000000000000000000000 : ℝ)*base92 + (509341/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1677_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11573/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3587/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1677_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1677_s2_0 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1540428467/10000000000 : ℝ)*x 0 + (5493898527/10000000000 : ℝ)*x 1 + (5131330651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1540428467/10000000000 : ℝ)^5039 ≤ (9559930158131/100000000000000 : ℝ)^4015 := by
    have hnat : (1540428467 : ℕ)^5039*100000000000000^4015 ≤ 9559930158131^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540428467 10000000000 9559930158131 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493898527/10000000000 : ℝ)^5039 ≤ (2357810307271/5000000000000 : ℝ)^4015 := by
    have hnat : (5493898527 : ℕ)^5039*5000000000000^4015 ≤ 2357810307271^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493898527 10000000000 2357810307271 5000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131330651/10000000000 : ℝ)^5039 ≤ (1731354546991/4000000000000 : ℝ)^4015 := by
    have hnat : (5131330651 : ℕ)^5039*4000000000000^4015 ≤ 1731354546991^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131330651 10000000000 1731354546991 4000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1540428467/10000000000 : ℝ), (5493898527/10000000000 : ℝ), (5131330651/10000000000 : ℝ)] ![(9559930158131/100000000000000 : ℝ), (2357810307271/5000000000000 : ℝ), (1731354546991/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1540428467/10000000000 : ℝ)|^5039 ≤ (9559930158131/100000000000000 : ℝ)^4015
        have hw : |(-1540428467/10000000000 : ℝ)|=(1540428467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493898527/10000000000 : ℝ)|^5039 ≤ (2357810307271/5000000000000 : ℝ)^4015
        have hw : |(5493898527/10000000000 : ℝ)|=(5493898527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131330651/10000000000 : ℝ)|^5039 ≤ (1731354546991/4000000000000 : ℝ)^4015
        have hw : |(5131330651/10000000000 : ℝ)|=(5131330651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s2_1 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354992489/10000000000 : ℝ)*x 0 + (-864530989/5000000000 : ℝ)*x 1 + (5131330453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354992489/10000000000 : ℝ)^5039 ≤ (1427021696081/3125000000000 : ℝ)^4015 := by
    have hnat : (5354992489 : ℕ)^5039*3125000000000^4015 ≤ 1427021696081^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354992489 10000000000 1427021696081 3125000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (864530989/5000000000 : ℝ)^5039 ≤ (2210288826499/20000000000000 : ℝ)^4015 := by
    have hnat : (864530989 : ℕ)^5039*20000000000000^4015 ≤ 2210288826499^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864530989 5000000000 2210288826499 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131330453/10000000000 : ℝ)^5039 ≤ (43283861578637/100000000000000 : ℝ)^4015 := by
    have hnat : (5131330453 : ℕ)^5039*100000000000000^4015 ≤ 43283861578637^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131330453 10000000000 43283861578637 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354992489/10000000000 : ℝ), (-864530989/5000000000 : ℝ), (5131330453/10000000000 : ℝ)] ![(1427021696081/3125000000000 : ℝ), (2210288826499/20000000000000 : ℝ), (43283861578637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354992489/10000000000 : ℝ)|^5039 ≤ (1427021696081/3125000000000 : ℝ)^4015
        have hw : |(5354992489/10000000000 : ℝ)|=(5354992489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-864530989/5000000000 : ℝ)|^5039 ≤ (2210288826499/20000000000000 : ℝ)^4015
        have hw : |(-864530989/5000000000 : ℝ)|=(864530989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131330453/10000000000 : ℝ)|^5039 ≤ (43283861578637/100000000000000 : ℝ)^4015
        have hw : |(5131330453/10000000000 : ℝ)|=(5131330453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s2_2 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669374057/1250000000 : ℝ)*x 0 + (5131330407/10000000000 : ℝ)*x 1 + (-864531041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669374057/1250000000 : ℝ)^5039 ≤ (45664693921413/100000000000000 : ℝ)^4015 := by
    have hnat : (669374057 : ℕ)^5039*100000000000000^4015 ≤ 45664693921413^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669374057 1250000000 45664693921413 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131330407/10000000000 : ℝ)^5039 ≤ (8656772218331/20000000000000 : ℝ)^4015 := by
    have hnat : (5131330407 : ℕ)^5039*20000000000000^4015 ≤ 8656772218331^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131330407 10000000000 8656772218331 20000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864531041/5000000000 : ℝ)^5039 ≤ (5525722483377/50000000000000 : ℝ)^4015 := by
    have hnat : (864531041 : ℕ)^5039*50000000000000^4015 ≤ 5525722483377^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864531041 5000000000 5525722483377 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669374057/1250000000 : ℝ), (5131330407/10000000000 : ℝ), (-864531041/5000000000 : ℝ)] ![(45664693921413/100000000000000 : ℝ), (8656772218331/20000000000000 : ℝ), (5525722483377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669374057/1250000000 : ℝ)|^5039 ≤ (45664693921413/100000000000000 : ℝ)^4015
        have hw : |(669374057/1250000000 : ℝ)|=(669374057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131330407/10000000000 : ℝ)|^5039 ≤ (8656772218331/20000000000000 : ℝ)^4015
        have hw : |(5131330407/10000000000 : ℝ)|=(5131330407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-864531041/5000000000 : ℝ)|^5039 ≤ (5525722483377/50000000000000 : ℝ)^4015
        have hw : |(-864531041/5000000000 : ℝ)|=(864531041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s2_3 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4149156407/10000000000 : ℝ)*x 0 + (3682662723/10000000000 : ℝ)*x 1 + (2327535743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4149156407/10000000000 : ℝ)^5039 ≤ (16576502729729/50000000000000 : ℝ)^4015 := by
    have hnat : (4149156407 : ℕ)^5039*50000000000000^4015 ≤ 16576502729729^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149156407 10000000000 16576502729729 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3682662723/10000000000 : ℝ)^5039 ≤ (14271983560527/50000000000000 : ℝ)^4015 := by
    have hnat : (3682662723 : ℕ)^5039*50000000000000^4015 ≤ 14271983560527^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3682662723 10000000000 14271983560527 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2327535743/5000000000 : ℝ)^5039 ≤ (38303027398811/100000000000000 : ℝ)^4015 := by
    have hnat : (2327535743 : ℕ)^5039*100000000000000^4015 ≤ 38303027398811^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327535743 5000000000 38303027398811 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4149156407/10000000000 : ℝ), (3682662723/10000000000 : ℝ), (2327535743/5000000000 : ℝ)] ![(16576502729729/50000000000000 : ℝ), (14271983560527/50000000000000 : ℝ), (38303027398811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4149156407/10000000000 : ℝ)|^5039 ≤ (16576502729729/50000000000000 : ℝ)^4015
        have hw : |(4149156407/10000000000 : ℝ)|=(4149156407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3682662723/10000000000 : ℝ)|^5039 ≤ (14271983560527/50000000000000 : ℝ)^4015
        have hw : |(3682662723/10000000000 : ℝ)|=(3682662723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2327535743/5000000000 : ℝ)|^5039 ≤ (38303027398811/100000000000000 : ℝ)^4015
        have hw : |(2327535743/5000000000 : ℝ)|=(2327535743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s2_4 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1540603387/10000000000 : ℝ)*x 0 + (5135265261/10000000000 : ℝ)*x 1 + (2744952307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1540603387/10000000000 : ℝ)^5039 ≤ (9561292599273/100000000000000 : ℝ)^4015 := by
    have hnat : (1540603387 : ℕ)^5039*100000000000000^4015 ≤ 9561292599273^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540603387 10000000000 9561292599273 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135265261/10000000000 : ℝ)^5039 ≤ (1083138043213/2500000000000 : ℝ)^4015 := by
    have hnat : (5135265261 : ℕ)^5039*2500000000000^4015 ≤ 1083138043213^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135265261 10000000000 1083138043213 2500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744952307/5000000000 : ℝ)^5039 ≤ (47113185654433/100000000000000 : ℝ)^4015 := by
    have hnat : (2744952307 : ℕ)^5039*100000000000000^4015 ≤ 47113185654433^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744952307 5000000000 47113185654433 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1540603387/10000000000 : ℝ), (5135265261/10000000000 : ℝ), (2744952307/5000000000 : ℝ)] ![(9561292599273/100000000000000 : ℝ), (1083138043213/2500000000000 : ℝ), (47113185654433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1540603387/10000000000 : ℝ)|^5039 ≤ (9561292599273/100000000000000 : ℝ)^4015
        have hw : |(-1540603387/10000000000 : ℝ)|=(1540603387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135265261/10000000000 : ℝ)|^5039 ≤ (1083138043213/2500000000000 : ℝ)^4015
        have hw : |(5135265261/10000000000 : ℝ)|=(5135265261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744952307/5000000000 : ℝ)|^5039 ≤ (47113185654433/100000000000000 : ℝ)^4015
        have hw : |(2744952307/5000000000 : ℝ)|=(2744952307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s2_5 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258217131/10000000000 : ℝ)*x 0 + (-1370487797/10000000000 : ℝ)*x 1 + (1372476151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258217131/10000000000 : ℝ)^5039 ≤ (348682539163/781250000000 : ℝ)^4015 := by
    have hnat : (5258217131 : ℕ)^5039*781250000000^4015 ≤ 348682539163^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258217131 10000000000 348682539163 781250000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370487797/10000000000 : ℝ)^5039 ≤ (1031931178559/12500000000000 : ℝ)^4015 := by
    have hnat : (1370487797 : ℕ)^5039*12500000000000^4015 ≤ 1031931178559^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370487797 10000000000 1031931178559 12500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372476151/2500000000 : ℝ)^5039 ≤ (5889148193341/12500000000000 : ℝ)^4015 := by
    have hnat : (1372476151 : ℕ)^5039*12500000000000^4015 ≤ 5889148193341^4015*2500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372476151 2500000000 5889148193341 12500000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258217131/10000000000 : ℝ), (-1370487797/10000000000 : ℝ), (1372476151/2500000000 : ℝ)] ![(348682539163/781250000000 : ℝ), (1031931178559/12500000000000 : ℝ), (5889148193341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258217131/10000000000 : ℝ)|^5039 ≤ (348682539163/781250000000 : ℝ)^4015
        have hw : |(5258217131/10000000000 : ℝ)|=(5258217131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1370487797/10000000000 : ℝ)|^5039 ≤ (1031931178559/12500000000000 : ℝ)^4015
        have hw : |(-1370487797/10000000000 : ℝ)|=(1370487797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372476151/2500000000 : ℝ)|^5039 ≤ (5889148193341/12500000000000 : ℝ)^4015
        have hw : |(1372476151/2500000000 : ℝ)|=(1372476151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s2_6 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657277139/1250000000 : ℝ)*x 0 + (2744952317/5000000000 : ℝ)*x 1 + (-1370487781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657277139/1250000000 : ℝ)^5039 ≤ (22315682405231/50000000000000 : ℝ)^4015 := by
    have hnat : (657277139 : ℕ)^5039*50000000000000^4015 ≤ 22315682405231^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657277139 1250000000 22315682405231 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744952317/5000000000 : ℝ)^5039 ≤ (47113185869843/100000000000000 : ℝ)^4015 := by
    have hnat : (2744952317 : ℕ)^5039*100000000000000^4015 ≤ 47113185869843^4015*5000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744952317 5000000000 47113185869843 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370487781/10000000000 : ℝ)^5039 ≤ (8255449307511/100000000000000 : ℝ)^4015 := by
    have hnat : (1370487781 : ℕ)^5039*100000000000000^4015 ≤ 8255449307511^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370487781 10000000000 8255449307511 100000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657277139/1250000000 : ℝ), (2744952317/5000000000 : ℝ), (-1370487781/10000000000 : ℝ)] ![(22315682405231/50000000000000 : ℝ), (47113185869843/100000000000000 : ℝ), (8255449307511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657277139/1250000000 : ℝ)|^5039 ≤ (22315682405231/50000000000000 : ℝ)^4015
        have hw : |(657277139/1250000000 : ℝ)|=(657277139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744952317/5000000000 : ℝ)|^5039 ≤ (47113185869843/100000000000000 : ℝ)^4015
        have hw : |(2744952317/5000000000 : ℝ)|=(2744952317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1370487781/10000000000 : ℝ)|^5039 ≤ (8255449307511/100000000000000 : ℝ)^4015
        have hw : |(-1370487781/10000000000 : ℝ)|=(1370487781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1677_s2_7 (p : ℝ) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207481271/500000000 : ℝ)*x 0 + (4644517911/10000000000 : ℝ)*x 1 + (461671939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207481271/500000000 : ℝ)^5039 ≤ (8289427217933/25000000000000 : ℝ)^4015 := by
    have hnat : (207481271 : ℕ)^5039*25000000000000^4015 ≤ 8289427217933^4015*500000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207481271 500000000 8289427217933 25000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4644517911/10000000000 : ℝ)^5039 ≤ (2387129644957/6250000000000 : ℝ)^4015 := by
    have hnat : (4644517911 : ℕ)^5039*6250000000000^4015 ≤ 2387129644957^4015*10000000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4644517911 10000000000 2387129644957 6250000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461671939/1250000000 : ℝ)^5039 ≤ (14324108397527/50000000000000 : ℝ)^4015 := by
    have hnat : (461671939 : ℕ)^5039*50000000000000^4015 ≤ 14324108397527^4015*1250000000^5039 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461671939 1250000000 14324108397527 50000000000000 5039 4015 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5039/1024 : ℝ)) 5039 4015 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207481271/500000000 : ℝ), (4644517911/10000000000 : ℝ), (461671939/1250000000 : ℝ)] ![(8289427217933/25000000000000 : ℝ), (2387129644957/6250000000000 : ℝ), (14324108397527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207481271/500000000 : ℝ)|^5039 ≤ (8289427217933/25000000000000 : ℝ)^4015
        have hw : |(207481271/500000000 : ℝ)|=(207481271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4644517911/10000000000 : ℝ)|^5039 ≤ (2387129644957/6250000000000 : ℝ)^4015
        have hw : |(4644517911/10000000000 : ℝ)|=(4644517911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461671939/1250000000 : ℝ)|^5039 ≤ (14324108397527/50000000000000 : ℝ)^4015
        have hw : |(461671939/1250000000 : ℝ)|=(461671939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1677_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3587/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (9661/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17363/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3587/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2291/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3587/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2291/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3587/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2291/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3587/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2291/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3587/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2291/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3587/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2291/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2291/25000 : ℝ) ^ (5031/1024 : ℝ) ≤ (795490146919713/100000000000000000000 : ℝ) := by
    have hpowers : (2291/25000 : ℝ)^5031 ≤ (795490146919713/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2291 : ℕ)^5031*100000000000000000000^1024 ≤ 795490146919713^1024*25000^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2291 25000 795490146919713 100000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2291/25000 : ℝ)) (X := (795490146919713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3587/20000 : ℝ) ^ (5031/1024 : ℝ) ≤ (21546203128520279/100000000000000000000 : ℝ) := by
    have hpowers : (3587/20000 : ℝ)^5031 ≤ (21546203128520279/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3587 : ℕ)^5031*100000000000000000000^1024 ≤ 21546203128520279^1024*20000^5031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3587 20000 21546203128520279 100000000000000000000 5031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3587/20000 : ℝ)) (X := (21546203128520279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000795490146919713/50000000000000000000 : ℝ) ≤ (5000016191149861/5000000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (50000795490146919713/50000000000000000000 : ℝ)^1024 ≤ (5000016191149861/5000000000000000 : ℝ)^5031 := by
      have hnat : (50000795490146919713 : ℕ)^1024*5000000000000000^5031 ≤ 5000016191149861^5031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000795490146919713 50000000000000000000 5000016191149861 5000000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000016191149861/5000000000000000 : ℝ)) (X := (50000795490146919713/50000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502792711659429999/12500000000000000000 : ℝ) ≤ (10000454698046211/10000000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (12502792711659429999/12500000000000000000 : ℝ)^1024 ≤ (10000454698046211/10000000000000000 : ℝ)^5031 := by
      have hnat : (12502792711659429999 : ℕ)^1024*10000000000000000^5031 ≤ 10000454698046211^5031*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502792711659429999 12500000000000000000 10000454698046211 10000000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000454698046211/10000000000000000 : ℝ)) (X := (12502792711659429999/12500000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021546203128520279/50000000000000000000 : ℝ) ≤ (100008770137927/100000000000000 : ℝ) ^ (5031/1024 : ℝ) := by
    have hpowers : (50021546203128520279/50000000000000000000 : ℝ)^1024 ≤ (100008770137927/100000000000000 : ℝ)^5031 := by
      have hnat : (50021546203128520279 : ℕ)^1024*100000000000000^5031 ≤ 100008770137927^5031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021546203128520279 50000000000000000000 100008770137927 100000000000000 1024 5031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100008770137927/100000000000000 : ℝ)) (X := (50021546203128520279/50000000000000000000 : ℝ)) (by norm_num) 5031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(795490146919713/100000000000000000000 : ℝ) ≤ ((1252893483173560161/1253000000000000000 : ℝ)+2*(60330820927/125300000000000 : ℝ)*(2291/25000 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (1252893483173560161/1253000000000000000 : ℝ)+2*(60330820927/125300000000000 : ℝ)*(2291/25000 : ℝ)=(5000016191149861/5000000000000000 : ℝ) by norm_num, show 1+2*(795490146919713/100000000000000000000 : ℝ)=(50000795490146919713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21546203128520279/100000000000000000000 : ℝ)+(795490146919713/100000000000000000000 : ℝ) ≤ ((1252893483173560161/1253000000000000000 : ℝ)+(60330820927/125300000000000 : ℝ)*((3587/20000 : ℝ)+(2291/25000 : ℝ)))^(5031/1024 : ℝ) := by
    rw [show (1252893483173560161/1253000000000000000 : ℝ)+(60330820927/125300000000000 : ℝ)*((3587/20000 : ℝ)+(2291/25000 : ℝ))=(10000454698046211/10000000000000000 : ℝ) by norm_num, show 1+(21546203128520279/100000000000000000000 : ℝ)+(795490146919713/100000000000000000000 : ℝ)=(12502792711659429999/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21546203128520279/100000000000000000000 : ℝ) ≤ ((1252893483173560161/1253000000000000000 : ℝ)+2*(60330820927/125300000000000 : ℝ)*(3587/20000 : ℝ))^(5031/1024 : ℝ) := by
    rw [show (1252893483173560161/1253000000000000000 : ℝ)+2*(60330820927/125300000000000 : ℝ)*(3587/20000 : ℝ)=(100008770137927/100000000000000 : ℝ) by norm_num, show 1+2*(21546203128520279/100000000000000000000 : ℝ)=(50021546203128520279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1252893483173560161/1253000000000000000 : ℝ)*(X 1 0+X 2 0)+(60330820927/125300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (2291/25000 : ℝ)) (hi := (3587/20000 : ℝ)) (c := (1252893483173560161/1253000000000000000 : ℝ)) (alpha := (60330820927/125300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1252893483173560161/1253000000000000000 : ℝ)*(X 0 1+X 2 1)+(60330820927/125300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (2291/25000 : ℝ)) (hi := (3587/20000 : ℝ)) (c := (1252893483173560161/1253000000000000000 : ℝ)) (alpha := (60330820927/125300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1252893483173560161/1253000000000000000 : ℝ)*(X 0 2+X 1 2)+(60330820927/125300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5031/1024 : ℝ)) (lo := (2291/25000 : ℝ)) (hi := (3587/20000 : ℝ)) (c := (1252893483173560161/1253000000000000000 : ℝ)) (alpha := (60330820927/125300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1540428467/10000000000 : ℝ)*X 0 0+(5493898527/10000000000 : ℝ)*X 0 1+(5131330651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354992489/10000000000 : ℝ)*X 1 0+(-864530989/5000000000 : ℝ)*X 1 1+(5131330453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669374057/1250000000 : ℝ)*X 2 0+(5131330407/10000000000 : ℝ)*X 2 1+(-864531041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4149156407/10000000000 : ℝ)*X 0 0+(3682662723/10000000000 : ℝ)*X 0 1+(2327535743/5000000000 : ℝ)*X 0 2+(4149156407/10000000000 : ℝ)*X 1 0+(3682662723/10000000000 : ℝ)*X 1 1+(2327535743/5000000000 : ℝ)*X 1 2+(4149156407/10000000000 : ℝ)*X 2 0+(3682662723/10000000000 : ℝ)*X 2 1+(2327535743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1540603387/10000000000 : ℝ)*X 0 0+(5135265261/10000000000 : ℝ)*X 0 1+(2744952307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258217131/10000000000 : ℝ)*X 1 0+(-1370487797/10000000000 : ℝ)*X 1 1+(1372476151/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((657277139/1250000000 : ℝ)*X 2 0+(2744952317/5000000000 : ℝ)*X 2 1+(-1370487781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((207481271/500000000 : ℝ)*X 0 0+(4644517911/10000000000 : ℝ)*X 0 1+(461671939/1250000000 : ℝ)*X 0 2+(207481271/500000000 : ℝ)*X 1 0+(4644517911/10000000000 : ℝ)*X 1 1+(461671939/1250000000 : ℝ)*X 1 2+(207481271/500000000 : ℝ)*X 2 0+(4644517911/10000000000 : ℝ)*X 2 1+(461671939/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1677_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (747383928919627774642719/279687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (103491913/25000000000000 : ℝ)*(base19) + (17109781/5000000000000 : ℝ)*(base23) + (7333029/25000000000000 : ℝ)*(lower2) + (117540983/100000000000000 : ℝ)*(upper3) + (12701073/100000000000000 : ℝ)*(upper5) + (118327657598141/6250000000000 : ℝ)*(major0) + (118327657598141/6250000000000 : ℝ)*(major1) + (118327657598141/6250000000000 : ℝ)*(major2) + (2758106630557887/100000000000000 : ℝ)*(sp0) + (1379053518191859/50000000000000 : ℝ)*(sp1) + (2758107108155751/100000000000000 : ℝ)*(sp2) + (205675091734719/20000000000000 : ℝ)*(sp3) + (204948371/25000000000000 : ℝ)*(sp4) + (2045041849/100000000000000 : ℝ)*(sp7) + (257094375928861/25000000000000 : ℝ)*(f.failure) + (2758107450351371/100000000000000 : ℝ)*(f.sum) + (2569096171149/783125000000000000000000000 : ℝ)*base65 + (77087394308324451/7831250000000000000000000000000 : ℝ)*base67 + (27916580385061951/7831250000000000000000000000000 : ℝ)*base69 + (48915878534261951/7831250000000000000000000000000 : ℝ)*base71 + (5653790546503/1566250000000000000000000000 : ℝ)*base73 + (90291432227730701/7831250000000000000000000000000 : ℝ)*base75 + (24904323511999451/7831250000000000000000000000000 : ℝ)*base77 + (40739987485499451/7831250000000000000000000000000 : ℝ)*base79 + (2536440595457/1566250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1339749/500000000000000000000 : ℝ)*base90 + (1339749/500000000000000000000 : ℝ)*base92 + (1339749/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (422046146532647401186598943/31325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1955462753/100000000000000 : ℝ)*(base19) + (1054244443/50000000000000 : ℝ)*(base23) + (57662663/20000000000000 : ℝ)*(upper3) + (36104687/50000000000000 : ℝ)*(lower4) + (14139403/5000000000000 : ℝ)*(upper5) + (967783159621207/50000000000000 : ℝ)*(major0) + (967783159621207/50000000000000 : ℝ)*(major1) + (967783159621207/50000000000000 : ℝ)*(major2) + (16476348721/100000000000000 : ℝ)*(sp1) + (17882973809/100000000000000 : ℝ)*(sp2) + (704941277606083/25000000000000 : ℝ)*(sp4) + (1409873339306429/50000000000000 : ℝ)*(sp5) + (704936279740409/25000000000000 : ℝ)*(sp6) + (210273415791157/20000000000000 : ℝ)*(sp7) + (210273415791157/20000000000000 : ℝ)*(f.failure) + (704941277606083/25000000000000 : ℝ)*(f.sum) + (6946994357269/3132500000000000000000000000 : ℝ)*base65 + (514791493680725673/62650000000000000000000000000000 : ℝ)*base68 + (268715386340375673/62650000000000000000000000000000 : ℝ)*base70 + (239036634062725673/62650000000000000000000000000000 : ℝ)*base72 + (14158168738537/6265000000000000000000000000 : ℝ)*base74 + (521698028302425673/62650000000000000000000000000000 : ℝ)*base76 + (224944968100575673/62650000000000000000000000000000 : ℝ)*base78 + (474833375993475673/62650000000000000000000000000000 : ℝ)*base80 + (599169138509/195781250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2619587/400000000000000000000 : ℝ)*base89 + (2619587/400000000000000000000 : ℝ)*base91 + (2619587/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1677_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3587/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9661/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17363/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1677_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1677_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9661/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17363/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1677_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1677_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1677_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5031/1024 : ℝ) ≤ p) (hpb : p ≤ (5039/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36819991/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9661/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17363/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1677_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

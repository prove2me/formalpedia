-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1124_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:01.688914+00:00
-- url     : https://prove2.me/submissions/ad2b9bcb-8e07-429c-82a1-e44086ce4c43

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
theorem support_rectangle_w1124_s3_0 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-217151697/1000000000 : ℝ)*x 0 + (1086213471/2000000000 : ℝ)*x 1 + (5230356751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217151697/1000000000 : ℝ)^8317 ≤ (13185374855587/100000000000000 : ℝ)^6269 := by
    have hnat : (217151697 : ℕ)^8317*100000000000000^6269 ≤ 13185374855587^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217151697 1000000000 13185374855587 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086213471/2000000000 : ℝ)^8317 ≤ (11122839466291/25000000000000 : ℝ)^6269 := by
    have hnat : (1086213471 : ℕ)^8317*25000000000000^6269 ≤ 11122839466291^6269*2000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086213471 2000000000 11122839466291 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230356751/10000000000 : ℝ)^8317 ≤ (42323267268997/100000000000000 : ℝ)^6269 := by
    have hnat : (5230356751 : ℕ)^8317*100000000000000^6269 ≤ 42323267268997^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230356751 10000000000 42323267268997 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217151697/1000000000 : ℝ), (1086213471/2000000000 : ℝ), (5230356751/10000000000 : ℝ)] ![(13185374855587/100000000000000 : ℝ), (11122839466291/25000000000000 : ℝ), (42323267268997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217151697/1000000000 : ℝ)|^8317 ≤ (13185374855587/100000000000000 : ℝ)^6269
        have hw : |(-217151697/1000000000 : ℝ)|=(217151697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086213471/2000000000 : ℝ)|^8317 ≤ (11122839466291/25000000000000 : ℝ)^6269
        have hw : |(1086213471/2000000000 : ℝ)|=(1086213471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230356751/10000000000 : ℝ)|^8317 ≤ (42323267268997/100000000000000 : ℝ)^6269
        have hw : |(5230356751/10000000000 : ℝ)|=(5230356751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s3_1 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267711623/500000000 : ℝ)*x 0 + (-1137077309/5000000000 : ℝ)*x 1 + (1307589169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267711623/500000000 : ℝ)^8317 ≤ (43658234270677/100000000000000 : ℝ)^6269 := by
    have hnat : (267711623 : ℕ)^8317*100000000000000^6269 ≤ 43658234270677^6269*500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267711623 500000000 43658234270677 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137077309/5000000000 : ℝ)^8317 ≤ (280369984997/2000000000000 : ℝ)^6269 := by
    have hnat : (1137077309 : ℕ)^8317*2000000000000^6269 ≤ 280369984997^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137077309 5000000000 280369984997 2000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307589169/2500000000 : ℝ)^8317 ≤ (21161633231923/50000000000000 : ℝ)^6269 := by
    have hnat : (1307589169 : ℕ)^8317*50000000000000^6269 ≤ 21161633231923^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307589169 2500000000 21161633231923 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267711623/500000000 : ℝ), (-1137077309/5000000000 : ℝ), (1307589169/2500000000 : ℝ)] ![(43658234270677/100000000000000 : ℝ), (280369984997/2000000000000 : ℝ), (21161633231923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267711623/500000000 : ℝ)|^8317 ≤ (43658234270677/100000000000000 : ℝ)^6269
        have hw : |(267711623/500000000 : ℝ)|=(267711623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1137077309/5000000000 : ℝ)|^8317 ≤ (280369984997/2000000000000 : ℝ)^6269
        have hw : |(-1137077309/5000000000 : ℝ)|=(1137077309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307589169/2500000000 : ℝ)|^8317 ≤ (21161633231923/50000000000000 : ℝ)^6269
        have hw : |(1307589169/2500000000 : ℝ)|=(1307589169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s3_2 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66927907/125000000 : ℝ)*x 0 + (5230356779/10000000000 : ℝ)*x 1 + (-2274154351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66927907/125000000 : ℝ)^8317 ≤ (43658235352453/100000000000000 : ℝ)^6269 := by
    have hnat : (66927907 : ℕ)^8317*100000000000000^6269 ≤ 43658235352453^6269*125000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66927907 125000000 43658235352453 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230356779/10000000000 : ℝ)^8317 ≤ (42323267569587/100000000000000 : ℝ)^6269 := by
    have hnat : (5230356779 : ℕ)^8317*100000000000000^6269 ≤ 42323267569587^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230356779 10000000000 42323267569587 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2274154351/10000000000 : ℝ)^8317 ≤ (14018497066309/100000000000000 : ℝ)^6269 := by
    have hnat : (2274154351 : ℕ)^8317*100000000000000^6269 ≤ 14018497066309^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274154351 10000000000 14018497066309 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66927907/125000000 : ℝ), (5230356779/10000000000 : ℝ), (-2274154351/10000000000 : ℝ)] ![(43658235352453/100000000000000 : ℝ), (42323267569587/100000000000000 : ℝ), (14018497066309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66927907/125000000 : ℝ)|^8317 ≤ (43658235352453/100000000000000 : ℝ)^6269
        have hw : |(66927907/125000000 : ℝ)|=(66927907/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230356779/10000000000 : ℝ)|^8317 ≤ (42323267569587/100000000000000 : ℝ)^6269
        have hw : |(5230356779/10000000000 : ℝ)|=(5230356779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2274154351/10000000000 : ℝ)|^8317 ≤ (14018497066309/100000000000000 : ℝ)^6269
        have hw : |(-2274154351/10000000000 : ℝ)|=(2274154351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s3_3 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364838887/10000000000 : ℝ)*x 0 + (4170413891/10000000000 : ℝ)*x 1 + (22841563/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364838887/10000000000 : ℝ)^8317 ≤ (8323204586351/25000000000000 : ℝ)^6269 := by
    have hnat : (4364838887 : ℕ)^8317*25000000000000^6269 ≤ 8323204586351^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364838887 10000000000 8323204586351 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170413891/10000000000 : ℝ)^8317 ≤ (15669916426677/50000000000000 : ℝ)^6269 := by
    have hnat : (4170413891 : ℕ)^8317*50000000000000^6269 ≤ 15669916426677^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170413891 10000000000 15669916426677 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22841563/50000000 : ℝ)^8317 ≤ (35367348783419/100000000000000 : ℝ)^6269 := by
    have hnat : (22841563 : ℕ)^8317*100000000000000^6269 ≤ 35367348783419^6269*50000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22841563 50000000 35367348783419 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364838887/10000000000 : ℝ), (4170413891/10000000000 : ℝ), (22841563/50000000 : ℝ)] ![(8323204586351/25000000000000 : ℝ), (15669916426677/50000000000000 : ℝ), (35367348783419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364838887/10000000000 : ℝ)|^8317 ≤ (8323204586351/25000000000000 : ℝ)^6269
        have hw : |(4364838887/10000000000 : ℝ)|=(4364838887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170413891/10000000000 : ℝ)|^8317 ≤ (15669916426677/50000000000000 : ℝ)^6269
        have hw : |(4170413891/10000000000 : ℝ)|=(4170413891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22841563/50000000 : ℝ)|^8317 ≤ (35367348783419/100000000000000 : ℝ)^6269
        have hw : |(22841563/50000000 : ℝ)|=(22841563/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s3_4 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085767959/5000000000 : ℝ)*x 0 + (5231145587/10000000000 : ℝ)*x 1 + (33939213/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085767959/5000000000 : ℝ)^8317 ≤ (329638187331/2500000000000 : ℝ)^6269 := by
    have hnat : (1085767959 : ℕ)^8317*2500000000000^6269 ≤ 329638187331^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085767959 5000000000 329638187331 2500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231145587/10000000000 : ℝ)^8317 ≤ (21165867955041/50000000000000 : ℝ)^6269 := by
    have hnat : (5231145587 : ℕ)^8317*50000000000000^6269 ≤ 21165867955041^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231145587 10000000000 21165867955041 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33939213/62500000 : ℝ)^8317 ≤ (44482736574071/100000000000000 : ℝ)^6269 := by
    have hnat : (33939213 : ℕ)^8317*100000000000000^6269 ≤ 44482736574071^6269*62500000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33939213 62500000 44482736574071 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085767959/5000000000 : ℝ), (5231145587/10000000000 : ℝ), (33939213/62500000 : ℝ)] ![(329638187331/2500000000000 : ℝ), (21165867955041/50000000000000 : ℝ), (44482736574071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085767959/5000000000 : ℝ)|^8317 ≤ (329638187331/2500000000000 : ℝ)^6269
        have hw : |(-1085767959/5000000000 : ℝ)|=(1085767959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231145587/10000000000 : ℝ)|^8317 ≤ (21165867955041/50000000000000 : ℝ)^6269
        have hw : |(5231145587/10000000000 : ℝ)|=(5231145587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33939213/62500000 : ℝ)|^8317 ≤ (44482736574071/100000000000000 : ℝ)^6269
        have hw : |(33939213/62500000 : ℝ)|=(33939213/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s3_5 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325862659/2500000000 : ℝ)*x 0 + (-518559281/2500000000 : ℝ)*x 1 + (2715137091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325862659/2500000000 : ℝ)^8317 ≤ (8621948303763/20000000000000 : ℝ)^6269 := by
    have hnat : (1325862659 : ℕ)^8317*20000000000000^6269 ≤ 8621948303763^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325862659 2500000000 8621948303763 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518559281/2500000000 : ℝ)^8317 ≤ (620376039267/5000000000000 : ℝ)^6269 := by
    have hnat : (518559281 : ℕ)^8317*5000000000000^6269 ≤ 620376039267^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518559281 2500000000 620376039267 5000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715137091/5000000000 : ℝ)^8317 ≤ (22241368841289/50000000000000 : ℝ)^6269 := by
    have hnat : (2715137091 : ℕ)^8317*50000000000000^6269 ≤ 22241368841289^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715137091 5000000000 22241368841289 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325862659/2500000000 : ℝ), (-518559281/2500000000 : ℝ), (2715137091/5000000000 : ℝ)] ![(8621948303763/20000000000000 : ℝ), (620376039267/5000000000000 : ℝ), (22241368841289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325862659/2500000000 : ℝ)|^8317 ≤ (8621948303763/20000000000000 : ℝ)^6269
        have hw : |(1325862659/2500000000 : ℝ)|=(1325862659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-518559281/2500000000 : ℝ)|^8317 ≤ (620376039267/5000000000000 : ℝ)^6269
        have hw : |(-518559281/2500000000 : ℝ)|=(518559281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715137091/5000000000 : ℝ)|^8317 ≤ (22241368841289/50000000000000 : ℝ)^6269
        have hw : |(2715137091/5000000000 : ℝ)|=(2715137091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s3_6 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (662931327/1250000000 : ℝ)*x 0 + (84848033/156250000 : ℝ)*x 1 + (-2074237247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662931327/1250000000 : ℝ)^8317 ≤ (43109741303133/100000000000000 : ℝ)^6269 := by
    have hnat : (662931327 : ℕ)^8317*100000000000000^6269 ≤ 43109741303133^6269*1250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662931327 1250000000 43109741303133 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84848033/156250000 : ℝ)^8317 ≤ (22241368460919/50000000000000 : ℝ)^6269 := by
    have hnat : (84848033 : ℕ)^8317*50000000000000^6269 ≤ 22241368460919^6269*156250000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84848033 156250000 22241368460919 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074237247/10000000000 : ℝ)^8317 ≤ (12407521761453/100000000000000 : ℝ)^6269 := by
    have hnat : (2074237247 : ℕ)^8317*100000000000000^6269 ≤ 12407521761453^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074237247 10000000000 12407521761453 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662931327/1250000000 : ℝ), (84848033/156250000 : ℝ), (-2074237247/10000000000 : ℝ)] ![(43109741303133/100000000000000 : ℝ), (22241368460919/50000000000000 : ℝ), (12407521761453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662931327/1250000000 : ℝ)|^8317 ≤ (43109741303133/100000000000000 : ℝ)^6269
        have hw : |(662931327/1250000000 : ℝ)|=(662931327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84848033/156250000 : ℝ)|^8317 ≤ (22241368460919/50000000000000 : ℝ)^6269
        have hw : |(84848033/156250000 : ℝ)|=(84848033/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074237247/10000000000 : ℝ)|^8317 ≤ (12407521761453/100000000000000 : ℝ)^6269
        have hw : |(-2074237247/10000000000 : ℝ)|=(2074237247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s3_7 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364876411/10000000000 : ℝ)*x 0 + (2283374617/5000000000 : ℝ)*x 1 + (166879449/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364876411/10000000000 : ℝ)^8317 ≤ (1040412439463/3125000000000 : ℝ)^6269 := by
    have hnat : (4364876411 : ℕ)^8317*3125000000000^6269 ≤ 1040412439463^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364876411 10000000000 1040412439463 3125000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2283374617/5000000000 : ℝ)^8317 ≤ (35351292260399/100000000000000 : ℝ)^6269 := by
    have hnat : (2283374617 : ℕ)^8317*100000000000000^6269 ≤ 35351292260399^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283374617 5000000000 35351292260399 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166879449/400000000 : ℝ)^8317 ≤ (1567775482811/5000000000000 : ℝ)^6269 := by
    have hnat : (166879449 : ℕ)^8317*5000000000000^6269 ≤ 1567775482811^6269*400000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166879449 400000000 1567775482811 5000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364876411/10000000000 : ℝ), (2283374617/5000000000 : ℝ), (166879449/400000000 : ℝ)] ![(1040412439463/3125000000000 : ℝ), (35351292260399/100000000000000 : ℝ), (1567775482811/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364876411/10000000000 : ℝ)|^8317 ≤ (1040412439463/3125000000000 : ℝ)^6269
        have hw : |(4364876411/10000000000 : ℝ)|=(4364876411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2283374617/5000000000 : ℝ)|^8317 ≤ (35351292260399/100000000000000 : ℝ)^6269
        have hw : |(2283374617/5000000000 : ℝ)|=(2283374617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166879449/400000000 : ℝ)|^8317 ≤ (1567775482811/5000000000000 : ℝ)^6269
        have hw : |(166879449/400000000 : ℝ)|=(166879449/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1124_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10581/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3707/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16557/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2247/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16557/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2247/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16557/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2247/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16557/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2247/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16557/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2247/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16557/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2247/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2247/25000 : ℝ) ^ (2079/512 : ℝ) ≤ (5640269079495617/100000000000000000000 : ℝ) := by
    have hpowers : (2247/25000 : ℝ)^2079 ≤ (5640269079495617/100000000000000000000 : ℝ)^512 := by
      have hnat : (2247 : ℕ)^2079*100000000000000000000^512 ≤ 5640269079495617^512*25000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2247 25000 5640269079495617 100000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2247/25000 : ℝ)) (X := (5640269079495617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16557/100000 : ℝ) ^ (2079/512 : ℝ) ≤ (2106145625348531/3125000000000000000 : ℝ) := by
    have hpowers : (16557/100000 : ℝ)^2079 ≤ (2106145625348531/3125000000000000000 : ℝ)^512 := by
      have hnat : (16557 : ℕ)^2079*3125000000000000000^512 ≤ 2106145625348531^512*100000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16557 100000 2106145625348531 3125000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16557/100000 : ℝ)) (X := (2106145625348531/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005640269079495617/50000000000000000000 : ℝ) ≤ (1250034724567209/1250000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50005640269079495617/50000000000000000000 : ℝ)^512 ≤ (1250034724567209/1250000000000000 : ℝ)^2079 := by
      have hnat : (50005640269079495617 : ℕ)^512*1250000000000000^2079 ≤ 1250034724567209^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005640269079495617 50000000000000000000 1250034724567209 1250000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250034724567209/1250000000000000 : ℝ)) (X := (50005640269079495617/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100073036929090648609/100000000000000000000 : ℝ) ≤ (10001798201979119/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (100073036929090648609/100000000000000000000 : ℝ)^512 ≤ (10001798201979119/10000000000000000 : ℝ)^2079 := by
      have hnat : (100073036929090648609 : ℕ)^512*10000000000000000^2079 ≤ 10001798201979119^2079*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100073036929090648609 100000000000000000000 10001798201979119 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001798201979119/10000000000000000 : ℝ)) (X := (100073036929090648609/100000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1564606145625348531/1562500000000000000 : ℝ) ≤ (5001659303710283/5000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (1564606145625348531/1562500000000000000 : ℝ)^512 ≤ (5001659303710283/5000000000000000 : ℝ)^2079 := by
      have hnat : (1564606145625348531 : ℕ)^512*5000000000000000^2079 ≤ 5001659303710283^2079*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1564606145625348531 1562500000000000000 5001659303710283 5000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001659303710283/5000000000000000 : ℝ)) (X := (1564606145625348531/1562500000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5640269079495617/100000000000000000000 : ℝ) ≤ ((13589219079342347/13593750000000000 : ℝ)+2*(52427773843/26100000000000 : ℝ)*(2247/25000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (13589219079342347/13593750000000000 : ℝ)+2*(52427773843/26100000000000 : ℝ)*(2247/25000 : ℝ)=(1250034724567209/1250000000000000 : ℝ) by norm_num, show 1+2*(5640269079495617/100000000000000000000 : ℝ)=(50005640269079495617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2106145625348531/3125000000000000000 : ℝ)+(5640269079495617/100000000000000000000 : ℝ) ≤ ((13589219079342347/13593750000000000 : ℝ)+(52427773843/26100000000000 : ℝ)*((16557/100000 : ℝ)+(2247/25000 : ℝ)))^(2079/512 : ℝ) := by
    rw [show (13589219079342347/13593750000000000 : ℝ)+(52427773843/26100000000000 : ℝ)*((16557/100000 : ℝ)+(2247/25000 : ℝ))=(10001798201979119/10000000000000000 : ℝ) by norm_num, show 1+(2106145625348531/3125000000000000000 : ℝ)+(5640269079495617/100000000000000000000 : ℝ)=(100073036929090648609/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2106145625348531/3125000000000000000 : ℝ) ≤ ((13589219079342347/13593750000000000 : ℝ)+2*(52427773843/26100000000000 : ℝ)*(16557/100000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (13589219079342347/13593750000000000 : ℝ)+2*(52427773843/26100000000000 : ℝ)*(16557/100000 : ℝ)=(5001659303710283/5000000000000000 : ℝ) by norm_num, show 1+2*(2106145625348531/3125000000000000000 : ℝ)=(1564606145625348531/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13589219079342347/13593750000000000 : ℝ)*(X 1 0+X 2 0)+(52427773843/26100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (2247/25000 : ℝ)) (hi := (16557/100000 : ℝ)) (c := (13589219079342347/13593750000000000 : ℝ)) (alpha := (52427773843/26100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13589219079342347/13593750000000000 : ℝ)*(X 0 1+X 2 1)+(52427773843/26100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (2247/25000 : ℝ)) (hi := (16557/100000 : ℝ)) (c := (13589219079342347/13593750000000000 : ℝ)) (alpha := (52427773843/26100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13589219079342347/13593750000000000 : ℝ)*(X 0 2+X 1 2)+(52427773843/26100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (2247/25000 : ℝ)) (hi := (16557/100000 : ℝ)) (c := (13589219079342347/13593750000000000 : ℝ)) (alpha := (52427773843/26100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-217151697/1000000000 : ℝ)*X 0 0+(1086213471/2000000000 : ℝ)*X 0 1+(5230356751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267711623/500000000 : ℝ)*X 1 0+(-1137077309/5000000000 : ℝ)*X 1 1+(1307589169/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66927907/125000000 : ℝ)*X 2 0+(5230356779/10000000000 : ℝ)*X 2 1+(-2274154351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364838887/10000000000 : ℝ)*X 0 0+(4170413891/10000000000 : ℝ)*X 0 1+(22841563/50000000 : ℝ)*X 0 2+(4364838887/10000000000 : ℝ)*X 1 0+(4170413891/10000000000 : ℝ)*X 1 1+(22841563/50000000 : ℝ)*X 1 2+(4364838887/10000000000 : ℝ)*X 2 0+(4170413891/10000000000 : ℝ)*X 2 1+(22841563/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1085767959/5000000000 : ℝ)*X 0 0+(5231145587/10000000000 : ℝ)*X 0 1+(33939213/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325862659/2500000000 : ℝ)*X 1 0+(-518559281/2500000000 : ℝ)*X 1 1+(2715137091/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662931327/1250000000 : ℝ)*X 2 0+(84848033/156250000 : ℝ)*X 2 1+(-2074237247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364876411/10000000000 : ℝ)*X 0 0+(2283374617/5000000000 : ℝ)*X 0 1+(166879449/400000000 : ℝ)*X 0 2+(4364876411/10000000000 : ℝ)*X 1 0+(2283374617/5000000000 : ℝ)*X 1 1+(166879449/400000000 : ℝ)*X 1 2+(4364876411/10000000000 : ℝ)*X 2 0+(2283374617/5000000000 : ℝ)*X 2 1+(166879449/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20801012052989511242309/7812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (957814233/100000000000000 : ℝ)*(base19) + (183534133/20000000000000 : ℝ)*(base23) + (75984883/100000000000000 : ℝ)*(lower2) + (151178221/100000000000000 : ℝ)*(upper5) + (1873888074786003/50000000000000 : ℝ)*(major0) + (1873888074786003/50000000000000 : ℝ)*(major1) + (1873888074786003/50000000000000 : ℝ)*(major2) + (124557817011007/2500000000000 : ℝ)*(sp0) + (2491166352542947/50000000000000 : ℝ)*(sp1) + (4982333664406289/100000000000000 : ℝ)*(sp2) + (628302643025211/25000000000000 : ℝ)*(sp3) + (10950818337/50000000000000 : ℝ)*(sp4) + (229794207/25000000000000 : ℝ)*(sp5) + (7056215217/100000000000000 : ℝ)*(sp7) + (125660881415803/5000000000000 : ℝ)*(f.failure) + (2491167291038477/50000000000000 : ℝ)*(f.sum) + (1677899160419/435000000000000000000000000 : ℝ)*base66 + (9724875292609957/1359375000000000000000000000000 : ℝ)*base67 + (4710713992906541/679687500000000000000000000000 : ℝ)*base69 + (756308231222729/169921875000000000000000000000 : ℝ)*base71 + (146050031143/54375000000000000000000000 : ℝ)*base74 + (772626062405959/679687500000000000000000000000 : ℝ)*base76 + (111057939004901/42480468750000000000000000000 : ℝ)*base77 + (6443481786219041/679687500000000000000000000000 : ℝ)*base79 + (2857024783/3398437500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7325519/500000000000000000000 : ℝ)*base90 + (7325519/500000000000000000000 : ℝ)*base92 + (7325519/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6181704419708091612525713/679687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (348555403/20000000000000 : ℝ)*(base19) + (976895301/50000000000000 : ℝ)*(base23) + (207653413/100000000000000 : ℝ)*(upper3) + (113002169/100000000000000 : ℝ)*(lower4) + (162882341/100000000000000 : ℝ)*(upper5) + (472190310942227/12500000000000 : ℝ)*(major0) + (472190310942227/12500000000000 : ℝ)*(major1) + (472190310942227/12500000000000 : ℝ)*(major2) + (2000734839/6250000000000 : ℝ)*(sp1) + (33774434567/100000000000000 : ℝ)*(sp2) + (1255469868808081/25000000000000 : ℝ)*(sp4) + (1004369144139577/20000000000000 : ℝ)*(sp5) + (1255460936751789/25000000000000 : ℝ)*(sp6) + (2533165196679251/100000000000000 : ℝ)*(sp7) + (2533165196679251/100000000000000 : ℝ)*(f.failure) + (1255469868808081/25000000000000 : ℝ)*(f.sum) + (5735680825543/1305000000000000000000000000 : ℝ)*base65 + (13747006335969353/2039062500000000000000000000000 : ℝ)*base67 + (31661931977360581/4078125000000000000000000000000 : ℝ)*base69 + (45516314948829331/4078125000000000000000000000000 : ℝ)*base71 + (3164419144261/652500000000000000000000000 : ℝ)*base74 + (72226609992766831/4078125000000000000000000000000 : ℝ)*base75 + (20025767361733169/4078125000000000000000000000000 : ℝ)*base78 + (53538668531360581/4078125000000000000000000000000 : ℝ)*base79 + (260435245771/652500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14487623/10000000000000000000000 : ℝ)*base90 + (14487623/10000000000000000000000 : ℝ)*base92 + (14487623/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1124_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3707/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1124_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1124_s4_0 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087333071/5000000000 : ℝ)*x 0 + (5402773047/10000000000 : ℝ)*x 1 + (5256591767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087333071/5000000000 : ℝ)^8317 ≤ (1321074932081/10000000000000 : ℝ)^6269 := by
    have hnat : (1087333071 : ℕ)^8317*10000000000000^6269 ≤ 1321074932081^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087333071 5000000000 1321074932081 10000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402773047/10000000000 : ℝ)^8317 ≤ (44184110748069/100000000000000 : ℝ)^6269 := by
    have hnat : (5402773047 : ℕ)^8317*100000000000000^6269 ≤ 44184110748069^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402773047 10000000000 44184110748069 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256591767/10000000000 : ℝ)^8317 ≤ (2130256995331/5000000000000 : ℝ)^6269 := by
    have hnat : (5256591767 : ℕ)^8317*5000000000000^6269 ≤ 2130256995331^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256591767 10000000000 2130256995331 5000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087333071/5000000000 : ℝ), (5402773047/10000000000 : ℝ), (5256591767/10000000000 : ℝ)] ![(1321074932081/10000000000000 : ℝ), (44184110748069/100000000000000 : ℝ), (2130256995331/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087333071/5000000000 : ℝ)|^8317 ≤ (1321074932081/10000000000000 : ℝ)^6269
        have hw : |(-1087333071/5000000000 : ℝ)|=(1087333071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402773047/10000000000 : ℝ)|^8317 ≤ (44184110748069/100000000000000 : ℝ)^6269
        have hw : |(5402773047/10000000000 : ℝ)|=(5402773047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256591767/10000000000 : ℝ)|^8317 ≤ (2130256995331/5000000000000 : ℝ)^6269
        have hw : |(5256591767/10000000000 : ℝ)|=(5256591767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s4_1 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336794931/2500000000 : ℝ)*x 0 + (-2248968969/10000000000 : ℝ)*x 1 + (5256591861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336794931/2500000000 : ℝ)^8317 ≤ (21790977939899/50000000000000 : ℝ)^6269 := by
    have hnat : (1336794931 : ℕ)^8317*50000000000000^6269 ≤ 21790977939899^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336794931 2500000000 21790977939899 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248968969/10000000000 : ℝ)^8317 ≤ (2762580636487/20000000000000 : ℝ)^6269 := by
    have hnat : (2248968969 : ℕ)^8317*20000000000000^6269 ≤ 2762580636487^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248968969 10000000000 2762580636487 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256591861/10000000000 : ℝ)^8317 ≤ (21302570458697/50000000000000 : ℝ)^6269 := by
    have hnat : (5256591861 : ℕ)^8317*50000000000000^6269 ≤ 21302570458697^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256591861 10000000000 21302570458697 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336794931/2500000000 : ℝ), (-2248968969/10000000000 : ℝ), (5256591861/10000000000 : ℝ)] ![(21790977939899/50000000000000 : ℝ), (2762580636487/20000000000000 : ℝ), (21302570458697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336794931/2500000000 : ℝ)|^8317 ≤ (21790977939899/50000000000000 : ℝ)^6269
        have hw : |(1336794931/2500000000 : ℝ)|=(1336794931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2248968969/10000000000 : ℝ)|^8317 ≤ (2762580636487/20000000000000 : ℝ)^6269
        have hw : |(-2248968969/10000000000 : ℝ)|=(2248968969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256591861/10000000000 : ℝ)|^8317 ≤ (21302570458697/50000000000000 : ℝ)^6269
        have hw : |(5256591861/10000000000 : ℝ)|=(5256591861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s4_2 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673590103/5000000000 : ℝ)*x 0 + (5256591369/10000000000 : ℝ)*x 1 + (-2248968979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673590103/5000000000 : ℝ)^8317 ≤ (21790980545857/50000000000000 : ℝ)^6269 := by
    have hnat : (2673590103 : ℕ)^8317*50000000000000^6269 ≤ 21790980545857^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673590103 5000000000 21790980545857 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256591369/10000000000 : ℝ)^8317 ≤ (532564195337/1250000000000 : ℝ)^6269 := by
    have hnat : (5256591369 : ℕ)^8317*1250000000000^6269 ≤ 532564195337^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256591369 10000000000 532564195337 1250000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248968979/10000000000 : ℝ)^8317 ≤ (6906451631959/50000000000000 : ℝ)^6269 := by
    have hnat : (2248968979 : ℕ)^8317*50000000000000^6269 ≤ 6906451631959^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248968979 10000000000 6906451631959 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673590103/5000000000 : ℝ), (5256591369/10000000000 : ℝ), (-2248968979/10000000000 : ℝ)] ![(21790980545857/50000000000000 : ℝ), (532564195337/1250000000000 : ℝ), (6906451631959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673590103/5000000000 : ℝ)|^8317 ≤ (21790980545857/50000000000000 : ℝ)^6269
        have hw : |(2673590103/5000000000 : ℝ)|=(2673590103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256591369/10000000000 : ℝ)|^8317 ≤ (532564195337/1250000000000 : ℝ)^6269
        have hw : |(5256591369/10000000000 : ℝ)|=(5256591369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2248968979/10000000000 : ℝ)|^8317 ≤ (6906451631959/50000000000000 : ℝ)^6269
        have hw : |(-2248968979/10000000000 : ℝ)|=(2248968979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s4_3 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218335889/500000000 : ℝ)*x 0 + (264013739/625000000 : ℝ)*x 1 + (4514018191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218335889/500000000 : ℝ)^8317 ≤ (3331183277737/10000000000000 : ℝ)^6269 := by
    have hnat : (218335889 : ℕ)^8317*10000000000000^6269 ≤ 3331183277737^6269*500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218335889 500000000 3331183277737 10000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264013739/625000000 : ℝ)^8317 ≤ (31877393869551/100000000000000 : ℝ)^6269 := by
    have hnat : (264013739 : ℕ)^8317*100000000000000^6269 ≤ 31877393869551^6269*625000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264013739 625000000 31877393869551 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514018191/10000000000 : ℝ)^8317 ≤ (8702693336299/25000000000000 : ℝ)^6269 := by
    have hnat : (4514018191 : ℕ)^8317*25000000000000^6269 ≤ 8702693336299^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514018191 10000000000 8702693336299 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218335889/500000000 : ℝ), (264013739/625000000 : ℝ), (4514018191/10000000000 : ℝ)] ![(3331183277737/10000000000000 : ℝ), (31877393869551/100000000000000 : ℝ), (8702693336299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218335889/500000000 : ℝ)|^8317 ≤ (3331183277737/10000000000000 : ℝ)^6269
        have hw : |(218335889/500000000 : ℝ)|=(218335889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264013739/625000000 : ℝ)|^8317 ≤ (31877393869551/100000000000000 : ℝ)^6269
        have hw : |(264013739/625000000 : ℝ)|=(264013739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514018191/10000000000 : ℝ)|^8317 ≤ (8702693336299/25000000000000 : ℝ)^6269
        have hw : |(4514018191/10000000000 : ℝ)|=(4514018191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s4_4 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-543668493/2500000000 : ℝ)*x 0 + (5257010561/10000000000 : ℝ)*x 1 + (5402352163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543668493/2500000000 : ℝ)^8317 ≤ (6605406213017/50000000000000 : ℝ)^6269 := by
    have hnat : (543668493 : ℕ)^8317*50000000000000^6269 ≤ 6605406213017^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543668493 2500000000 6605406213017 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257010561/10000000000 : ℝ)^8317 ≤ (8521928644227/20000000000000 : ℝ)^6269 := by
    have hnat : (5257010561 : ℕ)^8317*20000000000000^6269 ≤ 8521928644227^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257010561 10000000000 8521928644227 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402352163/10000000000 : ℝ)^8317 ≤ (22089772170017/50000000000000 : ℝ)^6269 := by
    have hnat : (5402352163 : ℕ)^8317*50000000000000^6269 ≤ 22089772170017^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402352163 10000000000 22089772170017 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543668493/2500000000 : ℝ), (5257010561/10000000000 : ℝ), (5402352163/10000000000 : ℝ)] ![(6605406213017/50000000000000 : ℝ), (8521928644227/20000000000000 : ℝ), (22089772170017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543668493/2500000000 : ℝ)|^8317 ≤ (6605406213017/50000000000000 : ℝ)^6269
        have hw : |(-543668493/2500000000 : ℝ)|=(543668493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257010561/10000000000 : ℝ)|^8317 ≤ (8521928644227/20000000000000 : ℝ)^6269
        have hw : |(5257010561/10000000000 : ℝ)|=(5257010561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402352163/10000000000 : ℝ)|^8317 ≤ (22089772170017/50000000000000 : ℝ)^6269
        have hw : |(5402352163/10000000000 : ℝ)|=(5402352163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s4_5 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132754903/250000000 : ℝ)*x 0 + (-2103208131/10000000000 : ℝ)*x 1 + (540235223/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132754903/250000000 : ℝ)^8317 ≤ (5397812604797/12500000000000 : ℝ)^6269 := by
    have hnat : (132754903 : ℕ)^8317*12500000000000^6269 ≤ 5397812604797^6269*250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132754903 250000000 5397812604797 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2103208131/10000000000 : ℝ)^8317 ≤ (394936065073/3125000000000 : ℝ)^6269 := by
    have hnat : (2103208131 : ℕ)^8317*3125000000000^6269 ≤ 394936065073^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103208131 10000000000 394936065073 3125000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540235223/1000000000 : ℝ)^8317 ≤ (8835909013389/20000000000000 : ℝ)^6269 := by
    have hnat : (540235223 : ℕ)^8317*20000000000000^6269 ≤ 8835909013389^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540235223 1000000000 8835909013389 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132754903/250000000 : ℝ), (-2103208131/10000000000 : ℝ), (540235223/1000000000 : ℝ)] ![(5397812604797/12500000000000 : ℝ), (394936065073/3125000000000 : ℝ), (8835909013389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132754903/250000000 : ℝ)|^8317 ≤ (5397812604797/12500000000000 : ℝ)^6269
        have hw : |(132754903/250000000 : ℝ)|=(132754903/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2103208131/10000000000 : ℝ)|^8317 ≤ (394936065073/3125000000000 : ℝ)^6269
        have hw : |(-2103208131/10000000000 : ℝ)|=(2103208131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540235223/1000000000 : ℝ)|^8317 ≤ (8835909013389/20000000000000 : ℝ)^6269
        have hw : |(540235223/1000000000 : ℝ)|=(540235223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s4_6 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310196167/10000000000 : ℝ)*x 0 + (2701176129/5000000000 : ℝ)*x 1 + (-525802007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310196167/10000000000 : ℝ)^8317 ≤ (43182501345441/100000000000000 : ℝ)^6269 := by
    have hnat : (5310196167 : ℕ)^8317*100000000000000^6269 ≤ 43182501345441^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310196167 10000000000 43182501345441 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701176129/5000000000 : ℝ)^8317 ≤ (44179545370729/100000000000000 : ℝ)^6269 := by
    have hnat : (2701176129 : ℕ)^8317*100000000000000^6269 ≤ 44179545370729^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701176129 5000000000 44179545370729 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525802007/2500000000 : ℝ)^8317 ≤ (3159488315307/25000000000000 : ℝ)^6269 := by
    have hnat : (525802007 : ℕ)^8317*25000000000000^6269 ≤ 3159488315307^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525802007 2500000000 3159488315307 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310196167/10000000000 : ℝ), (2701176129/5000000000 : ℝ), (-525802007/2500000000 : ℝ)] ![(43182501345441/100000000000000 : ℝ), (44179545370729/100000000000000 : ℝ), (3159488315307/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310196167/10000000000 : ℝ)|^8317 ≤ (43182501345441/100000000000000 : ℝ)^6269
        have hw : |(5310196167/10000000000 : ℝ)|=(5310196167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701176129/5000000000 : ℝ)|^8317 ≤ (44179545370729/100000000000000 : ℝ)^6269
        have hw : |(2701176129/5000000000 : ℝ)|=(2701176129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525802007/2500000000 : ℝ)|^8317 ≤ (3159488315307/25000000000000 : ℝ)^6269
        have hw : |(-525802007/2500000000 : ℝ)|=(525802007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s4_7 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436673241/1000000000 : ℝ)*x 0 + (225659357/500000000 : ℝ)*x 1 + (4225054243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436673241/1000000000 : ℝ)^8317 ≤ (33311980843729/100000000000000 : ℝ)^6269 := by
    have hnat : (436673241 : ℕ)^8317*100000000000000^6269 ≤ 33311980843729^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436673241 1000000000 33311980843729 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225659357/500000000 : ℝ)^8317 ≤ (2175141944009/6250000000000 : ℝ)^6269 := by
    have hnat : (225659357 : ℕ)^8317*6250000000000^6269 ≤ 2175141944009^6269*500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225659357 500000000 2175141944009 6250000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225054243/10000000000 : ℝ)^8317 ≤ (15942874016099/50000000000000 : ℝ)^6269 := by
    have hnat : (4225054243 : ℕ)^8317*50000000000000^6269 ≤ 15942874016099^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225054243 10000000000 15942874016099 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436673241/1000000000 : ℝ), (225659357/500000000 : ℝ), (4225054243/10000000000 : ℝ)] ![(33311980843729/100000000000000 : ℝ), (2175141944009/6250000000000 : ℝ), (15942874016099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436673241/1000000000 : ℝ)|^8317 ≤ (33311980843729/100000000000000 : ℝ)^6269
        have hw : |(436673241/1000000000 : ℝ)|=(436673241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225659357/500000000 : ℝ)|^8317 ≤ (2175141944009/6250000000000 : ℝ)^6269
        have hw : |(225659357/500000000 : ℝ)|=(225659357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225054243/10000000000 : ℝ)|^8317 ≤ (15942874016099/50000000000000 : ℝ)^6269
        have hw : |(4225054243/10000000000 : ℝ)|=(4225054243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1124_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3707/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11141/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3707/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10581/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3707/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10581/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3707/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10581/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3707/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10581/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3707/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10581/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3707/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10581/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10581/100000 : ℝ) ^ (2079/512 : ℝ) ≤ (5470348600025747/50000000000000000000 : ℝ) := by
    have hpowers : (10581/100000 : ℝ)^2079 ≤ (5470348600025747/50000000000000000000 : ℝ)^512 := by
      have hnat : (10581 : ℕ)^2079*50000000000000000000^512 ≤ 5470348600025747^512*100000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10581 100000 5470348600025747 50000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10581/100000 : ℝ)) (X := (5470348600025747/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3707/25000 : ℝ) ^ (2079/512 : ℝ) ≤ (43066735181238619/100000000000000000000 : ℝ) := by
    have hpowers : (3707/25000 : ℝ)^2079 ≤ (43066735181238619/100000000000000000000 : ℝ)^512 := by
      have hnat : (3707 : ℕ)^2079*100000000000000000000^512 ≤ 43066735181238619^512*25000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3707 25000 43066735181238619 100000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3707/25000 : ℝ)) (X := (43066735181238619/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005470348600025747/25000000000000000000 : ℝ) ≤ (2500134708395799/2500000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (25005470348600025747/25000000000000000000 : ℝ)^512 ≤ (2500134708395799/2500000000000000 : ℝ)^2079 := by
      have hnat : (25005470348600025747 : ℕ)^512*2500000000000000^2079 ≤ 2500134708395799^2079*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005470348600025747 25000000000000000000 2500134708395799 2500000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134708395799/2500000000000000 : ℝ)) (X := (25005470348600025747/25000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054007432381290113/100000000000000000000 : ℝ) ≤ (10001329782542519/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (100054007432381290113/100000000000000000000 : ℝ)^512 ≤ (10001329782542519/10000000000000000 : ℝ)^2079 := by
      have hnat : (100054007432381290113 : ℕ)^512*10000000000000000^2079 ≤ 10001329782542519^2079*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054007432381290113 100000000000000000000 10001329782542519 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001329782542519/10000000000000000 : ℝ)) (X := (100054007432381290113/100000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043066735181238619/50000000000000000000 : ℝ) ≤ (5001060365750921/5000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50043066735181238619/50000000000000000000 : ℝ)^512 ≤ (5001060365750921/5000000000000000 : ℝ)^2079 := by
      have hnat : (50043066735181238619 : ℕ)^512*5000000000000000^2079 ≤ 5001060365750921^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043066735181238619 50000000000000000000 5001060365750921 5000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001060365750921/5000000000000000 : ℝ)) (X := (50043066735181238619/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5470348600025747/50000000000000000000 : ℝ) ≤ ((21227775182175320043/21235000000000000000 : ℝ)+2*(790948959323/424700000000000 : ℝ)*(10581/100000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (21227775182175320043/21235000000000000000 : ℝ)+2*(790948959323/424700000000000 : ℝ)*(10581/100000 : ℝ)=(2500134708395799/2500000000000000 : ℝ) by norm_num, show 1+2*(5470348600025747/50000000000000000000 : ℝ)=(25005470348600025747/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43066735181238619/100000000000000000000 : ℝ)+(5470348600025747/50000000000000000000 : ℝ) ≤ ((21227775182175320043/21235000000000000000 : ℝ)+(790948959323/424700000000000 : ℝ)*((3707/25000 : ℝ)+(10581/100000 : ℝ)))^(2079/512 : ℝ) := by
    rw [show (21227775182175320043/21235000000000000000 : ℝ)+(790948959323/424700000000000 : ℝ)*((3707/25000 : ℝ)+(10581/100000 : ℝ))=(10001329782542519/10000000000000000 : ℝ) by norm_num, show 1+(43066735181238619/100000000000000000000 : ℝ)+(5470348600025747/50000000000000000000 : ℝ)=(100054007432381290113/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43066735181238619/100000000000000000000 : ℝ) ≤ ((21227775182175320043/21235000000000000000 : ℝ)+2*(790948959323/424700000000000 : ℝ)*(3707/25000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (21227775182175320043/21235000000000000000 : ℝ)+2*(790948959323/424700000000000 : ℝ)*(3707/25000 : ℝ)=(5001060365750921/5000000000000000 : ℝ) by norm_num, show 1+2*(43066735181238619/100000000000000000000 : ℝ)=(50043066735181238619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21227775182175320043/21235000000000000000 : ℝ)*(X 1 0+X 2 0)+(790948959323/424700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (10581/100000 : ℝ)) (hi := (3707/25000 : ℝ)) (c := (21227775182175320043/21235000000000000000 : ℝ)) (alpha := (790948959323/424700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21227775182175320043/21235000000000000000 : ℝ)*(X 0 1+X 2 1)+(790948959323/424700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (10581/100000 : ℝ)) (hi := (3707/25000 : ℝ)) (c := (21227775182175320043/21235000000000000000 : ℝ)) (alpha := (790948959323/424700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21227775182175320043/21235000000000000000 : ℝ)*(X 0 2+X 1 2)+(790948959323/424700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (10581/100000 : ℝ)) (hi := (3707/25000 : ℝ)) (c := (21227775182175320043/21235000000000000000 : ℝ)) (alpha := (790948959323/424700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1087333071/5000000000 : ℝ)*X 0 0+(5402773047/10000000000 : ℝ)*X 0 1+(5256591767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336794931/2500000000 : ℝ)*X 1 0+(-2248968969/10000000000 : ℝ)*X 1 1+(5256591861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673590103/5000000000 : ℝ)*X 2 0+(5256591369/10000000000 : ℝ)*X 2 1+(-2248968979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218335889/500000000 : ℝ)*X 0 0+(264013739/625000000 : ℝ)*X 0 1+(4514018191/10000000000 : ℝ)*X 0 2+(218335889/500000000 : ℝ)*X 1 0+(264013739/625000000 : ℝ)*X 1 1+(4514018191/10000000000 : ℝ)*X 1 2+(218335889/500000000 : ℝ)*X 2 0+(264013739/625000000 : ℝ)*X 2 1+(4514018191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-543668493/2500000000 : ℝ)*X 0 0+(5257010561/10000000000 : ℝ)*X 0 1+(5402352163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132754903/250000000 : ℝ)*X 1 0+(-2103208131/10000000000 : ℝ)*X 1 1+(540235223/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310196167/10000000000 : ℝ)*X 2 0+(2701176129/5000000000 : ℝ)*X 2 1+(-525802007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436673241/1000000000 : ℝ)*X 0 0+(225659357/500000000 : ℝ)*X 0 1+(4225054243/10000000000 : ℝ)*X 0 2+(436673241/1000000000 : ℝ)*X 1 0+(225659357/500000000 : ℝ)*X 1 1+(4225054243/10000000000 : ℝ)*X 1 2+(436673241/1000000000 : ℝ)*X 2 0+(225659357/500000000 : ℝ)*X 2 1+(4225054243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (533526784392367591951271811/106175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10801867/6250000000000 : ℝ)*(base21) + (109701409/100000000000000 : ℝ)*(base29) + (189564461/50000000000000 : ℝ)*(lower2) + (6842311/100000000000000 : ℝ)*(upper3) + (6750673/50000000000000 : ℝ)*(lower4) + (2572870499731543/50000000000000 : ℝ)*(major0) + (321608819322781/6250000000000 : ℝ)*(major1) + (321608819322781/6250000000000 : ℝ)*(major2) + (213775138611811/3125000000000 : ℝ)*(sp0) + (6840804325876543/100000000000000 : ℝ)*(sp1) + (1710198029273657/25000000000000 : ℝ)*(sp2) + (862668157549123/25000000000000 : ℝ)*(sp3) + (12035952043/100000000000000 : ℝ)*(sp6) + (4985055347/100000000000000 : ℝ)*(sp7) + (3450677615251839/100000000000000 : ℝ)*(f.failure) + (213775138611811/3125000000000 : ℝ)*(f.sum) + (21897861830699/10617500000000000000000000000 : ℝ)*base65 + (430702010971324583/132718750000000000000000000000000 : ℝ)*base67 + (2095480920439605833/132718750000000000000000000000000 : ℝ)*base69 + (6070549956991083651/1061750000000000000000000000000000 : ℝ)*base72 + (4795159494779/10617500000000000000000000000 : ℝ)*base73 + (623902444537769167/132718750000000000000000000000000 : ℝ)*base76 + (64199385921240833651/1061750000000000000000000000000000 : ℝ)*base78 + (976986421415168333/132718750000000000000000000000000 : ℝ)*base79 + (26272988151801/10617500000000000000000000000 : ℝ)*base82 + (1738947/10000000000000000000000 : ℝ)*base90 + (101738947/10000000000000000000000 : ℝ)*base92 + (101738947/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1003683282936881158214907831/212350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50922549/6250000000000 : ℝ)*(base19) + (219917627/20000000000000 : ℝ)*(base23) + (181573351/100000000000000 : ℝ)*(upper3) + (82729711/100000000000000 : ℝ)*(lower4) + (83181697/50000000000000 : ℝ)*(upper5) + (1035096190703239/20000000000000 : ℝ)*(major0) + (1035096190703239/20000000000000 : ℝ)*(major1) + (1035096190703239/20000000000000 : ℝ)*(major2) + (2050653797/12500000000000 : ℝ)*(sp1) + (26188069003/100000000000000 : ℝ)*(sp2) + (6880340920412111/100000000000000 : ℝ)*(sp4) + (6880323700420951/100000000000000 : ℝ)*(sp5) + (1720078408188743/25000000000000 : ℝ)*(sp6) + (1735310414534273/50000000000000 : ℝ)*(sp7) + (1735310414534273/50000000000000 : ℝ)*(f.failure) + (6880340920412111/100000000000000 : ℝ)*(f.sum) + (3203680263899/4247000000000000000000000000 : ℝ)*base66 + (5164392997940130723/424700000000000000000000000000000 : ℝ)*base68 + (998546398222130723/424700000000000000000000000000000 : ℝ)*base70 + (241791891382769277/424700000000000000000000000000000 : ℝ)*base71 + (1308442872563/265437500000000000000000000 : ℝ)*base74 + (1071974638435230723/424700000000000000000000000000000 : ℝ)*base76 + (1331866260587830723/424700000000000000000000000000000 : ℝ)*base78 + (3460475074243469277/424700000000000000000000000000000 : ℝ)*base79 + (3438384265739/2123500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (21295171/5000000000000000000000 : ℝ)*base89 + (21295171/5000000000000000000000 : ℝ)*base91 + (21295171/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1124_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3707/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1124_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1124_s5_0 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-271918303/1250000000 : ℝ)*x 0 + (5395388629/10000000000 : ℝ)*x 1 + (526352959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271918303/1250000000 : ℝ)^8317 ≤ (13216232273007/100000000000000 : ℝ)^6269 := by
    have hnat : (271918303 : ℕ)^8317*100000000000000^6269 ≤ 13216232273007^6269*1250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271918303 1250000000 13216232273007 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395388629/10000000000 : ℝ)^8317 ≤ (22052004951399/50000000000000 : ℝ)^6269 := by
    have hnat : (5395388629 : ℕ)^8317*50000000000000^6269 ≤ 22052004951399^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395388629 10000000000 22052004951399 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526352959/1000000000 : ℝ)^8317 ≤ (42679757799809/100000000000000 : ℝ)^6269 := by
    have hnat : (526352959 : ℕ)^8317*100000000000000^6269 ≤ 42679757799809^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526352959 1000000000 42679757799809 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271918303/1250000000 : ℝ), (5395388629/10000000000 : ℝ), (526352959/1000000000 : ℝ)] ![(13216232273007/100000000000000 : ℝ), (22052004951399/50000000000000 : ℝ), (42679757799809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271918303/1250000000 : ℝ)|^8317 ≤ (13216232273007/100000000000000 : ℝ)^6269
        have hw : |(-271918303/1250000000 : ℝ)|=(271918303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395388629/10000000000 : ℝ)|^8317 ≤ (22052004951399/50000000000000 : ℝ)^6269
        have hw : |(5395388629/10000000000 : ℝ)|=(5395388629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526352959/1000000000 : ℝ)|^8317 ≤ (42679757799809/100000000000000 : ℝ)^6269
        have hw : |(526352959/1000000000 : ℝ)|=(526352959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s5_1 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345330807/10000000000 : ℝ)*x 0 + (-280282737/1250000000 : ℝ)*x 1 + (5263529543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345330807/10000000000 : ℝ)^8317 ≤ (21780982238929/50000000000000 : ℝ)^6269 := by
    have hnat : (5345330807 : ℕ)^8317*50000000000000^6269 ≤ 21780982238929^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345330807 10000000000 21780982238929 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280282737/1250000000 : ℝ)^8317 ≤ (13758278211973/100000000000000 : ℝ)^6269 := by
    have hnat : (280282737 : ℕ)^8317*100000000000000^6269 ≤ 13758278211973^6269*1250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280282737 1250000000 13758278211973 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263529543/10000000000 : ℝ)^8317 ≤ (10669939323551/25000000000000 : ℝ)^6269 := by
    have hnat : (5263529543 : ℕ)^8317*25000000000000^6269 ≤ 10669939323551^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263529543 10000000000 10669939323551 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345330807/10000000000 : ℝ), (-280282737/1250000000 : ℝ), (5263529543/10000000000 : ℝ)] ![(21780982238929/50000000000000 : ℝ), (13758278211973/100000000000000 : ℝ), (10669939323551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345330807/10000000000 : ℝ)|^8317 ≤ (21780982238929/50000000000000 : ℝ)^6269
        have hw : |(5345330807/10000000000 : ℝ)|=(5345330807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-280282737/1250000000 : ℝ)|^8317 ≤ (13758278211973/100000000000000 : ℝ)^6269
        have hw : |(-280282737/1250000000 : ℝ)|=(280282737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263529543/10000000000 : ℝ)|^8317 ≤ (10669939323551/25000000000000 : ℝ)^6269
        have hw : |(5263529543/10000000000 : ℝ)|=(5263529543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s5_2 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345331101/10000000000 : ℝ)*x 0 + (5263529337/10000000000 : ℝ)*x 1 + (-1121130889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345331101/10000000000 : ℝ)^8317 ≤ (43561967656551/100000000000000 : ℝ)^6269 := by
    have hnat : (5345331101 : ℕ)^8317*100000000000000^6269 ≤ 43561967656551^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345331101 10000000000 43561967656551 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263529337/10000000000 : ℝ)^8317 ≤ (42679755078149/100000000000000 : ℝ)^6269 := by
    have hnat : (5263529337 : ℕ)^8317*100000000000000^6269 ≤ 42679755078149^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263529337 10000000000 42679755078149 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121130889/5000000000 : ℝ)^8317 ≤ (2751655450281/20000000000000 : ℝ)^6269 := by
    have hnat : (1121130889 : ℕ)^8317*20000000000000^6269 ≤ 2751655450281^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121130889 5000000000 2751655450281 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345331101/10000000000 : ℝ), (5263529337/10000000000 : ℝ), (-1121130889/5000000000 : ℝ)] ![(43561967656551/100000000000000 : ℝ), (42679755078149/100000000000000 : ℝ), (2751655450281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345331101/10000000000 : ℝ)|^8317 ≤ (43561967656551/100000000000000 : ℝ)^6269
        have hw : |(5345331101/10000000000 : ℝ)|=(5345331101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263529337/10000000000 : ℝ)|^8317 ≤ (42679755078149/100000000000000 : ℝ)^6269
        have hw : |(5263529337/10000000000 : ℝ)|=(5263529337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1121130889/5000000000 : ℝ)|^8317 ≤ (2751655450281/20000000000000 : ℝ)^6269
        have hw : |(-1121130889/5000000000 : ℝ)|=(1121130889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s5_3 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367113189/10000000000 : ℝ)*x 0 + (4238365493/10000000000 : ℝ)*x 1 + (4499769783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367113189/10000000000 : ℝ)^8317 ≤ (133263338657/400000000000 : ℝ)^6269 := by
    have hnat : (4367113189 : ℕ)^8317*400000000000^6269 ≤ 133263338657^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367113189 10000000000 133263338657 400000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238365493/10000000000 : ℝ)^8317 ≤ (3201909246083/10000000000000 : ℝ)^6269 := by
    have hnat : (4238365493 : ℕ)^8317*10000000000000^6269 ≤ 3201909246083^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238365493 10000000000 3201909246083 10000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499769783/10000000000 : ℝ)^8317 ≤ (8666268214317/25000000000000 : ℝ)^6269 := by
    have hnat : (4499769783 : ℕ)^8317*25000000000000^6269 ≤ 8666268214317^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499769783 10000000000 8666268214317 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367113189/10000000000 : ℝ), (4238365493/10000000000 : ℝ), (4499769783/10000000000 : ℝ)] ![(133263338657/400000000000 : ℝ), (3201909246083/10000000000000 : ℝ), (8666268214317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367113189/10000000000 : ℝ)|^8317 ≤ (133263338657/400000000000 : ℝ)^6269
        have hw : |(4367113189/10000000000 : ℝ)|=(4367113189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238365493/10000000000 : ℝ)|^8317 ≤ (3201909246083/10000000000000 : ℝ)^6269
        have hw : |(4238365493/10000000000 : ℝ)|=(4238365493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499769783/10000000000 : ℝ)|^8317 ≤ (8666268214317/25000000000000 : ℝ)^6269
        have hw : |(4499769783/10000000000 : ℝ)|=(4499769783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s5_4 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087675833/5000000000 : ℝ)*x 0 + (526387087/1000000000 : ℝ)*x 1 + (2697523097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087675833/5000000000 : ℝ)^8317 ≤ (3304068631193/25000000000000 : ℝ)^6269 := by
    have hnat : (1087675833 : ℕ)^8317*25000000000000^6269 ≤ 3304068631193^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087675833 5000000000 3304068631193 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526387087/1000000000 : ℝ)^8317 ≤ (10670857293703/25000000000000 : ℝ)^6269 := by
    have hnat : (526387087 : ℕ)^8317*25000000000000^6269 ≤ 10670857293703^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526387087 1000000000 10670857293703 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697523097/5000000000 : ℝ)^8317 ≤ (11025074070787/25000000000000 : ℝ)^6269 := by
    have hnat : (2697523097 : ℕ)^8317*25000000000000^6269 ≤ 11025074070787^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697523097 5000000000 11025074070787 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087675833/5000000000 : ℝ), (526387087/1000000000 : ℝ), (2697523097/5000000000 : ℝ)] ![(3304068631193/25000000000000 : ℝ), (10670857293703/25000000000000 : ℝ), (11025074070787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087675833/5000000000 : ℝ)|^8317 ≤ (3304068631193/25000000000000 : ℝ)^6269
        have hw : |(-1087675833/5000000000 : ℝ)|=(1087675833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526387087/1000000000 : ℝ)|^8317 ≤ (10670857293703/25000000000000 : ℝ)^6269
        have hw : |(526387087/1000000000 : ℝ)|=(526387087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697523097/5000000000 : ℝ)|^8317 ≤ (11025074070787/25000000000000 : ℝ)^6269
        have hw : |(2697523097/5000000000 : ℝ)|=(2697523097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s5_5 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311969159/10000000000 : ℝ)*x 0 + (-131921577/625000000 : ℝ)*x 1 + (2697523041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311969159/10000000000 : ℝ)^8317 ≤ (4320163051519/10000000000000 : ℝ)^6269 := by
    have hnat : (5311969159 : ℕ)^8317*10000000000000^6269 ≤ 4320163051519^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311969159 10000000000 4320163051519 10000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131921577/625000000 : ℝ)^8317 ≤ (3174518598673/25000000000000 : ℝ)^6269 := by
    have hnat : (131921577 : ℕ)^8317*25000000000000^6269 ≤ 3174518598673^6269*625000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131921577 625000000 3174518598673 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697523041/5000000000 : ℝ)^8317 ≤ (882005901371/2000000000000 : ℝ)^6269 := by
    have hnat : (2697523041 : ℕ)^8317*2000000000000^6269 ≤ 882005901371^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697523041 5000000000 882005901371 2000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311969159/10000000000 : ℝ), (-131921577/625000000 : ℝ), (2697523041/5000000000 : ℝ)] ![(4320163051519/10000000000000 : ℝ), (3174518598673/25000000000000 : ℝ), (882005901371/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311969159/10000000000 : ℝ)|^8317 ≤ (4320163051519/10000000000000 : ℝ)^6269
        have hw : |(5311969159/10000000000 : ℝ)|=(5311969159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131921577/625000000 : ℝ)|^8317 ≤ (3174518598673/25000000000000 : ℝ)^6269
        have hw : |(-131921577/625000000 : ℝ)|=(131921577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697523041/5000000000 : ℝ)|^8317 ≤ (882005901371/2000000000000 : ℝ)^6269
        have hw : |(2697523041/5000000000 : ℝ)|=(2697523041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s5_6 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062393819/2000000000 : ℝ)*x 0 + (1079009233/2000000000 : ℝ)*x 1 + (-2110745207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062393819/2000000000 : ℝ)^8317 ≤ (43201629824643/100000000000000 : ℝ)^6269 := by
    have hnat : (1062393819 : ℕ)^8317*100000000000000^6269 ≤ 43201629824643^6269*2000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062393819 2000000000 43201629824643 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079009233/2000000000 : ℝ)^8317 ≤ (22050147984327/50000000000000 : ℝ)^6269 := by
    have hnat : (1079009233 : ℕ)^8317*50000000000000^6269 ≤ 22050147984327^6269*2000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079009233 2000000000 22050147984327 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110745207/10000000000 : ℝ)^8317 ≤ (12698074195161/100000000000000 : ℝ)^6269 := by
    have hnat : (2110745207 : ℕ)^8317*100000000000000^6269 ≤ 12698074195161^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110745207 10000000000 12698074195161 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062393819/2000000000 : ℝ), (1079009233/2000000000 : ℝ), (-2110745207/10000000000 : ℝ)] ![(43201629824643/100000000000000 : ℝ), (22050147984327/50000000000000 : ℝ), (12698074195161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062393819/2000000000 : ℝ)|^8317 ≤ (43201629824643/100000000000000 : ℝ)^6269
        have hw : |(1062393819/2000000000 : ℝ)|=(1062393819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079009233/2000000000 : ℝ)|^8317 ≤ (22050147984327/50000000000000 : ℝ)^6269
        have hw : |(1079009233/2000000000 : ℝ)|=(1079009233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110745207/10000000000 : ℝ)|^8317 ≤ (12698074195161/100000000000000 : ℝ)^6269
        have hw : |(-2110745207/10000000000 : ℝ)|=(2110745207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s5_7 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367123771/10000000000 : ℝ)*x 0 + (224954673/500000000 : ℝ)*x 1 + (84780889/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367123771/10000000000 : ℝ)^8317 ≤ (1041123180157/3125000000000 : ℝ)^6269 := by
    have hnat : (4367123771 : ℕ)^8317*3125000000000^6269 ≤ 1041123180157^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367123771 10000000000 1041123180157 3125000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224954673/500000000 : ℝ)^8317 ≤ (6931632139563/20000000000000 : ℝ)^6269 := by
    have hnat : (224954673 : ℕ)^8317*20000000000000^6269 ≤ 6931632139563^6269*500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224954673 500000000 6931632139563 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84780889/200000000 : ℝ)^8317 ≤ (32025897532107/100000000000000 : ℝ)^6269 := by
    have hnat : (84780889 : ℕ)^8317*100000000000000^6269 ≤ 32025897532107^6269*200000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84780889 200000000 32025897532107 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367123771/10000000000 : ℝ), (224954673/500000000 : ℝ), (84780889/200000000 : ℝ)] ![(1041123180157/3125000000000 : ℝ), (6931632139563/20000000000000 : ℝ), (32025897532107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367123771/10000000000 : ℝ)|^8317 ≤ (1041123180157/3125000000000 : ℝ)^6269
        have hw : |(4367123771/10000000000 : ℝ)|=(4367123771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224954673/500000000 : ℝ)|^8317 ≤ (6931632139563/20000000000000 : ℝ)^6269
        have hw : |(224954673/500000000 : ℝ)|=(224954673/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84780889/200000000 : ℝ)|^8317 ≤ (32025897532107/100000000000000 : ℝ)^6269
        have hw : |(84780889/200000000 : ℝ)|=(84780889/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1124_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11289/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11141/100000 : ℝ) ^ (2079/512 : ℝ) ≤ (13489347230649691/100000000000000000000 : ℝ) := by
    have hpowers : (11141/100000 : ℝ)^2079 ≤ (13489347230649691/100000000000000000000 : ℝ)^512 := by
      have hnat : (11141 : ℕ)^2079*100000000000000000000^512 ≤ 13489347230649691^512*100000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11141 100000 13489347230649691 100000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11141/100000 : ℝ)) (X := (13489347230649691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (2079/512 : ℝ) ≤ (36499944588073997/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^2079 ≤ (36499944588073997/100000000000000000000 : ℝ)^512 := by
      have hnat : (3559 : ℕ)^2079*100000000000000000000^512 ≤ 36499944588073997^512*25000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 36499944588073997 100000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (36499944588073997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013489347230649691/50000000000000000000 : ℝ) ≤ (2000132868565347/2000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50013489347230649691/50000000000000000000 : ℝ)^512 ≤ (2000132868565347/2000000000000000 : ℝ)^2079 := by
      have hnat : (50013489347230649691 : ℕ)^512*2000000000000000^2079 ≤ 2000132868565347^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013489347230649691 50000000000000000000 2000132868565347 2000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000132868565347/2000000000000000 : ℝ)) (X := (50013489347230649691/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506248661477340461/12500000000000000000 : ℝ) ≤ (5000615432828959/5000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (12506248661477340461/12500000000000000000 : ℝ)^512 ≤ (5000615432828959/5000000000000000 : ℝ)^2079 := by
      have hnat : (12506248661477340461 : ℕ)^512*5000000000000000^2079 ≤ 5000615432828959^2079*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506248661477340461 12500000000000000000 5000615432828959 5000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000615432828959/5000000000000000 : ℝ)) (X := (12506248661477340461/12500000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036499944588073997/50000000000000000000 : ℝ) ≤ (10001797388489101/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50036499944588073997/50000000000000000000 : ℝ)^512 ≤ (10001797388489101/10000000000000000 : ℝ)^2079 := by
      have hnat : (50036499944588073997 : ℕ)^512*10000000000000000^2079 ≤ 10001797388489101^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036499944588073997 50000000000000000000 10001797388489101 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001797388489101/10000000000000000 : ℝ)) (X := (50036499944588073997/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13489347230649691/100000000000000000000 : ℝ) ≤ ((30939432879324325219/30950000000000000000 : ℝ)+2*(566522831183/309500000000000 : ℝ)*(11141/100000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (30939432879324325219/30950000000000000000 : ℝ)+2*(566522831183/309500000000000 : ℝ)*(11141/100000 : ℝ)=(2000132868565347/2000000000000000 : ℝ) by norm_num, show 1+2*(13489347230649691/100000000000000000000 : ℝ)=(50013489347230649691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36499944588073997/100000000000000000000 : ℝ)+(13489347230649691/100000000000000000000 : ℝ) ≤ ((30939432879324325219/30950000000000000000 : ℝ)+(566522831183/309500000000000 : ℝ)*((3559/25000 : ℝ)+(11141/100000 : ℝ)))^(2079/512 : ℝ) := by
    rw [show (30939432879324325219/30950000000000000000 : ℝ)+(566522831183/309500000000000 : ℝ)*((3559/25000 : ℝ)+(11141/100000 : ℝ))=(5000615432828959/5000000000000000 : ℝ) by norm_num, show 1+(36499944588073997/100000000000000000000 : ℝ)+(13489347230649691/100000000000000000000 : ℝ)=(12506248661477340461/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36499944588073997/100000000000000000000 : ℝ) ≤ ((30939432879324325219/30950000000000000000 : ℝ)+2*(566522831183/309500000000000 : ℝ)*(3559/25000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (30939432879324325219/30950000000000000000 : ℝ)+2*(566522831183/309500000000000 : ℝ)*(3559/25000 : ℝ)=(10001797388489101/10000000000000000 : ℝ) by norm_num, show 1+2*(36499944588073997/100000000000000000000 : ℝ)=(50036499944588073997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30939432879324325219/30950000000000000000 : ℝ)*(X 1 0+X 2 0)+(566522831183/309500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (30939432879324325219/30950000000000000000 : ℝ)) (alpha := (566522831183/309500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30939432879324325219/30950000000000000000 : ℝ)*(X 0 1+X 2 1)+(566522831183/309500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (30939432879324325219/30950000000000000000 : ℝ)) (alpha := (566522831183/309500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30939432879324325219/30950000000000000000 : ℝ)*(X 0 2+X 1 2)+(566522831183/309500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (30939432879324325219/30950000000000000000 : ℝ)) (alpha := (566522831183/309500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-271918303/1250000000 : ℝ)*X 0 0+(5395388629/10000000000 : ℝ)*X 0 1+(526352959/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345330807/10000000000 : ℝ)*X 1 0+(-280282737/1250000000 : ℝ)*X 1 1+(5263529543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345331101/10000000000 : ℝ)*X 2 0+(5263529337/10000000000 : ℝ)*X 2 1+(-1121130889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367113189/10000000000 : ℝ)*X 0 0+(4238365493/10000000000 : ℝ)*X 0 1+(4499769783/10000000000 : ℝ)*X 0 2+(4367113189/10000000000 : ℝ)*X 1 0+(4238365493/10000000000 : ℝ)*X 1 1+(4499769783/10000000000 : ℝ)*X 1 2+(4367113189/10000000000 : ℝ)*X 2 0+(4238365493/10000000000 : ℝ)*X 2 1+(4499769783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1087675833/5000000000 : ℝ)*X 0 0+(526387087/1000000000 : ℝ)*X 0 1+(2697523097/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311969159/10000000000 : ℝ)*X 1 0+(-131921577/625000000 : ℝ)*X 1 1+(2697523041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062393819/2000000000 : ℝ)*X 2 0+(1079009233/2000000000 : ℝ)*X 2 1+(-2110745207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367123771/10000000000 : ℝ)*X 0 0+(224954673/500000000 : ℝ)*X 0 1+(84780889/200000000 : ℝ)*X 0 2+(4367123771/10000000000 : ℝ)*X 1 0+(224954673/500000000 : ℝ)*X 1 1+(84780889/200000000 : ℝ)*X 1 2+(4367123771/10000000000 : ℝ)*X 2 0+(224954673/500000000 : ℝ)*X 2 1+(84780889/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13426262086357111953663/7737500000000000000000000000 : ℝ) := by norm_num
    linear_combination (36155937/10000000000000 : ℝ)*(base19) + (409786189/50000000000000 : ℝ)*(base23) + (2842897/50000000000000 : ℝ)*(lower2) + (42413743/100000000000000 : ℝ)*(upper5) + (1426174218584577/25000000000000 : ℝ)*(major0) + (1426174218584577/25000000000000 : ℝ)*(major1) + (1426174218584577/25000000000000 : ℝ)*(major2) + (236995871753279/3125000000000 : ℝ)*(sp0) + (947984730697363/12500000000000 : ℝ)*(sp1) + (1516777128670173/20000000000000 : ℝ)*(sp2) + (1912749382728663/50000000000000 : ℝ)*(sp3) + (3713363663/20000000000000 : ℝ)*(sp4) + (8255784969/100000000000000 : ℝ)*(sp5) + (8462455383/100000000000000 : ℝ)*(sp7) + (956376806978177/25000000000000 : ℝ)*(f.failure) + (7583886462923243/100000000000000 : ℝ)*(f.sum) + (8476648098011/15475000000000000000000000000 : ℝ)*base66 + (13798606241910352637/773750000000000000000000000000000 : ℝ)*base68 + (3855781461637852637/773750000000000000000000000000000 : ℝ)*base70 + (845576719747147363/773750000000000000000000000000000 : ℝ)*base71 + (37010857053493/7737500000000000000000000000 : ℝ)*base74 + (8000823320487147363/773750000000000000000000000000000 : ℝ)*base75 + (8911544608304647363/773750000000000000000000000000000 : ℝ)*base77 + (4574561294306602637/773750000000000000000000000000000 : ℝ)*base80 + (22401911807343/7737500000000000000000000000 : ℝ)*base82 + (14089021/2500000000000000000000 : ℝ)*base90 + (14089021/2500000000000000000000 : ℝ)*base92 + (14089021/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4934419550661718294275094713/1547500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224115389/100000000000000 : ℝ)*(base19) + (69416381/20000000000000 : ℝ)*(base23) + (7178507/100000000000000 : ℝ)*(lower3) + (446233/500000000000 : ℝ)*(lower4) + (2135033/4000000000000 : ℝ)*(lower5) + (5734404328656591/100000000000000 : ℝ)*(major0) + (5734404328656591/100000000000000 : ℝ)*(major1) + (5734404328656591/100000000000000 : ℝ)*(major2) + (950479637/50000000000000 : ℝ)*(sp1) + (2338316747/25000000000000 : ℝ)*(sp2) + (3811689914848671/50000000000000 : ℝ)*(sp4) + (3811688852311339/50000000000000 : ℝ)*(sp5) + (7623370129348449/100000000000000 : ℝ)*(sp6) + (961357180331961/25000000000000 : ℝ)*(sp7) + (961357180331961/25000000000000 : ℝ)*(f.failure) + (3811689914848671/50000000000000 : ℝ)*(f.sum) + (38149372280047/15475000000000000000000000000 : ℝ)*base66 + (10925078934467168429/3095000000000000000000000000000000 : ℝ)*base67 + (38826645165507168429/3095000000000000000000000000000000 : ℝ)*base69 + (51203622574612831571/3095000000000000000000000000000000 : ℝ)*base72 + (46195606593153/15475000000000000000000000000 : ℝ)*base73 + (107405460087657168429/3095000000000000000000000000000000 : ℝ)*base75 + (29707719518297831571/3095000000000000000000000000000000 : ℝ)*base78 + (34485619418872168429/3095000000000000000000000000000000 : ℝ)*base79 + (17010388982739/7737500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (18618453/2500000000000000000000 : ℝ)*base90 + (18618453/2500000000000000000000 : ℝ)*base92 + (18618453/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1124_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1124_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1124_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1124_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1124_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1124_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1124_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

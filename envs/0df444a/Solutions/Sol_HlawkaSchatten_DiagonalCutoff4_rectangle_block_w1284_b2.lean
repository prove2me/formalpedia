-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1284_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:19.035759+00:00
-- url     : https://prove2.me/submissions/f5e39b28-8a9f-41c3-8a31-8bbae96a416d

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
theorem support_rectangle_w1284_s6_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095149249/10000000000 : ℝ)*x 0 + (5415742217/10000000000 : ℝ)*x 1 + (524260673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095149249/10000000000 : ℝ)^1061 ≤ (1274538305693/10000000000000 : ℝ)^805 := by
    have hnat : (2095149249 : ℕ)^1061*10000000000000^805 ≤ 1274538305693^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095149249 10000000000 1274538305693 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415742217/10000000000 : ℝ)^1061 ≤ (11140326603357/25000000000000 : ℝ)^805 := by
    have hnat : (5415742217 : ℕ)^1061*25000000000000^805 ≤ 11140326603357^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415742217 10000000000 11140326603357 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524260673/1000000000 : ℝ)^1061 ≤ (42693310512583/100000000000000 : ℝ)^805 := by
    have hnat : (524260673 : ℕ)^1061*100000000000000^805 ≤ 42693310512583^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524260673 1000000000 42693310512583 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095149249/10000000000 : ℝ), (5415742217/10000000000 : ℝ), (524260673/1000000000 : ℝ)] ![(1274538305693/10000000000000 : ℝ), (11140326603357/25000000000000 : ℝ), (42693310512583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095149249/10000000000 : ℝ)|^1061 ≤ (1274538305693/10000000000000 : ℝ)^805
        have hw : |(-2095149249/10000000000 : ℝ)|=(2095149249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415742217/10000000000 : ℝ)|^1061 ≤ (11140326603357/25000000000000 : ℝ)^805
        have hw : |(5415742217/10000000000 : ℝ)|=(5415742217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524260673/1000000000 : ℝ)|^1061 ≤ (42693310512583/100000000000000 : ℝ)^805
        have hw : |(524260673/1000000000 : ℝ)|=(524260673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s6_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349925423/10000000000 : ℝ)*x 0 + (-436682711/2000000000 : ℝ)*x 1 + (5242606573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349925423/10000000000 : ℝ)^1061 ≤ (342569711079/781250000000 : ℝ)^805 := by
    have hnat : (5349925423 : ℕ)^1061*781250000000^805 ≤ 342569711079^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349925423 10000000000 342569711079 781250000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436682711/2000000000 : ℝ)^1061 ≤ (6728884064553/50000000000000 : ℝ)^805 := by
    have hnat : (436682711 : ℕ)^1061*50000000000000^805 ≤ 6728884064553^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436682711 2000000000 6728884064553 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242606573/10000000000 : ℝ)^1061 ≤ (2134665441373/5000000000000 : ℝ)^805 := by
    have hnat : (5242606573 : ℕ)^1061*5000000000000^805 ≤ 2134665441373^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242606573 10000000000 2134665441373 5000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349925423/10000000000 : ℝ), (-436682711/2000000000 : ℝ), (5242606573/10000000000 : ℝ)] ![(342569711079/781250000000 : ℝ), (6728884064553/50000000000000 : ℝ), (2134665441373/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349925423/10000000000 : ℝ)|^1061 ≤ (342569711079/781250000000 : ℝ)^805
        have hw : |(5349925423/10000000000 : ℝ)|=(5349925423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436682711/2000000000 : ℝ)|^1061 ≤ (6728884064553/50000000000000 : ℝ)^805
        have hw : |(-436682711/2000000000 : ℝ)|=(436682711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242606573/10000000000 : ℝ)|^1061 ≤ (2134665441373/5000000000000 : ℝ)^805
        have hw : |(5242606573/10000000000 : ℝ)|=(5242606573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s6_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349925631/10000000000 : ℝ)*x 0 + (262130337/500000000 : ℝ)*x 1 + (-1091706529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349925631/10000000000 : ℝ)^1061 ≤ (8769785053013/20000000000000 : ℝ)^805 := by
    have hnat : (5349925631 : ℕ)^1061*20000000000000^805 ≤ 8769785053013^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349925631 10000000000 8769785053013 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262130337/500000000 : ℝ)^1061 ≤ (10673327654979/25000000000000 : ℝ)^805 := by
    have hnat : (262130337 : ℕ)^1061*25000000000000^805 ≤ 10673327654979^805*500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262130337 500000000 10673327654979 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091706529/5000000000 : ℝ)^1061 ≤ (6728882045801/50000000000000 : ℝ)^805 := by
    have hnat : (1091706529 : ℕ)^1061*50000000000000^805 ≤ 6728882045801^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091706529 5000000000 6728882045801 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349925631/10000000000 : ℝ), (262130337/500000000 : ℝ), (-1091706529/5000000000 : ℝ)] ![(8769785053013/20000000000000 : ℝ), (10673327654979/25000000000000 : ℝ), (6728882045801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349925631/10000000000 : ℝ)|^1061 ≤ (8769785053013/20000000000000 : ℝ)^805
        have hw : |(5349925631/10000000000 : ℝ)|=(5349925631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262130337/500000000 : ℝ)|^1061 ≤ (10673327654979/25000000000000 : ℝ)^805
        have hw : |(262130337/500000000 : ℝ)|=(262130337/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091706529/5000000000 : ℝ)|^1061 ≤ (6728882045801/50000000000000 : ℝ)^805
        have hw : |(-1091706529/5000000000 : ℝ)|=(1091706529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s6_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1085502769/2500000000 : ℝ)*x 0 + (4168114401/10000000000 : ℝ)*x 1 + (565357599/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085502769/2500000000 : ℝ)^1061 ≤ (33302139905829/100000000000000 : ℝ)^805 := by
    have hnat : (1085502769 : ℕ)^1061*100000000000000^805 ≤ 33302139905829^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085502769 2500000000 33302139905829 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168114401/10000000000 : ℝ)^1061 ≤ (31555546910677/100000000000000 : ℝ)^805 := by
    have hnat : (4168114401 : ℕ)^1061*100000000000000^805 ≤ 31555546910677^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168114401 10000000000 31555546910677 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565357599/1250000000 : ℝ)^1061 ≤ (4392789145681/12500000000000 : ℝ)^805 := by
    have hnat : (565357599 : ℕ)^1061*12500000000000^805 ≤ 4392789145681^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565357599 1250000000 4392789145681 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085502769/2500000000 : ℝ), (4168114401/10000000000 : ℝ), (565357599/1250000000 : ℝ)] ![(33302139905829/100000000000000 : ℝ), (31555546910677/100000000000000 : ℝ), (4392789145681/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085502769/2500000000 : ℝ)|^1061 ≤ (33302139905829/100000000000000 : ℝ)^805
        have hw : |(1085502769/2500000000 : ℝ)|=(1085502769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168114401/10000000000 : ℝ)|^1061 ≤ (31555546910677/100000000000000 : ℝ)^805
        have hw : |(4168114401/10000000000 : ℝ)|=(4168114401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565357599/1250000000 : ℝ)|^1061 ≤ (4392789145681/12500000000000 : ℝ)^805
        have hw : |(565357599/1250000000 : ℝ)|=(565357599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s6_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095161973/10000000000 : ℝ)*x 0 + (5243224199/10000000000 : ℝ)*x 1 + (1083024333/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095161973/10000000000 : ℝ)^1061 ≤ (2549097015207/20000000000000 : ℝ)^805 := by
    have hnat : (2095161973 : ℕ)^1061*20000000000000^805 ≤ 2549097015207^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095161973 10000000000 2549097015207 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243224199/10000000000 : ℝ)^1061 ≤ (21349969049099/50000000000000 : ℝ)^805 := by
    have hnat : (5243224199 : ℕ)^1061*50000000000000^805 ≤ 21349969049099^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243224199 10000000000 21349969049099 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083024333/2000000000 : ℝ)^1061 ≤ (44554576806459/100000000000000 : ℝ)^805 := by
    have hnat : (1083024333 : ℕ)^1061*100000000000000^805 ≤ 44554576806459^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083024333 2000000000 44554576806459 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095161973/10000000000 : ℝ), (5243224199/10000000000 : ℝ), (1083024333/2000000000 : ℝ)] ![(2549097015207/20000000000000 : ℝ), (21349969049099/50000000000000 : ℝ), (44554576806459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095161973/10000000000 : ℝ)|^1061 ≤ (2549097015207/20000000000000 : ℝ)^805
        have hw : |(-2095161973/10000000000 : ℝ)|=(2095161973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243224199/10000000000 : ℝ)|^1061 ≤ (21349969049099/50000000000000 : ℝ)^805
        have hw : |(5243224199/10000000000 : ℝ)|=(5243224199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083024333/2000000000 : ℝ)|^1061 ≤ (44554576806459/100000000000000 : ℝ)^805
        have hw : |(1083024333/2000000000 : ℝ)|=(1083024333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s6_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652821739/5000000000 : ℝ)*x 0 + (-1005449169/5000000000 : ℝ)*x 1 + (5415121677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652821739/5000000000 : ℝ)^1061 ≤ (8674238198251/20000000000000 : ℝ)^805 := by
    have hnat : (2652821739 : ℕ)^1061*20000000000000^805 ≤ 8674238198251^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652821739 5000000000 8674238198251 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005449169/5000000000 : ℝ)^1061 ≤ (6037116026677/50000000000000 : ℝ)^805 := by
    have hnat : (1005449169 : ℕ)^1061*50000000000000^805 ≤ 6037116026677^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005449169 5000000000 6037116026677 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415121677/10000000000 : ℝ)^1061 ≤ (44554576936591/100000000000000 : ℝ)^805 := by
    have hnat : (5415121677 : ℕ)^1061*100000000000000^805 ≤ 44554576936591^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415121677 10000000000 44554576936591 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652821739/5000000000 : ℝ), (-1005449169/5000000000 : ℝ), (5415121677/10000000000 : ℝ)] ![(8674238198251/20000000000000 : ℝ), (6037116026677/50000000000000 : ℝ), (44554576936591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652821739/5000000000 : ℝ)|^1061 ≤ (8674238198251/20000000000000 : ℝ)^805
        have hw : |(2652821739/5000000000 : ℝ)|=(2652821739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005449169/5000000000 : ℝ)|^1061 ≤ (6037116026677/50000000000000 : ℝ)^805
        have hw : |(-1005449169/5000000000 : ℝ)|=(1005449169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415121677/10000000000 : ℝ)|^1061 ≤ (44554576936591/100000000000000 : ℝ)^805
        have hw : |(5415121677/10000000000 : ℝ)|=(5415121677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s6_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305643503/10000000000 : ℝ)*x 0 + (5415121659/10000000000 : ℝ)*x 1 + (-251362291/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305643503/10000000000 : ℝ)^1061 ≤ (43371191260609/100000000000000 : ℝ)^805 := by
    have hnat : (5305643503 : ℕ)^1061*100000000000000^805 ≤ 43371191260609^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305643503 10000000000 43371191260609 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415121659/10000000000 : ℝ)^1061 ≤ (44554576741393/100000000000000 : ℝ)^805 := by
    have hnat : (5415121659 : ℕ)^1061*100000000000000^805 ≤ 44554576741393^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415121659 10000000000 44554576741393 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251362291/1250000000 : ℝ)^1061 ≤ (1509278996777/12500000000000 : ℝ)^805 := by
    have hnat : (251362291 : ℕ)^1061*12500000000000^805 ≤ 1509278996777^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251362291 1250000000 1509278996777 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305643503/10000000000 : ℝ), (5415121659/10000000000 : ℝ), (-251362291/1250000000 : ℝ)] ![(43371191260609/100000000000000 : ℝ), (44554576741393/100000000000000 : ℝ), (1509278996777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305643503/10000000000 : ℝ)|^1061 ≤ (43371191260609/100000000000000 : ℝ)^805
        have hw : |(5305643503/10000000000 : ℝ)|=(5305643503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415121659/10000000000 : ℝ)|^1061 ≤ (44554576741393/100000000000000 : ℝ)^805
        have hw : |(5415121659/10000000000 : ℝ)|=(5415121659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251362291/1250000000 : ℝ)|^1061 ≤ (1509278996777/12500000000000 : ℝ)^805
        have hw : |(-251362291/1250000000 : ℝ)|=(251362291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s6_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4342037931/10000000000 : ℝ)*x 0 + (4521595783/10000000000 : ℝ)*x 1 + (2084692687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342037931/10000000000 : ℝ)^1061 ≤ (4162801422327/12500000000000 : ℝ)^805 := by
    have hnat : (4342037931 : ℕ)^1061*12500000000000^805 ≤ 4162801422327^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342037931 10000000000 4162801422327 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521595783/10000000000 : ℝ)^1061 ≤ (17564679477821/50000000000000 : ℝ)^805 := by
    have hnat : (4521595783 : ℕ)^1061*50000000000000^805 ≤ 17564679477821^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521595783 10000000000 17564679477821 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084692687/5000000000 : ℝ)^1061 ≤ (31568229647027/100000000000000 : ℝ)^805 := by
    have hnat : (2084692687 : ℕ)^1061*100000000000000^805 ≤ 31568229647027^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084692687 5000000000 31568229647027 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342037931/10000000000 : ℝ), (4521595783/10000000000 : ℝ), (2084692687/5000000000 : ℝ)] ![(4162801422327/12500000000000 : ℝ), (17564679477821/50000000000000 : ℝ), (31568229647027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342037931/10000000000 : ℝ)|^1061 ≤ (4162801422327/12500000000000 : ℝ)^805
        have hw : |(4342037931/10000000000 : ℝ)|=(4342037931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521595783/10000000000 : ℝ)|^1061 ≤ (17564679477821/50000000000000 : ℝ)^805
        have hw : |(4521595783/10000000000 : ℝ)|=(4521595783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084692687/5000000000 : ℝ)|^1061 ≤ (31568229647027/100000000000000 : ℝ)^805
        have hw : |(2084692687/5000000000 : ℝ)|=(2084692687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2201/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14669/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10993/100000 : ℝ) ^ (4243/1024 : ℝ) ≤ (5318420306510049/50000000000000000000 : ℝ) := by
    have hpowers : (10993/100000 : ℝ)^4243 ≤ (5318420306510049/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10993 : ℕ)^4243*50000000000000000000^1024 ≤ 5318420306510049^1024*100000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10993 100000 5318420306510049 50000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10993/100000 : ℝ)) (X := (5318420306510049/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7341/50000 : ℝ) ^ (4243/1024 : ℝ) ≤ (4410004214897461/12500000000000000000 : ℝ) := by
    have hpowers : (7341/50000 : ℝ)^4243 ≤ (4410004214897461/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7341 : ℕ)^4243*12500000000000000000^1024 ≤ 4410004214897461^1024*50000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7341 50000 4410004214897461 12500000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7341/50000 : ℝ)) (X := (4410004214897461/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005318420306510049/25000000000000000000 : ℝ) ≤ (200010267495573/200000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (25005318420306510049/25000000000000000000 : ℝ)^1024 ≤ (200010267495573/200000000000000 : ℝ)^4243 := by
      have hnat : (25005318420306510049 : ℕ)^1024*200000000000000^4243 ≤ 200010267495573^4243*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005318420306510049 25000000000000000000 200010267495573 200000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200010267495573/200000000000000 : ℝ)) (X := (25005318420306510049/25000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022958437166099893/50000000000000000000 : ℝ) ≤ (5000553979400457/5000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50022958437166099893/50000000000000000000 : ℝ)^1024 ≤ (5000553979400457/5000000000000000 : ℝ)^4243 := by
      have hnat : (50022958437166099893 : ℕ)^1024*5000000000000000^4243 ≤ 5000553979400457^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022958437166099893 50000000000000000000 5000553979400457 5000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000553979400457/5000000000000000 : ℝ)) (X := (50022958437166099893/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254410004214897461/6250000000000000000 : ℝ) ≤ (5000851271411589/5000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (6254410004214897461/6250000000000000000 : ℝ)^1024 ≤ (5000851271411589/5000000000000000 : ℝ)^4243 := by
      have hnat : (6254410004214897461 : ℕ)^1024*5000000000000000^4243 ≤ 5000851271411589^4243*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254410004214897461 6250000000000000000 5000851271411589 5000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000851271411589/5000000000000000 : ℝ)) (X := (6254410004214897461/6250000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5318420306510049/50000000000000000000 : ℝ) ≤ ((18439410657622471773/18445000000000000000 : ℝ)+2*(74323002783/46112500000000 : ℝ)*(10993/100000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (18439410657622471773/18445000000000000000 : ℝ)+2*(74323002783/46112500000000 : ℝ)*(10993/100000 : ℝ)=(200010267495573/200000000000000 : ℝ) by norm_num, show 1+2*(5318420306510049/50000000000000000000 : ℝ)=(25005318420306510049/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4410004214897461/12500000000000000000 : ℝ)+(5318420306510049/50000000000000000000 : ℝ) ≤ ((18439410657622471773/18445000000000000000 : ℝ)+(74323002783/46112500000000 : ℝ)*((7341/50000 : ℝ)+(10993/100000 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (18439410657622471773/18445000000000000000 : ℝ)+(74323002783/46112500000000 : ℝ)*((7341/50000 : ℝ)+(10993/100000 : ℝ))=(5000553979400457/5000000000000000 : ℝ) by norm_num, show 1+(4410004214897461/12500000000000000000 : ℝ)+(5318420306510049/50000000000000000000 : ℝ)=(50022958437166099893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4410004214897461/12500000000000000000 : ℝ) ≤ ((18439410657622471773/18445000000000000000 : ℝ)+2*(74323002783/46112500000000 : ℝ)*(7341/50000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (18439410657622471773/18445000000000000000 : ℝ)+2*(74323002783/46112500000000 : ℝ)*(7341/50000 : ℝ)=(5000851271411589/5000000000000000 : ℝ) by norm_num, show 1+2*(4410004214897461/12500000000000000000 : ℝ)=(6254410004214897461/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18439410657622471773/18445000000000000000 : ℝ)*(X 1 0+X 2 0)+(74323002783/46112500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (10993/100000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (18439410657622471773/18445000000000000000 : ℝ)) (alpha := (74323002783/46112500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18439410657622471773/18445000000000000000 : ℝ)*(X 0 1+X 2 1)+(74323002783/46112500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (10993/100000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (18439410657622471773/18445000000000000000 : ℝ)) (alpha := (74323002783/46112500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18439410657622471773/18445000000000000000 : ℝ)*(X 0 2+X 1 2)+(74323002783/46112500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (10993/100000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (18439410657622471773/18445000000000000000 : ℝ)) (alpha := (74323002783/46112500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2095149249/10000000000 : ℝ)*X 0 0+(5415742217/10000000000 : ℝ)*X 0 1+(524260673/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349925423/10000000000 : ℝ)*X 1 0+(-436682711/2000000000 : ℝ)*X 1 1+(5242606573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349925631/10000000000 : ℝ)*X 2 0+(262130337/500000000 : ℝ)*X 2 1+(-1091706529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085502769/2500000000 : ℝ)*X 0 0+(4168114401/10000000000 : ℝ)*X 0 1+(565357599/1250000000 : ℝ)*X 0 2+(1085502769/2500000000 : ℝ)*X 1 0+(4168114401/10000000000 : ℝ)*X 1 1+(565357599/1250000000 : ℝ)*X 1 2+(1085502769/2500000000 : ℝ)*X 2 0+(4168114401/10000000000 : ℝ)*X 2 1+(565357599/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2095161973/10000000000 : ℝ)*X 0 0+(5243224199/10000000000 : ℝ)*X 0 1+(1083024333/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652821739/5000000000 : ℝ)*X 1 0+(-1005449169/5000000000 : ℝ)*X 1 1+(5415121677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305643503/10000000000 : ℝ)*X 2 0+(5415121659/10000000000 : ℝ)*X 2 1+(-251362291/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342037931/10000000000 : ℝ)*X 0 0+(4521595783/10000000000 : ℝ)*X 0 1+(2084692687/5000000000 : ℝ)*X 0 2+(4342037931/10000000000 : ℝ)*X 1 0+(4521595783/10000000000 : ℝ)*X 1 1+(2084692687/5000000000 : ℝ)*X 1 2+(4342037931/10000000000 : ℝ)*X 2 0+(4521595783/10000000000 : ℝ)*X 2 1+(2084692687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5333545711327574586193019871/922250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132138563/12500000000000 : ℝ)*(base19) + (63263773/6250000000000 : ℝ)*(base23) + (43783989/25000000000000 : ℝ)*(upper4) + (32036867/20000000000000 : ℝ)*(upper5) + (4297403733123997/100000000000000 : ℝ)*(major0) + (4297403733123997/100000000000000 : ℝ)*(major1) + (4297403733123997/100000000000000 : ℝ)*(major2) + (5775842201379203/100000000000000 : ℝ)*(sp0) + (180495782481879/3125000000000 : ℝ)*(sp1) + (2887936040532289/50000000000000 : ℝ)*(sp2) + (352365589531081/12500000000000 : ℝ)*(sp3) + (30891905743/100000000000000 : ℝ)*(sp4) + (3498378157/50000000000000 : ℝ)*(sp5) + (1892788287/20000000000000 : ℝ)*(sp7) + (704733545047521/25000000000000 : ℝ)*(f.failure) + (2887936546642473/50000000000000 : ℝ)*(f.sum) + (17792763229207/18445000000000000000000000000 : ℝ)*base66 + (24238514057837336681/1844500000000000000000000000000000 : ℝ)*base67 + (26329249587902336681/1844500000000000000000000000000000 : ℝ)*base69 + (11151797425631336681/1844500000000000000000000000000000 : ℝ)*base71 + (32066090871163/18445000000000000000000000000 : ℝ)*base73 + (17471477998455836681/1844500000000000000000000000000000 : ℝ)*base75 + (27542274388582336681/1844500000000000000000000000000000 : ℝ)*base77 + (19146831178603336681/1844500000000000000000000000000000 : ℝ)*base79 + (22992213889109/9222500000000000000000000000 : ℝ)*base81 + (7098259/2500000000000000000000 : ℝ)*base90 + (7098259/2500000000000000000000 : ℝ)*base92 + (7098259/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116092046544622882436427/18445000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1093836561/100000000000000 : ℝ)*(base19) + (616864851/50000000000000 : ℝ)*(base23) + (129057281/100000000000000 : ℝ)*(upper3) + (24755787/50000000000000 : ℝ)*(lower4) + (66262949/50000000000000 : ℝ)*(upper5) + (2164158173505859/50000000000000 : ℝ)*(major0) + (2164158173505859/50000000000000 : ℝ)*(major1) + (2164158173505859/50000000000000 : ℝ)*(major2) + (549856751/2500000000000 : ℝ)*(sp1) + (24290182017/100000000000000 : ℝ)*(sp2) + (1454355199863307/25000000000000 : ℝ)*(sp4) + (1454349427836657/25000000000000 : ℝ)*(sp5) + (5817395275541509/100000000000000 : ℝ)*(sp6) + (88725365149113/3125000000000 : ℝ)*(sp7) + (88725365149113/3125000000000 : ℝ)*(f.failure) + (1454355199863307/25000000000000 : ℝ)*(f.sum) + (6183521262103/4611250000000000000000000000 : ℝ)*base65 + (1950930364408581993/922250000000000000000000000000000 : ℝ)*base68 + (3624468094977418007/922250000000000000000000000000000 : ℝ)*base69 + (8623525225683581993/922250000000000000000000000000000 : ℝ)*base72 + (581372856923/288203125000000000000000000 : ℝ)*base73 + (4465888917681418007/922250000000000000000000000000000 : ℝ)*base75 + (4594600165853918007/922250000000000000000000000000000 : ℝ)*base77 + (6997642502976331993/922250000000000000000000000000000 : ℝ)*base80 + (29179643479041/9222500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1817227/312500000000000000000 : ℝ)*base90 + (1817227/312500000000000000000 : ℝ)*base92 + (1817227/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1284_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1284_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1284_s7_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-130947681/625000000 : ℝ)*x 0 + (5415627193/10000000000 : ℝ)*x 1 + (2621356377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130947681/625000000 : ℝ)^1061 ≤ (12745492476517/100000000000000 : ℝ)^805 := by
    have hnat : (130947681 : ℕ)^1061*100000000000000^805 ≤ 12745492476517^805*625000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130947681 625000000 12745492476517 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415627193/10000000000 : ℝ)^1061 ≤ (8912011802287/20000000000000 : ℝ)^805 := by
    have hnat : (5415627193 : ℕ)^1061*20000000000000^805 ≤ 8912011802287^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415627193 10000000000 8912011802287 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621356377/5000000000 : ℝ)^1061 ≤ (21347224250231/50000000000000 : ℝ)^805 := by
    have hnat : (2621356377 : ℕ)^1061*50000000000000^805 ≤ 21347224250231^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621356377 5000000000 21347224250231 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130947681/625000000 : ℝ), (5415627193/10000000000 : ℝ), (2621356377/5000000000 : ℝ)] ![(12745492476517/100000000000000 : ℝ), (8912011802287/20000000000000 : ℝ), (21347224250231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130947681/625000000 : ℝ)|^1061 ≤ (12745492476517/100000000000000 : ℝ)^805
        have hw : |(-130947681/625000000 : ℝ)|=(130947681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415627193/10000000000 : ℝ)|^1061 ≤ (8912011802287/20000000000000 : ℝ)^805
        have hw : |(5415627193/10000000000 : ℝ)|=(5415627193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621356377/5000000000 : ℝ)|^1061 ≤ (21347224250231/50000000000000 : ℝ)^805
        have hw : |(2621356377/5000000000 : ℝ)|=(2621356377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s7_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674947697/5000000000 : ℝ)*x 0 + (-2183312479/10000000000 : ℝ)*x 1 + (2621356649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674947697/5000000000 : ℝ)^1061 ≤ (1753943945013/4000000000000 : ℝ)^805 := by
    have hnat : (2674947697 : ℕ)^1061*4000000000000^805 ≤ 1753943945013^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674947697 5000000000 1753943945013 4000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2183312479/10000000000 : ℝ)^1061 ≤ (13456947019009/100000000000000 : ℝ)^805 := by
    have hnat : (2183312479 : ℕ)^1061*100000000000000^805 ≤ 13456947019009^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183312479 10000000000 13456947019009 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621356649/5000000000 : ℝ)^1061 ≤ (42694454339399/100000000000000 : ℝ)^805 := by
    have hnat : (2621356649 : ℕ)^1061*100000000000000^805 ≤ 42694454339399^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621356649 5000000000 42694454339399 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674947697/5000000000 : ℝ), (-2183312479/10000000000 : ℝ), (2621356649/5000000000 : ℝ)] ![(1753943945013/4000000000000 : ℝ), (13456947019009/100000000000000 : ℝ), (42694454339399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674947697/5000000000 : ℝ)|^1061 ≤ (1753943945013/4000000000000 : ℝ)^805
        have hw : |(2674947697/5000000000 : ℝ)|=(2674947697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2183312479/10000000000 : ℝ)|^1061 ≤ (13456947019009/100000000000000 : ℝ)^805
        have hw : |(-2183312479/10000000000 : ℝ)|=(2183312479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621356649/5000000000 : ℝ)|^1061 ≤ (42694454339399/100000000000000 : ℝ)^805
        have hw : |(2621356649/5000000000 : ℝ)|=(2621356649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s7_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (167184253/312500000 : ℝ)*x 0 + (262135557/500000000 : ℝ)*x 1 + (-2183314397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167184253/312500000 : ℝ)^1061 ≤ (43848606208779/100000000000000 : ℝ)^805 := by
    have hnat : (167184253 : ℕ)^1061*100000000000000^805 ≤ 43848606208779^805*312500000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167184253 312500000 43848606208779 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262135557/500000000 : ℝ)^1061 ≤ (21347215588427/50000000000000 : ℝ)^805 := by
    have hnat : (262135557 : ℕ)^1061*50000000000000^805 ≤ 21347215588427^805*500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262135557 500000000 21347215588427 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183314397/10000000000 : ℝ)^1061 ≤ (6728481300067/50000000000000 : ℝ)^805 := by
    have hnat : (2183314397 : ℕ)^1061*50000000000000^805 ≤ 6728481300067^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183314397 10000000000 6728481300067 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167184253/312500000 : ℝ), (262135557/500000000 : ℝ), (-2183314397/10000000000 : ℝ)] ![(43848606208779/100000000000000 : ℝ), (21347215588427/50000000000000 : ℝ), (6728481300067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167184253/312500000 : ℝ)|^1061 ≤ (43848606208779/100000000000000 : ℝ)^805
        have hw : |(167184253/312500000 : ℝ)|=(167184253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262135557/500000000 : ℝ)|^1061 ≤ (21347215588427/50000000000000 : ℝ)^805
        have hw : |(262135557/500000000 : ℝ)|=(262135557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183314397/10000000000 : ℝ)|^1061 ≤ (6728481300067/50000000000000 : ℝ)^805
        have hw : |(-2183314397/10000000000 : ℝ)|=(2183314397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s7_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4342017581/10000000000 : ℝ)*x 0 + (4168339673/10000000000 : ℝ)*x 1 + (565329359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342017581/10000000000 : ℝ)^1061 ≤ (33302205663757/100000000000000 : ℝ)^805 := by
    have hnat : (4342017581 : ℕ)^1061*100000000000000^805 ≤ 33302205663757^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342017581 10000000000 33302205663757 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168339673/10000000000 : ℝ)^1061 ≤ (31557794756559/100000000000000 : ℝ)^805 := by
    have hnat : (4168339673 : ℕ)^1061*100000000000000^805 ≤ 31557794756559^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168339673 10000000000 31557794756559 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565329359/1250000000 : ℝ)^1061 ≤ (17569999783839/50000000000000 : ℝ)^805 := by
    have hnat : (565329359 : ℕ)^1061*50000000000000^805 ≤ 17569999783839^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565329359 1250000000 17569999783839 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342017581/10000000000 : ℝ), (4168339673/10000000000 : ℝ), (565329359/1250000000 : ℝ)] ![(33302205663757/100000000000000 : ℝ), (31557794756559/100000000000000 : ℝ), (17569999783839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342017581/10000000000 : ℝ)|^1061 ≤ (33302205663757/100000000000000 : ℝ)^805
        have hw : |(4342017581/10000000000 : ℝ)|=(4342017581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168339673/10000000000 : ℝ)|^1061 ≤ (31557794756559/100000000000000 : ℝ)^805
        have hw : |(4168339673/10000000000 : ℝ)|=(4168339673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565329359/1250000000 : ℝ)|^1061 ≤ (17569999783839/50000000000000 : ℝ)^805
        have hw : |(565329359/1250000000 : ℝ)|=(565329359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s7_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-523793997/2500000000 : ℝ)*x 0 + (655416007/1250000000 : ℝ)*x 1 + (1083001701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523793997/2500000000 : ℝ)^1061 ≤ (12745597446411/100000000000000 : ℝ)^805 := by
    have hnat : (523793997 : ℕ)^1061*100000000000000^805 ≤ 12745597446411^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523793997 2500000000 12745597446411 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655416007/1250000000 : ℝ)^1061 ≤ (10675263217171/25000000000000 : ℝ)^805 := by
    have hnat : (655416007 : ℕ)^1061*25000000000000^805 ≤ 10675263217171^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655416007 1250000000 10675263217171 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083001701/2000000000 : ℝ)^1061 ≤ (44553349663659/100000000000000 : ℝ)^805 := by
    have hnat : (1083001701 : ℕ)^1061*100000000000000^805 ≤ 44553349663659^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083001701 2000000000 44553349663659 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523793997/2500000000 : ℝ), (655416007/1250000000 : ℝ), (1083001701/2000000000 : ℝ)] ![(12745597446411/100000000000000 : ℝ), (10675263217171/25000000000000 : ℝ), (44553349663659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523793997/2500000000 : ℝ)|^1061 ≤ (12745597446411/100000000000000 : ℝ)^805
        have hw : |(-523793997/2500000000 : ℝ)|=(523793997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655416007/1250000000 : ℝ)|^1061 ≤ (10675263217171/25000000000000 : ℝ)^805
        have hw : |(655416007/1250000000 : ℝ)|=(655416007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083001701/2000000000 : ℝ)|^1061 ≤ (44553349663659/100000000000000 : ℝ)^805
        have hw : |(1083001701/2000000000 : ℝ)|=(1083001701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s7_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530567053/1000000000 : ℝ)*x 0 + (-2011016587/10000000000 : ℝ)*x 1 + (1083001701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530567053/1000000000 : ℝ)^1061 ≤ (43371482453643/100000000000000 : ℝ)^805 := by
    have hnat : (530567053 : ℕ)^1061*100000000000000^805 ≤ 43371482453643^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530567053 1000000000 43371482453643 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011016587/10000000000 : ℝ)^1061 ≤ (12075167869307/100000000000000 : ℝ)^805 := by
    have hnat : (2011016587 : ℕ)^1061*100000000000000^805 ≤ 12075167869307^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011016587 10000000000 12075167869307 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083001701/2000000000 : ℝ)^1061 ≤ (44553349663659/100000000000000 : ℝ)^805 := by
    have hnat : (1083001701 : ℕ)^1061*100000000000000^805 ≤ 44553349663659^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083001701 2000000000 44553349663659 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530567053/1000000000 : ℝ), (-2011016587/10000000000 : ℝ), (1083001701/2000000000 : ℝ)] ![(43371482453643/100000000000000 : ℝ), (12075167869307/100000000000000 : ℝ), (44553349663659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530567053/1000000000 : ℝ)|^1061 ≤ (43371482453643/100000000000000 : ℝ)^805
        have hw : |(530567053/1000000000 : ℝ)|=(530567053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2011016587/10000000000 : ℝ)|^1061 ≤ (12075167869307/100000000000000 : ℝ)^805
        have hw : |(-2011016587/10000000000 : ℝ)|=(2011016587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083001701/2000000000 : ℝ)|^1061 ≤ (44553349663659/100000000000000 : ℝ)^805
        have hw : |(1083001701/2000000000 : ℝ)|=(1083001701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s7_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530567053/1000000000 : ℝ)*x 0 + (1083001701/2000000000 : ℝ)*x 1 + (-2011016587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530567053/1000000000 : ℝ)^1061 ≤ (43371482453643/100000000000000 : ℝ)^805 := by
    have hnat : (530567053 : ℕ)^1061*100000000000000^805 ≤ 43371482453643^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530567053 1000000000 43371482453643 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083001701/2000000000 : ℝ)^1061 ≤ (44553349663659/100000000000000 : ℝ)^805 := by
    have hnat : (1083001701 : ℕ)^1061*100000000000000^805 ≤ 44553349663659^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083001701 2000000000 44553349663659 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011016587/10000000000 : ℝ)^1061 ≤ (12075167869307/100000000000000 : ℝ)^805 := by
    have hnat : (2011016587 : ℕ)^1061*100000000000000^805 ≤ 12075167869307^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011016587 10000000000 12075167869307 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530567053/1000000000 : ℝ), (1083001701/2000000000 : ℝ), (-2011016587/10000000000 : ℝ)] ![(43371482453643/100000000000000 : ℝ), (44553349663659/100000000000000 : ℝ), (12075167869307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530567053/1000000000 : ℝ)|^1061 ≤ (43371482453643/100000000000000 : ℝ)^805
        have hw : |(530567053/1000000000 : ℝ)|=(530567053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083001701/2000000000 : ℝ)|^1061 ≤ (44553349663659/100000000000000 : ℝ)^805
        have hw : |(1083001701/2000000000 : ℝ)|=(1083001701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011016587/10000000000 : ℝ)|^1061 ≤ (12075167869307/100000000000000 : ℝ)^805
        have hw : |(-2011016587/10000000000 : ℝ)|=(2011016587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s7_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (86840913/200000000 : ℝ)*x 0 + (4521372463/10000000000 : ℝ)*x 1 + (833921341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86840913/200000000 : ℝ)^1061 ≤ (33302489408819/100000000000000 : ℝ)^805 := by
    have hnat : (86840913 : ℕ)^1061*100000000000000^805 ≤ 33302489408819^805*200000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86840913 200000000 33302489408819 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521372463/10000000000 : ℝ)^1061 ≤ (1756353609357/5000000000000 : ℝ)^805 := by
    have hnat : (4521372463 : ℕ)^1061*5000000000000^805 ≤ 1756353609357^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521372463 10000000000 1756353609357 5000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833921341/2000000000 : ℝ)^1061 ≤ (31570438381981/100000000000000 : ℝ)^805 := by
    have hnat : (833921341 : ℕ)^1061*100000000000000^805 ≤ 31570438381981^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833921341 2000000000 31570438381981 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86840913/200000000 : ℝ), (4521372463/10000000000 : ℝ), (833921341/2000000000 : ℝ)] ![(33302489408819/100000000000000 : ℝ), (1756353609357/5000000000000 : ℝ), (31570438381981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86840913/200000000 : ℝ)|^1061 ≤ (33302489408819/100000000000000 : ℝ)^805
        have hw : |(86840913/200000000 : ℝ)|=(86840913/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521372463/10000000000 : ℝ)|^1061 ≤ (1756353609357/5000000000000 : ℝ)^805
        have hw : |(4521372463/10000000000 : ℝ)|=(4521372463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833921341/2000000000 : ℝ)|^1061 ≤ (31570438381981/100000000000000 : ℝ)^805
        have hw : |(833921341/2000000000 : ℝ)|=(833921341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11007/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14667/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14669/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14669/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14669/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14669/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14669/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14669/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2201/20000 : ℝ) ^ (4243/1024 : ℝ) ≤ (10685034930134759/100000000000000000000 : ℝ) := by
    have hpowers : (2201/20000 : ℝ)^4243 ≤ (10685034930134759/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2201 : ℕ)^4243*100000000000000000000^1024 ≤ 10685034930134759^1024*20000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2201 20000 10685034930134759 100000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2201/20000 : ℝ)) (X := (10685034930134759/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14669/100000 : ℝ) ^ (4243/1024 : ℝ) ≤ (35150776220170609/100000000000000000000 : ℝ) := by
    have hpowers : (14669/100000 : ℝ)^4243 ≤ (35150776220170609/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14669 : ℕ)^4243*100000000000000000000^1024 ≤ 35150776220170609^1024*100000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14669 100000 35150776220170609 100000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14669/100000 : ℝ)) (X := (35150776220170609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010685034930134759/50000000000000000000 : ℝ) ≤ (10000515700632959/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50010685034930134759/50000000000000000000 : ℝ)^1024 ≤ (10000515700632959/10000000000000000 : ℝ)^4243 := by
      have hnat : (50010685034930134759 : ℕ)^1024*10000000000000000^4243 ≤ 10000515700632959^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010685034930134759 50000000000000000000 10000515700632959 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000515700632959/10000000000000000 : ℝ)) (X := (50010685034930134759/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505729476393788171/12500000000000000000 : ℝ) ≤ (200022120062269/200000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (12505729476393788171/12500000000000000000 : ℝ)^1024 ≤ (200022120062269/200000000000000 : ℝ)^4243 := by
      have hnat : (12505729476393788171 : ℕ)^1024*200000000000000^4243 ≤ 200022120062269^4243*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505729476393788171 12500000000000000000 200022120062269 200000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200022120062269/200000000000000 : ℝ)) (X := (12505729476393788171/12500000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035150776220170609/50000000000000000000 : ℝ) ≤ (10001696305593941/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50035150776220170609/50000000000000000000 : ℝ)^1024 ≤ (10001696305593941/10000000000000000 : ℝ)^4243 := by
      have hnat : (50035150776220170609 : ℕ)^1024*10000000000000000^4243 ≤ 10001696305593941^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035150776220170609 50000000000000000000 10001696305593941 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001696305593941/10000000000000000 : ℝ)) (X := (50035150776220170609/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10685034930134759/100000000000000000000 : ℝ) ≤ ((18314448484761777433/18320000000000000000 : ℝ)+2*(590302480491/366400000000000 : ℝ)*(2201/20000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (18314448484761777433/18320000000000000000 : ℝ)+2*(590302480491/366400000000000 : ℝ)*(2201/20000 : ℝ)=(10000515700632959/10000000000000000 : ℝ) by norm_num, show 1+2*(10685034930134759/100000000000000000000 : ℝ)=(50010685034930134759/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35150776220170609/100000000000000000000 : ℝ)+(10685034930134759/100000000000000000000 : ℝ) ≤ ((18314448484761777433/18320000000000000000 : ℝ)+(590302480491/366400000000000 : ℝ)*((14669/100000 : ℝ)+(2201/20000 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (18314448484761777433/18320000000000000000 : ℝ)+(590302480491/366400000000000 : ℝ)*((14669/100000 : ℝ)+(2201/20000 : ℝ))=(200022120062269/200000000000000 : ℝ) by norm_num, show 1+(35150776220170609/100000000000000000000 : ℝ)+(10685034930134759/100000000000000000000 : ℝ)=(12505729476393788171/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35150776220170609/100000000000000000000 : ℝ) ≤ ((18314448484761777433/18320000000000000000 : ℝ)+2*(590302480491/366400000000000 : ℝ)*(14669/100000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (18314448484761777433/18320000000000000000 : ℝ)+2*(590302480491/366400000000000 : ℝ)*(14669/100000 : ℝ)=(10001696305593941/10000000000000000 : ℝ) by norm_num, show 1+2*(35150776220170609/100000000000000000000 : ℝ)=(50035150776220170609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18314448484761777433/18320000000000000000 : ℝ)*(X 1 0+X 2 0)+(590302480491/366400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (14669/100000 : ℝ)) (c := (18314448484761777433/18320000000000000000 : ℝ)) (alpha := (590302480491/366400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18314448484761777433/18320000000000000000 : ℝ)*(X 0 1+X 2 1)+(590302480491/366400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (14669/100000 : ℝ)) (c := (18314448484761777433/18320000000000000000 : ℝ)) (alpha := (590302480491/366400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18314448484761777433/18320000000000000000 : ℝ)*(X 0 2+X 1 2)+(590302480491/366400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (14669/100000 : ℝ)) (c := (18314448484761777433/18320000000000000000 : ℝ)) (alpha := (590302480491/366400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-130947681/625000000 : ℝ)*X 0 0+(5415627193/10000000000 : ℝ)*X 0 1+(2621356377/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674947697/5000000000 : ℝ)*X 1 0+(-2183312479/10000000000 : ℝ)*X 1 1+(2621356649/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167184253/312500000 : ℝ)*X 2 0+(262135557/500000000 : ℝ)*X 2 1+(-2183314397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342017581/10000000000 : ℝ)*X 0 0+(4168339673/10000000000 : ℝ)*X 0 1+(565329359/1250000000 : ℝ)*X 0 2+(4342017581/10000000000 : ℝ)*X 1 0+(4168339673/10000000000 : ℝ)*X 1 1+(565329359/1250000000 : ℝ)*X 1 2+(4342017581/10000000000 : ℝ)*X 2 0+(4168339673/10000000000 : ℝ)*X 2 1+(565329359/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-523793997/2500000000 : ℝ)*X 0 0+(655416007/1250000000 : ℝ)*X 0 1+(1083001701/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530567053/1000000000 : ℝ)*X 1 0+(-2011016587/10000000000 : ℝ)*X 1 1+(1083001701/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530567053/1000000000 : ℝ)*X 2 0+(1083001701/2000000000 : ℝ)*X 2 1+(-2011016587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((86840913/200000000 : ℝ)*X 0 0+(4521372463/10000000000 : ℝ)*X 0 1+(833921341/2000000000 : ℝ)*X 0 2+(86840913/200000000 : ℝ)*X 1 0+(4521372463/10000000000 : ℝ)*X 1 1+(833921341/2000000000 : ℝ)*X 1 2+(86840913/200000000 : ℝ)*X 2 0+(4521372463/10000000000 : ℝ)*X 2 1+(833921341/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (606589513855495470341174997/45800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92591019/50000000000000 : ℝ)*(base15) + (107245649/100000000000000 : ℝ)*(upper2) + (75563579/50000000000000 : ℝ)*(upper4) + (80738083/50000000000000 : ℝ)*(lower5) + (215144148791903/5000000000000 : ℝ)*(major0) + (215144148791903/5000000000000 : ℝ)*(major1) + (215144148791903/5000000000000 : ℝ)*(major2) + (2891612264623193/50000000000000 : ℝ)*(sp0) + (46265895752089/800000000000 : ℝ)*(sp1) + (5783174749077853/100000000000000 : ℝ)*(sp2) + (705628861220139/25000000000000 : ℝ)*(sp3) + (12624946777/100000000000000 : ℝ)*(sp4) + (6240511531/10000000000000 : ℝ)*(sp6) + (12911125307/100000000000000 : ℝ)*(sp7) + (1411264178002931/50000000000000 : ℝ)*(f.failure) + (5783237154193163/100000000000000 : ℝ)*(f.sum) + (19524973445091/916000000000000000000000000 : ℝ)*base66 + (809525180315225001/91600000000000000000000000000000 : ℝ)*base68 + (658276025816425001/91600000000000000000000000000000 : ℝ)*base70 + (667445198640425001/91600000000000000000000000000000 : ℝ)*base72 + (6249710991491/916000000000000000000000000 : ℝ)*base74 + (35182248579974999/91600000000000000000000000000000 : ℝ)*base75 + (531081921761225001/91600000000000000000000000000000 : ℝ)*base78 + (48158232948774999/91600000000000000000000000000000 : ℝ)*base79 + (1106687196523/916000000000000000000000000 : ℝ)*base82 + (37436649/5000000000000000000000 : ℝ)*base90 + (37436649/5000000000000000000000 : ℝ)*base92 + (37436649/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4640167991884861474295442369/458000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1806443019/100000000000000 : ℝ)*(base19) + (981498401/50000000000000 : ℝ)*(base23) + (124422059/20000000000000 : ℝ)*(lower1) + (12883893/6250000000000 : ℝ)*(upper3) + (71009513/100000000000000 : ℝ)*(lower4) + (207942441/100000000000000 : ℝ)*(upper5) + (2166880129842977/50000000000000 : ℝ)*(major0) + (2166880129842977/50000000000000 : ℝ)*(major1) + (2166880129842977/50000000000000 : ℝ)*(major2) + (2725294133/100000000000000 : ℝ)*(sp2) + (1456184374060227/25000000000000 : ℝ)*(sp4) + (582473568979789/10000000000000 : ℝ)*(sp5) + (1456183201987493/25000000000000 : ℝ)*(sp6) + (284278268541861/10000000000000 : ℝ)*(sp7) + (284278268541861/10000000000000 : ℝ)*(f.failure) + (1456184374060227/25000000000000 : ℝ)*(f.sum) + (69718169405653/9160000000000000000000000000 : ℝ)*base66 + (4207820619850511959/916000000000000000000000000000000 : ℝ)*base68 + (19435818021642511959/916000000000000000000000000000000 : ℝ)*base70 + (4382205880402511959/916000000000000000000000000000000 : ℝ)*base72 + (38923959261707/9160000000000000000000000000 : ℝ)*base73 + (68654450851202511959/916000000000000000000000000000000 : ℝ)*base76 + (6318582457250511959/916000000000000000000000000000000 : ℝ)*base78 + (7321248406762511959/916000000000000000000000000000000 : ℝ)*base80 + (96432689172893/9160000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (16734881/1000000000000000000000 : ℝ)*base89 + (16734881/1000000000000000000000 : ℝ)*base91 + (16734881/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1284_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11007/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14667/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1284_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1284_s8_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095165087/10000000000 : ℝ)*x 0 + (1083121877/2000000000 : ℝ)*x 1 + (524272911/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095165087/10000000000 : ℝ)^1061 ≤ (6372755021823/50000000000000 : ℝ)^805 := by
    have hnat : (2095165087 : ℕ)^1061*50000000000000^805 ≤ 6372755021823^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095165087 10000000000 6372755021823 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083121877/2000000000 : ℝ)^1061 ≤ (44559865889581/100000000000000 : ℝ)^805 := by
    have hnat : (1083121877 : ℕ)^1061*100000000000000^805 ≤ 44559865889581^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083121877 2000000000 44559865889581 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524272911/1000000000 : ℝ)^1061 ≤ (42694624055043/100000000000000 : ℝ)^805 := by
    have hnat : (524272911 : ℕ)^1061*100000000000000^805 ≤ 42694624055043^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524272911 1000000000 42694624055043 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095165087/10000000000 : ℝ), (1083121877/2000000000 : ℝ), (524272911/1000000000 : ℝ)] ![(6372755021823/50000000000000 : ℝ), (44559865889581/100000000000000 : ℝ), (42694624055043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095165087/10000000000 : ℝ)|^1061 ≤ (6372755021823/50000000000000 : ℝ)^805
        have hw : |(-2095165087/10000000000 : ℝ)|=(2095165087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083121877/2000000000 : ℝ)|^1061 ≤ (44559865889581/100000000000000 : ℝ)^805
        have hw : |(1083121877/2000000000 : ℝ)|=(1083121877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524272911/1000000000 : ℝ)|^1061 ≤ (42694624055043/100000000000000 : ℝ)^805
        have hw : |(524272911/1000000000 : ℝ)|=(524272911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s8_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674945851/5000000000 : ℝ)*x 0 + (-545824127/2500000000 : ℝ)*x 1 + (2621364551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674945851/5000000000 : ℝ)^1061 ≤ (2192427937099/5000000000000 : ℝ)^805 := by
    have hnat : (2674945851 : ℕ)^1061*5000000000000^805 ≤ 2192427937099^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674945851 5000000000 2192427937099 5000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545824127/2500000000 : ℝ)^1061 ≤ (13456817276661/100000000000000 : ℝ)^805 := by
    have hnat : (545824127 : ℕ)^1061*100000000000000^805 ≤ 13456817276661^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545824127 2500000000 13456817276661 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621364551/5000000000 : ℝ)^1061 ≤ (5336827996147/12500000000000 : ℝ)^805 := by
    have hnat : (2621364551 : ℕ)^1061*12500000000000^805 ≤ 5336827996147^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621364551 5000000000 5336827996147 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674945851/5000000000 : ℝ), (-545824127/2500000000 : ℝ), (2621364551/5000000000 : ℝ)] ![(2192427937099/5000000000000 : ℝ), (13456817276661/100000000000000 : ℝ), (5336827996147/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674945851/5000000000 : ℝ)|^1061 ≤ (2192427937099/5000000000000 : ℝ)^805
        have hw : |(2674945851/5000000000 : ℝ)|=(2674945851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545824127/2500000000 : ℝ)|^1061 ≤ (13456817276661/100000000000000 : ℝ)^805
        have hw : |(-545824127/2500000000 : ℝ)|=(545824127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621364551/5000000000 : ℝ)|^1061 ≤ (5336827996147/12500000000000 : ℝ)^805
        have hw : |(2621364551/5000000000 : ℝ)|=(2621364551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s8_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349891731/10000000000 : ℝ)*x 0 + (5242729099/10000000000 : ℝ)*x 1 + (-272912059/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349891731/10000000000 : ℝ)^1061 ≤ (5481069881907/12500000000000 : ℝ)^805 := by
    have hnat : (5349891731 : ℕ)^1061*12500000000000^805 ≤ 5481069881907^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349891731 10000000000 5481069881907 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242729099/10000000000 : ℝ)^1061 ≤ (2668413996061/6250000000000 : ℝ)^805 := by
    have hnat : (5242729099 : ℕ)^1061*6250000000000^805 ≤ 2668413996061^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242729099 10000000000 2668413996061 6250000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272912059/1250000000 : ℝ)^1061 ≤ (13456816984211/100000000000000 : ℝ)^805 := by
    have hnat : (272912059 : ℕ)^1061*100000000000000^805 ≤ 13456816984211^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272912059 1250000000 13456816984211 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349891731/10000000000 : ℝ), (5242729099/10000000000 : ℝ), (-272912059/1250000000 : ℝ)] ![(5481069881907/12500000000000 : ℝ), (2668413996061/6250000000000 : ℝ), (13456816984211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349891731/10000000000 : ℝ)|^1061 ≤ (5481069881907/12500000000000 : ℝ)^805
        have hw : |(5349891731/10000000000 : ℝ)|=(5349891731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242729099/10000000000 : ℝ)|^1061 ≤ (2668413996061/6250000000000 : ℝ)^805
        have hw : |(5242729099/10000000000 : ℝ)|=(5242729099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272912059/1250000000 : ℝ)|^1061 ≤ (13456816984211/100000000000000 : ℝ)^805
        have hw : |(-272912059/1250000000 : ℝ)|=(272912059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s8_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2171010357/5000000000 : ℝ)*x 0 + (833674821/2000000000 : ℝ)*x 1 + (4522598229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171010357/5000000000 : ℝ)^1061 ≤ (33302237334727/100000000000000 : ℝ)^805 := by
    have hnat : (2171010357 : ℕ)^1061*100000000000000^805 ≤ 33302237334727^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171010357 5000000000 33302237334727 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833674821/2000000000 : ℝ)^1061 ≤ (7889534583743/25000000000000 : ℝ)^805 := by
    have hnat : (833674821 : ℕ)^1061*25000000000000^805 ≤ 7889534583743^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833674821 2000000000 7889534583743 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522598229/10000000000 : ℝ)^1061 ≤ (17569812159059/50000000000000 : ℝ)^805 := by
    have hnat : (4522598229 : ℕ)^1061*50000000000000^805 ≤ 17569812159059^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522598229 10000000000 17569812159059 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171010357/5000000000 : ℝ), (833674821/2000000000 : ℝ), (4522598229/10000000000 : ℝ)] ![(33302237334727/100000000000000 : ℝ), (7889534583743/25000000000000 : ℝ), (17569812159059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171010357/5000000000 : ℝ)|^1061 ≤ (33302237334727/100000000000000 : ℝ)^805
        have hw : |(2171010357/5000000000 : ℝ)|=(2171010357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833674821/2000000000 : ℝ)|^1061 ≤ (7889534583743/25000000000000 : ℝ)^805
        have hw : |(833674821/2000000000 : ℝ)|=(833674821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522598229/10000000000 : ℝ)|^1061 ≤ (17569812159059/50000000000000 : ℝ)^805
        have hw : |(4522598229/10000000000 : ℝ)|=(4522598229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s8_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-523794441/2500000000 : ℝ)*x 0 + (655418091/1250000000 : ℝ)*x 1 + (541499069/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523794441/2500000000 : ℝ)^1061 ≤ (3186402921539/25000000000000 : ℝ)^805 := by
    have hnat : (523794441 : ℕ)^1061*25000000000000^805 ≤ 3186402921539^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523794441 2500000000 3186402921539 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655418091/1250000000 : ℝ)^1061 ≤ (42701231821681/100000000000000 : ℝ)^805 := by
    have hnat : (655418091 : ℕ)^1061*100000000000000^805 ≤ 42701231821681^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655418091 1250000000 42701231821681 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541499069/1000000000 : ℝ)^1061 ≤ (2784572279557/6250000000000 : ℝ)^805 := by
    have hnat : (541499069 : ℕ)^1061*6250000000000^805 ≤ 2784572279557^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541499069 1000000000 2784572279557 6250000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523794441/2500000000 : ℝ), (655418091/1250000000 : ℝ), (541499069/1000000000 : ℝ)] ![(3186402921539/25000000000000 : ℝ), (42701231821681/100000000000000 : ℝ), (2784572279557/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523794441/2500000000 : ℝ)|^1061 ≤ (3186402921539/25000000000000 : ℝ)^805
        have hw : |(-523794441/2500000000 : ℝ)|=(523794441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655418091/1250000000 : ℝ)|^1061 ≤ (42701231821681/100000000000000 : ℝ)^805
        have hw : |(655418091/1250000000 : ℝ)|=(655418091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541499069/1000000000 : ℝ)|^1061 ≤ (2784572279557/6250000000000 : ℝ)^805
        have hw : |(541499069/1000000000 : ℝ)|=(541499069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s8_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305674983/10000000000 : ℝ)*x 0 + (-402206981/2000000000 : ℝ)*x 1 + (676873839/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305674983/10000000000 : ℝ)^1061 ≤ (2710720651937/6250000000000 : ℝ)^805 := by
    have hnat : (5305674983 : ℕ)^1061*6250000000000^805 ≤ 2710720651937^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305674983 10000000000 2710720651937 6250000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402206981/2000000000 : ℝ)^1061 ≤ (377353526203/3125000000000 : ℝ)^805 := by
    have hnat : (402206981 : ℕ)^1061*3125000000000^805 ≤ 377353526203^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402206981 2000000000 377353526203 3125000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676873839/1250000000 : ℝ)^1061 ≤ (22276578355743/50000000000000 : ℝ)^805 := by
    have hnat : (676873839 : ℕ)^1061*50000000000000^805 ≤ 22276578355743^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676873839 1250000000 22276578355743 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305674983/10000000000 : ℝ), (-402206981/2000000000 : ℝ), (676873839/1250000000 : ℝ)] ![(2710720651937/6250000000000 : ℝ), (377353526203/3125000000000 : ℝ), (22276578355743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305674983/10000000000 : ℝ)|^1061 ≤ (2710720651937/6250000000000 : ℝ)^805
        have hw : |(5305674983/10000000000 : ℝ)|=(5305674983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402206981/2000000000 : ℝ)|^1061 ≤ (377353526203/3125000000000 : ℝ)^805
        have hw : |(-402206981/2000000000 : ℝ)|=(402206981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676873839/1250000000 : ℝ)|^1061 ≤ (22276578355743/50000000000000 : ℝ)^805
        have hw : |(676873839/1250000000 : ℝ)|=(676873839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s8_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (212226999/400000000 : ℝ)*x 0 + (5414990723/10000000000 : ℝ)*x 1 + (-2011034901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212226999/400000000 : ℝ)^1061 ≤ (43371530344799/100000000000000 : ℝ)^805 := by
    have hnat : (212226999 : ℕ)^1061*100000000000000^805 ≤ 43371530344799^805*400000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212226999 400000000 43371530344799 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414990723/10000000000 : ℝ)^1061 ≤ (44553156830773/100000000000000 : ℝ)^805 := by
    have hnat : (5414990723 : ℕ)^1061*100000000000000^805 ≤ 44553156830773^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414990723 10000000000 44553156830773 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011034901/10000000000 : ℝ)^1061 ≤ (301882820171/2500000000000 : ℝ)^805 := by
    have hnat : (2011034901 : ℕ)^1061*2500000000000^805 ≤ 301882820171^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011034901 10000000000 301882820171 2500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212226999/400000000 : ℝ), (5414990723/10000000000 : ℝ), (-2011034901/10000000000 : ℝ)] ![(43371530344799/100000000000000 : ℝ), (44553156830773/100000000000000 : ℝ), (301882820171/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212226999/400000000 : ℝ)|^1061 ≤ (43371530344799/100000000000000 : ℝ)^805
        have hw : |(212226999/400000000 : ℝ)|=(212226999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414990723/10000000000 : ℝ)|^1061 ≤ (44553156830773/100000000000000 : ℝ)^805
        have hw : |(5414990723/10000000000 : ℝ)|=(5414990723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011034901/10000000000 : ℝ)|^1061 ≤ (301882820171/2500000000000 : ℝ)^805
        have hw : |(-2011034901/10000000000 : ℝ)|=(2011034901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s8_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (868409379/2000000000 : ℝ)*x 0 + (904267393/2000000000 : ℝ)*x 1 + (1042410467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868409379/2000000000 : ℝ)^1061 ≤ (33302501994339/100000000000000 : ℝ)^805 := by
    have hnat : (868409379 : ℕ)^1061*100000000000000^805 ≤ 33302501994339^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868409379 2000000000 33302501994339 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904267393/2000000000 : ℝ)^1061 ≤ (17563354347713/50000000000000 : ℝ)^805 := by
    have hnat : (904267393 : ℕ)^1061*50000000000000^805 ≤ 17563354347713^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904267393 2000000000 17563354347713 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042410467/2500000000 : ℝ)^1061 ≤ (31570789288573/100000000000000 : ℝ)^805 := by
    have hnat : (1042410467 : ℕ)^1061*100000000000000^805 ≤ 31570789288573^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042410467 2500000000 31570789288573 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868409379/2000000000 : ℝ), (904267393/2000000000 : ℝ), (1042410467/2500000000 : ℝ)] ![(33302501994339/100000000000000 : ℝ), (17563354347713/50000000000000 : ℝ), (31570789288573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868409379/2000000000 : ℝ)|^1061 ≤ (33302501994339/100000000000000 : ℝ)^805
        have hw : |(868409379/2000000000 : ℝ)|=(868409379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904267393/2000000000 : ℝ)|^1061 ≤ (17563354347713/50000000000000 : ℝ)^805
        have hw : |(904267393/2000000000 : ℝ)|=(904267393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042410467/2500000000 : ℝ)|^1061 ≤ (31570789288573/100000000000000 : ℝ)^805
        have hw : |(1042410467/2500000000 : ℝ)|=(1042410467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11007/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (344/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7333/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11007/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11007/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11007/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11007/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11007/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11007/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11007/100000 : ℝ) ^ (4243/1024 : ℝ) ≤ (427723335778723/4000000000000000000 : ℝ) := by
    have hpowers : (11007/100000 : ℝ)^4243 ≤ (427723335778723/4000000000000000000 : ℝ)^1024 := by
      have hnat : (11007 : ℕ)^4243*4000000000000000000^1024 ≤ 427723335778723^1024*100000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11007 100000 427723335778723 4000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11007/100000 : ℝ)) (X := (427723335778723/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14667/100000 : ℝ) ^ (4243/1024 : ℝ) ≤ (35130922384991601/100000000000000000000 : ℝ) := by
    have hpowers : (14667/100000 : ℝ)^4243 ≤ (35130922384991601/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14667 : ℕ)^4243*100000000000000000000^1024 ≤ 35130922384991601^1024*100000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14667 100000 35130922384991601 100000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14667/100000 : ℝ)) (X := (35130922384991601/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000427723335778723/2000000000000000000 : ℝ) ≤ (2500129022262777/2500000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (2000427723335778723/2000000000000000000 : ℝ)^1024 ≤ (2500129022262777/2500000000000000 : ℝ)^4243 := by
      have hnat : (2000427723335778723 : ℕ)^1024*2500000000000000^4243 ≤ 2500129022262777^4243*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000427723335778723 2000000000000000000 2500129022262777 2500000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500129022262777/2500000000000000 : ℝ)) (X := (2000427723335778723/2000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011456001444864919/25000000000000000000 : ℝ) ≤ (2000221143660643/2000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (25011456001444864919/25000000000000000000 : ℝ)^1024 ≤ (2000221143660643/2000000000000000 : ℝ)^4243 := by
      have hnat : (25011456001444864919 : ℕ)^1024*2000000000000000^4243 ≤ 2000221143660643^4243*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011456001444864919 25000000000000000000 2000221143660643 2000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221143660643/2000000000000000 : ℝ)) (X := (25011456001444864919/25000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035130922384991601/50000000000000000000 : ℝ) ≤ (5000847673777661/5000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50035130922384991601/50000000000000000000 : ℝ)^1024 ≤ (5000847673777661/5000000000000000 : ℝ)^4243 := by
      have hnat : (50035130922384991601 : ℕ)^1024*5000000000000000^4243 ≤ 5000847673777661^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035130922384991601 50000000000000000000 5000847673777661 5000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000847673777661/5000000000000000 : ℝ)) (X := (50035130922384991601/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(427723335778723/4000000000000000000 : ℝ) ≤ ((6098151464595195297/6100000000000000000 : ℝ)+2*(589629252107/366000000000000 : ℝ)*(11007/100000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (6098151464595195297/6100000000000000000 : ℝ)+2*(589629252107/366000000000000 : ℝ)*(11007/100000 : ℝ)=(2500129022262777/2500000000000000 : ℝ) by norm_num, show 1+2*(427723335778723/4000000000000000000 : ℝ)=(2000427723335778723/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35130922384991601/100000000000000000000 : ℝ)+(427723335778723/4000000000000000000 : ℝ) ≤ ((6098151464595195297/6100000000000000000 : ℝ)+(589629252107/366000000000000 : ℝ)*((14667/100000 : ℝ)+(11007/100000 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (6098151464595195297/6100000000000000000 : ℝ)+(589629252107/366000000000000 : ℝ)*((14667/100000 : ℝ)+(11007/100000 : ℝ))=(2000221143660643/2000000000000000 : ℝ) by norm_num, show 1+(35130922384991601/100000000000000000000 : ℝ)+(427723335778723/4000000000000000000 : ℝ)=(25011456001444864919/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35130922384991601/100000000000000000000 : ℝ) ≤ ((6098151464595195297/6100000000000000000 : ℝ)+2*(589629252107/366000000000000 : ℝ)*(14667/100000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (6098151464595195297/6100000000000000000 : ℝ)+2*(589629252107/366000000000000 : ℝ)*(14667/100000 : ℝ)=(5000847673777661/5000000000000000 : ℝ) by norm_num, show 1+2*(35130922384991601/100000000000000000000 : ℝ)=(50035130922384991601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6098151464595195297/6100000000000000000 : ℝ)*(X 1 0+X 2 0)+(589629252107/366000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (11007/100000 : ℝ)) (hi := (14667/100000 : ℝ)) (c := (6098151464595195297/6100000000000000000 : ℝ)) (alpha := (589629252107/366000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6098151464595195297/6100000000000000000 : ℝ)*(X 0 1+X 2 1)+(589629252107/366000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (11007/100000 : ℝ)) (hi := (14667/100000 : ℝ)) (c := (6098151464595195297/6100000000000000000 : ℝ)) (alpha := (589629252107/366000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6098151464595195297/6100000000000000000 : ℝ)*(X 0 2+X 1 2)+(589629252107/366000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (11007/100000 : ℝ)) (hi := (14667/100000 : ℝ)) (c := (6098151464595195297/6100000000000000000 : ℝ)) (alpha := (589629252107/366000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2095165087/10000000000 : ℝ)*X 0 0+(1083121877/2000000000 : ℝ)*X 0 1+(524272911/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674945851/5000000000 : ℝ)*X 1 0+(-545824127/2500000000 : ℝ)*X 1 1+(2621364551/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349891731/10000000000 : ℝ)*X 2 0+(5242729099/10000000000 : ℝ)*X 2 1+(-272912059/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171010357/5000000000 : ℝ)*X 0 0+(833674821/2000000000 : ℝ)*X 0 1+(4522598229/10000000000 : ℝ)*X 0 2+(2171010357/5000000000 : ℝ)*X 1 0+(833674821/2000000000 : ℝ)*X 1 1+(4522598229/10000000000 : ℝ)*X 1 2+(2171010357/5000000000 : ℝ)*X 2 0+(833674821/2000000000 : ℝ)*X 2 1+(4522598229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-523794441/2500000000 : ℝ)*X 0 0+(655418091/1250000000 : ℝ)*X 0 1+(541499069/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305674983/10000000000 : ℝ)*X 1 0+(-402206981/2000000000 : ℝ)*X 1 1+(676873839/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212226999/400000000 : ℝ)*X 2 0+(5414990723/10000000000 : ℝ)*X 2 1+(-2011034901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((868409379/2000000000 : ℝ)*X 0 0+(904267393/2000000000 : ℝ)*X 0 1+(1042410467/2500000000 : ℝ)*X 0 2+(868409379/2000000000 : ℝ)*X 1 0+(904267393/2000000000 : ℝ)*X 1 1+(1042410467/2500000000 : ℝ)*X 1 2+(868409379/2000000000 : ℝ)*X 2 0+(904267393/2000000000 : ℝ)*X 2 1+(1042410467/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (441946612087706205254078833/305000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139466779/25000000000000 : ℝ)*(base19) + (100434531/20000000000000 : ℝ)*(base23) + (19687271/25000000000000 : ℝ)*(upper3) + (46570607/100000000000000 : ℝ)*(upper4) + (63823807/100000000000000 : ℝ)*(upper5) + (4303725684184763/100000000000000 : ℝ)*(major0) + (4303725684184763/100000000000000 : ℝ)*(major1) + (4303725684184763/100000000000000 : ℝ)*(major2) + (1446089903258819/25000000000000 : ℝ)*(sp0) + (1156873924283959/20000000000000 : ℝ)*(sp1) + (1156873935422851/20000000000000 : ℝ)*(sp2) + (352884490970993/12500000000000 : ℝ)*(sp3) + (5283125817/50000000000000 : ℝ)*(sp4) + (521301449/10000000000000 : ℝ)*(sp7) + (1411540570391217/50000000000000 : ℝ)*(f.failure) + (578437017928691/10000000000000 : ℝ)*(f.sum) + (16461845711759/18300000000000000000000000000 : ℝ)*base66 + (8954779761872028833/1830000000000000000000000000000000 : ℝ)*base67 + (8168798395347971167/1830000000000000000000000000000000 : ℝ)*base70 + (18360308747547971167/1830000000000000000000000000000000 : ℝ)*base72 + (116339205932641/18300000000000000000000000000 : ℝ)*base73 + (5526282549447971167/1830000000000000000000000000000000 : ℝ)*base76 + (18170728956002028833/1830000000000000000000000000000000 : ℝ)*base77 + (9600057680517971167/1830000000000000000000000000000000 : ℝ)*base80 + (45778536443159/18300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (811843/5000000000000000000000 : ℝ)*base90 + (811843/5000000000000000000000 : ℝ)*base92 + (811843/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24814014117523112749687/6100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (369476199/50000000000000 : ℝ)*(base19) + (49824471/6250000000000 : ℝ)*(base23) + (264151619/100000000000000 : ℝ)*(lower1) + (17495157/20000000000000 : ℝ)*(upper3) + (29993059/100000000000000 : ℝ)*(lower4) + (3521171/4000000000000 : ℝ)*(upper5) + (4334646888873259/100000000000000 : ℝ)*(major0) + (4334646888873259/100000000000000 : ℝ)*(major1) + (4334646888873259/100000000000000 : ℝ)*(major2) + (1259132709/100000000000000 : ℝ)*(sp2) + (728241170193339/12500000000000 : ℝ)*(sp4) + (2912964311297157/50000000000000 : ℝ)*(sp5) + (1456481826305617/25000000000000 : ℝ)*(sp6) + (355420535075511/12500000000000 : ℝ)*(sp7) + (355420535075511/12500000000000 : ℝ)*(f.failure) + (728241170193339/12500000000000 : ℝ)*(f.sum) + (4484322986887/18300000000000000000000000000 : ℝ)*base66 + (12907563271013238769/1830000000000000000000000000000000 : ℝ)*base67 + (17483074924373238769/1830000000000000000000000000000000 : ℝ)*base69 + (17049365012766761231/1830000000000000000000000000000000 : ℝ)*base72 + (48567597381713/18300000000000000000000000000 : ℝ)*base73 + (8455162602666761231/1830000000000000000000000000000000 : ℝ)*base76 + (4309309290876761231/1830000000000000000000000000000000 : ℝ)*base78 + (15913833800243238769/1830000000000000000000000000000000 : ℝ)*base79 + (174765947062313/18300000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15088469/1250000000000000000000 : ℝ)*base90 + (15088469/1250000000000000000000 : ℝ)*base92 + (15088469/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1284_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11007/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1284_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1284_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1284_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1284_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1284_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1284_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

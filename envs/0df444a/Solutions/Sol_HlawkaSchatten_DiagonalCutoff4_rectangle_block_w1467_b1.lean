-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1467_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:09:28.88155+00:00
-- url     : https://prove2.me/submissions/23f5c1c2-a732-4f95-a8be-83411128a1ef

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
theorem support_rectangle_w1467_s3_0 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1935755299/10000000000 : ℝ)*x 0 + (2722302523/5000000000 : ℝ)*x 1 + (1042025011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1935755299/10000000000 : ℝ)^4431 ≤ (184640902351/1562500000000 : ℝ)^3407 := by
    have hnat : (1935755299 : ℕ)^4431*1562500000000^3407 ≤ 184640902351^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935755299 10000000000 184640902351 1562500000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722302523/5000000000 : ℝ)^4431 ≤ (45353316496187/100000000000000 : ℝ)^3407 := by
    have hnat : (2722302523 : ℕ)^4431*100000000000000^3407 ≤ 45353316496187^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722302523 5000000000 45353316496187 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042025011/2000000000 : ℝ)^4431 ≤ (8565933146509/20000000000000 : ℝ)^3407 := by
    have hnat : (1042025011 : ℕ)^4431*20000000000000^3407 ≤ 8565933146509^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042025011 2000000000 8565933146509 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1935755299/10000000000 : ℝ), (2722302523/5000000000 : ℝ), (1042025011/2000000000 : ℝ)] ![(184640902351/1562500000000 : ℝ), (45353316496187/100000000000000 : ℝ), (8565933146509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1935755299/10000000000 : ℝ)|^4431 ≤ (184640902351/1562500000000 : ℝ)^3407
        have hw : |(-1935755299/10000000000 : ℝ)|=(1935755299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722302523/5000000000 : ℝ)|^4431 ≤ (45353316496187/100000000000000 : ℝ)^3407
        have hw : |(2722302523/5000000000 : ℝ)|=(2722302523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042025011/2000000000 : ℝ)|^4431 ≤ (8565933146509/20000000000000 : ℝ)^3407
        have hw : |(1042025011/2000000000 : ℝ)|=(1042025011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s3_1 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071076053/2000000000 : ℝ)*x 0 + (-128506071/625000000 : ℝ)*x 1 + (325632781/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071076053/2000000000 : ℝ)^4431 ≤ (22194540870211/50000000000000 : ℝ)^3407 := by
    have hnat : (1071076053 : ℕ)^4431*50000000000000^3407 ≤ 22194540870211^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071076053 2000000000 22194540870211 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128506071/625000000 : ℝ)^4431 ≤ (1597657310373/12500000000000 : ℝ)^3407 := by
    have hnat : (128506071 : ℕ)^4431*12500000000000^3407 ≤ 1597657310373^3407*625000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128506071 625000000 1597657310373 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325632781/625000000 : ℝ)^4431 ≤ (5353707469521/12500000000000 : ℝ)^3407 := by
    have hnat : (325632781 : ℕ)^4431*12500000000000^3407 ≤ 5353707469521^3407*625000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325632781 625000000 5353707469521 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071076053/2000000000 : ℝ), (-128506071/625000000 : ℝ), (325632781/625000000 : ℝ)] ![(22194540870211/50000000000000 : ℝ), (1597657310373/12500000000000 : ℝ), (5353707469521/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071076053/2000000000 : ℝ)|^4431 ≤ (22194540870211/50000000000000 : ℝ)^3407
        have hw : |(1071076053/2000000000 : ℝ)|=(1071076053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128506071/625000000 : ℝ)|^4431 ≤ (1597657310373/12500000000000 : ℝ)^3407
        have hw : |(-128506071/625000000 : ℝ)|=(128506071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325632781/625000000 : ℝ)|^4431 ≤ (5353707469521/12500000000000 : ℝ)^3407
        have hw : |(325632781/625000000 : ℝ)|=(325632781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s3_2 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355380921/10000000000 : ℝ)*x 0 + (5210123869/10000000000 : ℝ)*x 1 + (-2056097091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355380921/10000000000 : ℝ)^4431 ≤ (2774318050753/6250000000000 : ℝ)^3407 := by
    have hnat : (5355380921 : ℕ)^4431*6250000000000^3407 ≤ 2774318050753^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355380921 10000000000 2774318050753 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5210123869/10000000000 : ℝ)^4431 ≤ (42829653052791/100000000000000 : ℝ)^3407 := by
    have hnat : (5210123869 : ℕ)^4431*100000000000000^3407 ≤ 42829653052791^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210123869 10000000000 42829653052791 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056097091/10000000000 : ℝ)^4431 ≤ (1597657264897/12500000000000 : ℝ)^3407 := by
    have hnat : (2056097091 : ℕ)^4431*12500000000000^3407 ≤ 1597657264897^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056097091 10000000000 1597657264897 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355380921/10000000000 : ℝ), (5210123869/10000000000 : ℝ), (-2056097091/10000000000 : ℝ)] ![(2774318050753/6250000000000 : ℝ), (42829653052791/100000000000000 : ℝ), (1597657264897/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355380921/10000000000 : ℝ)|^4431 ≤ (2774318050753/6250000000000 : ℝ)^3407
        have hw : |(5355380921/10000000000 : ℝ)|=(5355380921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5210123869/10000000000 : ℝ)|^4431 ≤ (42829653052791/100000000000000 : ℝ)^3407
        have hw : |(5210123869/10000000000 : ℝ)|=(5210123869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056097091/10000000000 : ℝ)|^4431 ≤ (1597657264897/12500000000000 : ℝ)^3407
        have hw : |(-2056097091/10000000000 : ℝ)|=(2056097091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s3_3 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072668301/2500000000 : ℝ)*x 0 + (4040039059/10000000000 : ℝ)*x 1 + (4554927107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072668301/2500000000 : ℝ)^4431 ≤ (16635970528283/50000000000000 : ℝ)^3407 := by
    have hnat : (1072668301 : ℕ)^4431*50000000000000^3407 ≤ 16635970528283^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072668301 2500000000 16635970528283 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4040039059/10000000000 : ℝ)^4431 ≤ (15383378589917/50000000000000 : ℝ)^3407 := by
    have hnat : (4040039059 : ℕ)^4431*50000000000000^3407 ≤ 15383378589917^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4040039059 10000000000 15383378589917 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4554927107/10000000000 : ℝ)^4431 ≤ (35961301748721/100000000000000 : ℝ)^3407 := by
    have hnat : (4554927107 : ℕ)^4431*100000000000000^3407 ≤ 35961301748721^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554927107 10000000000 35961301748721 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072668301/2500000000 : ℝ), (4040039059/10000000000 : ℝ), (4554927107/10000000000 : ℝ)] ![(16635970528283/50000000000000 : ℝ), (15383378589917/50000000000000 : ℝ), (35961301748721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072668301/2500000000 : ℝ)|^4431 ≤ (16635970528283/50000000000000 : ℝ)^3407
        have hw : |(1072668301/2500000000 : ℝ)|=(1072668301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4040039059/10000000000 : ℝ)|^4431 ≤ (15383378589917/50000000000000 : ℝ)^3407
        have hw : |(4040039059/10000000000 : ℝ)|=(4040039059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4554927107/10000000000 : ℝ)|^4431 ≤ (35961301748721/100000000000000 : ℝ)^3407
        have hw : |(4554927107/10000000000 : ℝ)|=(4554927107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s3_4 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-19357911/100000000 : ℝ)*x 0 + (2605688107/5000000000 : ℝ)*x 1 + (5443344007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19357911/100000000 : ℝ)^4431 ≤ (5908650994649/50000000000000 : ℝ)^3407 := by
    have hnat : (19357911 : ℕ)^4431*50000000000000^3407 ≤ 5908650994649^3407*100000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19357911 100000000 5908650994649 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2605688107/5000000000 : ℝ)^4431 ≤ (42843042597103/100000000000000 : ℝ)^3407 := by
    have hnat : (2605688107 : ℕ)^4431*100000000000000^3407 ≤ 42843042597103^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605688107 5000000000 42843042597103 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443344007/10000000000 : ℝ)^4431 ≤ (45339655395677/100000000000000 : ℝ)^3407 := by
    have hnat : (5443344007 : ℕ)^4431*100000000000000^3407 ≤ 45339655395677^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443344007 10000000000 45339655395677 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19357911/100000000 : ℝ), (2605688107/5000000000 : ℝ), (5443344007/10000000000 : ℝ)] ![(5908650994649/50000000000000 : ℝ), (42843042597103/100000000000000 : ℝ), (45339655395677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19357911/100000000 : ℝ)|^4431 ≤ (5908650994649/50000000000000 : ℝ)^3407
        have hw : |(-19357911/100000000 : ℝ)|=(19357911/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2605688107/5000000000 : ℝ)|^4431 ≤ (42843042597103/100000000000000 : ℝ)^3407
        have hw : |(2605688107/5000000000 : ℝ)|=(2605688107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443344007/10000000000 : ℝ)|^4431 ≤ (45339655395677/100000000000000 : ℝ)^3407
        have hw : |(5443344007/10000000000 : ℝ)|=(5443344007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s3_5 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294278457/10000000000 : ℝ)*x 0 + (-18228777/100000000 : ℝ)*x 1 + (5443344151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294278457/10000000000 : ℝ)^4431 ≤ (8746308325267/20000000000000 : ℝ)^3407 := by
    have hnat : (5294278457 : ℕ)^4431*20000000000000^3407 ≤ 8746308325267^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294278457 10000000000 8746308325267 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18228777/100000000 : ℝ)^4431 ≤ (546440070513/5000000000000 : ℝ)^3407 := by
    have hnat : (18228777 : ℕ)^4431*5000000000000^3407 ≤ 546440070513^3407*100000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18228777 100000000 546440070513 5000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443344151/10000000000 : ℝ)^4431 ≤ (11334914238901/25000000000000 : ℝ)^3407 := by
    have hnat : (5443344151 : ℕ)^4431*25000000000000^3407 ≤ 11334914238901^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443344151 10000000000 11334914238901 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294278457/10000000000 : ℝ), (-18228777/100000000 : ℝ), (5443344151/10000000000 : ℝ)] ![(8746308325267/20000000000000 : ℝ), (546440070513/5000000000000 : ℝ), (11334914238901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294278457/10000000000 : ℝ)|^4431 ≤ (8746308325267/20000000000000 : ℝ)^3407
        have hw : |(5294278457/10000000000 : ℝ)|=(5294278457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18228777/100000000 : ℝ)|^4431 ≤ (546440070513/5000000000000 : ℝ)^3407
        have hw : |(-18228777/100000000 : ℝ)|=(18228777/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443344151/10000000000 : ℝ)|^4431 ≤ (11334914238901/25000000000000 : ℝ)^3407
        have hw : |(5443344151/10000000000 : ℝ)|=(5443344151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s3_6 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647139347/5000000000 : ℝ)*x 0 + (5443344073/10000000000 : ℝ)*x 1 + (-1822877481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647139347/5000000000 : ℝ)^4431 ≤ (43731544172379/100000000000000 : ℝ)^3407 := by
    have hnat : (2647139347 : ℕ)^4431*100000000000000^3407 ≤ 43731544172379^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647139347 5000000000 43731544172379 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443344073/10000000000 : ℝ)^4431 ≤ (11334914027661/25000000000000 : ℝ)^3407 := by
    have hnat : (5443344073 : ℕ)^4431*25000000000000^3407 ≤ 11334914027661^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443344073 10000000000 11334914027661 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1822877481/10000000000 : ℝ)^4431 ≤ (218575994053/2000000000000 : ℝ)^3407 := by
    have hnat : (1822877481 : ℕ)^4431*2000000000000^3407 ≤ 218575994053^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822877481 10000000000 218575994053 2000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647139347/5000000000 : ℝ), (5443344073/10000000000 : ℝ), (-1822877481/10000000000 : ℝ)] ![(43731544172379/100000000000000 : ℝ), (11334914027661/25000000000000 : ℝ), (218575994053/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647139347/5000000000 : ℝ)|^4431 ≤ (43731544172379/100000000000000 : ℝ)^3407
        have hw : |(2647139347/5000000000 : ℝ)|=(2647139347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443344073/10000000000 : ℝ)|^4431 ≤ (11334914027661/25000000000000 : ℝ)^3407
        have hw : |(5443344073/10000000000 : ℝ)|=(5443344073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1822877481/10000000000 : ℝ)|^4431 ≤ (218575994053/2000000000000 : ℝ)^3407
        have hw : |(-1822877481/10000000000 : ℝ)|=(1822877481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s3_7 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (429075143/1000000000 : ℝ)*x 0 + (56902243/125000000 : ℝ)*x 1 + (2021403699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429075143/1000000000 : ℝ)^4431 ≤ (8318182494897/25000000000000 : ℝ)^3407 := by
    have hnat : (429075143 : ℕ)^4431*25000000000000^3407 ≤ 8318182494897^3407*1000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429075143 1000000000 8318182494897 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56902243/125000000 : ℝ)^4431 ≤ (17966545704703/50000000000000 : ℝ)^3407 := by
    have hnat : (56902243 : ℕ)^4431*50000000000000^3407 ≤ 17966545704703^3407*125000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56902243 125000000 17966545704703 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021403699/5000000000 : ℝ)^4431 ≤ (76985446471/250000000000 : ℝ)^3407 := by
    have hnat : (2021403699 : ℕ)^4431*250000000000^3407 ≤ 76985446471^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021403699 5000000000 76985446471 250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429075143/1000000000 : ℝ), (56902243/125000000 : ℝ), (2021403699/5000000000 : ℝ)] ![(8318182494897/25000000000000 : ℝ), (17966545704703/50000000000000 : ℝ), (76985446471/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429075143/1000000000 : ℝ)|^4431 ≤ (8318182494897/25000000000000 : ℝ)^3407
        have hw : |(429075143/1000000000 : ℝ)|=(429075143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56902243/125000000 : ℝ)|^4431 ≤ (17966545704703/50000000000000 : ℝ)^3407
        have hw : |(56902243/125000000 : ℝ)|=(56902243/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2021403699/5000000000 : ℝ)|^4431 ≤ (76985446471/250000000000 : ℝ)^3407
        have hw : |(2021403699/5000000000 : ℝ)|=(2021403699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1467_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (17/160 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3117/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10067/100000 : ℝ) ^ (4429/1024 : ℝ) ≤ (973594353167467/20000000000000000000 : ℝ) := by
    have hpowers : (10067/100000 : ℝ)^4429 ≤ (973594353167467/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10067 : ℕ)^4429*20000000000000000000^1024 ≤ 973594353167467^1024*100000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10067 100000 973594353167467 20000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10067/100000 : ℝ)) (X := (973594353167467/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8097/50000 : ℝ) ^ (4429/1024 : ℝ) ≤ (2377837806990159/6250000000000000000 : ℝ) := by
    have hpowers : (8097/50000 : ℝ)^4429 ≤ (2377837806990159/6250000000000000000 : ℝ)^1024 := by
      have hnat : (8097 : ℕ)^4429*6250000000000000000^1024 ≤ 2377837806990159^1024*50000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8097 50000 2377837806990159 6250000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8097/50000 : ℝ)) (X := (2377837806990159/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000973594353167467/10000000000000000000 : ℝ) ≤ (10000225089931979/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (10000973594353167467/10000000000000000000 : ℝ)^1024 ≤ (10000225089931979/10000000000000000 : ℝ)^4429 := by
      have hnat : (10000973594353167467 : ℕ)^1024*10000000000000000^4429 ≤ 10000225089931979^4429*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000973594353167467 10000000000000000000 10000225089931979 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000225089931979/10000000000000000 : ℝ)) (X := (10000973594353167467/10000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042913376677679879/100000000000000000000 : ℝ) ≤ (40003968033483/40000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (100042913376677679879/100000000000000000000 : ℝ)^1024 ≤ (40003968033483/40000000000000 : ℝ)^4429 := by
      have hnat : (100042913376677679879 : ℕ)^1024*40000000000000^4429 ≤ 40003968033483^4429*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042913376677679879 100000000000000000000 40003968033483 40000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40003968033483/40000000000000 : ℝ)) (X := (100042913376677679879/100000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127377837806990159/3125000000000000000 : ℝ) ≤ (10001758926809521/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (3127377837806990159/3125000000000000000 : ℝ)^1024 ≤ (10001758926809521/10000000000000000 : ℝ)^4429 := by
      have hnat : (3127377837806990159 : ℕ)^1024*10000000000000000^4429 ≤ 10001758926809521^4429*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127377837806990159 3125000000000000000 10001758926809521 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001758926809521/10000000000000000 : ℝ)) (X := (3127377837806990159/3125000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(973594353167467/20000000000000000000 : ℝ) ≤ ((61255937990167020019/61270000000000000000 : ℝ)+2*(766918438771/612700000000000 : ℝ)*(10067/100000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (61255937990167020019/61270000000000000000 : ℝ)+2*(766918438771/612700000000000 : ℝ)*(10067/100000 : ℝ)=(10000225089931979/10000000000000000 : ℝ) by norm_num, show 1+2*(973594353167467/20000000000000000000 : ℝ)=(10000973594353167467/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2377837806990159/6250000000000000000 : ℝ)+(973594353167467/20000000000000000000 : ℝ) ≤ ((61255937990167020019/61270000000000000000 : ℝ)+(766918438771/612700000000000 : ℝ)*((8097/50000 : ℝ)+(10067/100000 : ℝ)))^(4429/1024 : ℝ) := by
    rw [show (61255937990167020019/61270000000000000000 : ℝ)+(766918438771/612700000000000 : ℝ)*((8097/50000 : ℝ)+(10067/100000 : ℝ))=(40003968033483/40000000000000 : ℝ) by norm_num, show 1+(2377837806990159/6250000000000000000 : ℝ)+(973594353167467/20000000000000000000 : ℝ)=(100042913376677679879/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2377837806990159/6250000000000000000 : ℝ) ≤ ((61255937990167020019/61270000000000000000 : ℝ)+2*(766918438771/612700000000000 : ℝ)*(8097/50000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (61255937990167020019/61270000000000000000 : ℝ)+2*(766918438771/612700000000000 : ℝ)*(8097/50000 : ℝ)=(10001758926809521/10000000000000000 : ℝ) by norm_num, show 1+2*(2377837806990159/6250000000000000000 : ℝ)=(3127377837806990159/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (61255937990167020019/61270000000000000000 : ℝ)*(X 1 0+X 2 0)+(766918438771/612700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (10067/100000 : ℝ)) (hi := (8097/50000 : ℝ)) (c := (61255937990167020019/61270000000000000000 : ℝ)) (alpha := (766918438771/612700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (61255937990167020019/61270000000000000000 : ℝ)*(X 0 1+X 2 1)+(766918438771/612700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (10067/100000 : ℝ)) (hi := (8097/50000 : ℝ)) (c := (61255937990167020019/61270000000000000000 : ℝ)) (alpha := (766918438771/612700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (61255937990167020019/61270000000000000000 : ℝ)*(X 0 2+X 1 2)+(766918438771/612700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (10067/100000 : ℝ)) (hi := (8097/50000 : ℝ)) (c := (61255937990167020019/61270000000000000000 : ℝ)) (alpha := (766918438771/612700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1935755299/10000000000 : ℝ)*X 0 0+(2722302523/5000000000 : ℝ)*X 0 1+(1042025011/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071076053/2000000000 : ℝ)*X 1 0+(-128506071/625000000 : ℝ)*X 1 1+(325632781/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355380921/10000000000 : ℝ)*X 2 0+(5210123869/10000000000 : ℝ)*X 2 1+(-2056097091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1072668301/2500000000 : ℝ)*X 0 0+(4040039059/10000000000 : ℝ)*X 0 1+(4554927107/10000000000 : ℝ)*X 0 2+(1072668301/2500000000 : ℝ)*X 1 0+(4040039059/10000000000 : ℝ)*X 1 1+(4554927107/10000000000 : ℝ)*X 1 2+(1072668301/2500000000 : ℝ)*X 2 0+(4040039059/10000000000 : ℝ)*X 2 1+(4554927107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-19357911/100000000 : ℝ)*X 0 0+(2605688107/5000000000 : ℝ)*X 0 1+(5443344007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294278457/10000000000 : ℝ)*X 1 0+(-18228777/100000000 : ℝ)*X 1 1+(5443344151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647139347/5000000000 : ℝ)*X 2 0+(5443344073/10000000000 : ℝ)*X 2 1+(-1822877481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((429075143/1000000000 : ℝ)*X 0 0+(56902243/125000000 : ℝ)*X 0 1+(2021403699/5000000000 : ℝ)*X 0 2+(429075143/1000000000 : ℝ)*X 1 0+(56902243/125000000 : ℝ)*X 1 1+(2021403699/5000000000 : ℝ)*X 1 2+(429075143/1000000000 : ℝ)*X 2 0+(56902243/125000000 : ℝ)*X 2 1+(2021403699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6602129112704188558374321399/1531750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116569959/25000000000000 : ℝ)*(base19) + (171917619/25000000000000 : ℝ)*(base23) + (10075291/6250000000000 : ℝ)*(lower2) + (7619733/50000000000000 : ℝ)*(lower3) + (52328959/50000000000000 : ℝ)*(lower5) + (1551730571997669/50000000000000 : ℝ)*(major0) + (1551730571997669/50000000000000 : ℝ)*(major1) + (1551730571997669/50000000000000 : ℝ)*(major2) + (533094144922451/12500000000000 : ℝ)*(sp0) + (2132376350451829/50000000000000 : ℝ)*(sp1) + (2132376239756509/50000000000000 : ℝ)*(sp2) + (242770983648901/12500000000000 : ℝ)*(sp3) + (3901943/50000000000000 : ℝ)*(sp4) + (221588613/20000000000000 : ℝ)*(sp7) + (1942168977134273/100000000000000 : ℝ)*(f.failure) + (2132376583591747/50000000000000 : ℝ)*(f.sum) + (34135988336487/7658750000000000000000000000 : ℝ)*base65 + (16895287217169764289/3063500000000000000000000000000000 : ℝ)*base68 + (33999154885243764289/3063500000000000000000000000000000 : ℝ)*base70 + (10342418771727764289/3063500000000000000000000000000000 : ℝ)*base72 + (14361147484621/15317500000000000000000000000 : ℝ)*base74 + (3044070375344764289/3063500000000000000000000000000000 : ℝ)*base76 + (17231679478935764289/3063500000000000000000000000000000 : ℝ)*base78 + (37587872801114764289/3063500000000000000000000000000000 : ℝ)*base80 + (35903466632641/15317500000000000000000000000 : ℝ)*base82 + (5202461/1000000000000000000000 : ℝ)*base89 + (5202461/1000000000000000000000 : ℝ)*base91 + (5202461/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2263254835198389584951088579/765875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51559377/12500000000000 : ℝ)*(base23) + (1201801/25000000000000 : ℝ)*(lower2) + (15120771/25000000000000 : ℝ)*(upper3) + (72837671/100000000000000 : ℝ)*(lower4) + (1568536346381253/50000000000000 : ℝ)*(major0) + (1568536346381253/50000000000000 : ℝ)*(major1) + (1568536346381253/50000000000000 : ℝ)*(major2) + (68368033/100000000000000 : ℝ)*(sp1) + (7952856171/100000000000000 : ℝ)*(sp2) + (3349011/800000000000 : ℝ)*(sp3) + (33679234012841/781250000000 : ℝ)*(sp4) + (134716933914863/3125000000000 : ℝ)*(sp5) + (2155466794156231/50000000000000 : ℝ)*(sp6) + (245400364343859/12500000000000 : ℝ)*(sp7) + (61350104168039/3125000000000 : ℝ)*(f.failure) + (33679234012841/781250000000 : ℝ)*(f.sum) + (673852493013/15317500000000000000000000000 : ℝ)*base65 + (15024317368674103807/3063500000000000000000000000000000 : ℝ)*base67 + (149307710834434103807/3063500000000000000000000000000000 : ℝ)*base69 + (4043096724434103807/3063500000000000000000000000000000 : ℝ)*base71 + (83919248075831/30635000000000000000000000000 : ℝ)*base73 + (33817618246586103807/3063500000000000000000000000000000 : ℝ)*base75 + (108174516190302896193/3063500000000000000000000000000000 : ℝ)*base78 + (53221889849208603807/3063500000000000000000000000000000 : ℝ)*base79 + (28848447910599/7658750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (45923/31250000000000000000 : ℝ)*base89 + (45923/31250000000000000000 : ℝ)*base91 + (45923/31250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1467_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (17/160 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3117/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1467_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1467_s4_0 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-484121491/2500000000 : ℝ)*x 0 + (5439914743/10000000000 : ℝ)*x 1 + (651791759/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (484121491/2500000000 : ℝ)^4431 ≤ (5911409556353/50000000000000 : ℝ)^3407 := by
    have hnat : (484121491 : ℕ)^4431*50000000000000^3407 ≤ 5911409556353^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484121491 2500000000 5911409556353 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439914743/10000000000 : ℝ)^4431 ≤ (906050205377/2000000000000 : ℝ)^3407 := by
    have hnat : (5439914743 : ℕ)^4431*2000000000000^3407 ≤ 906050205377^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439914743 10000000000 906050205377 2000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651791759/1250000000 : ℝ)^4431 ≤ (42874670606051/100000000000000 : ℝ)^3407 := by
    have hnat : (651791759 : ℕ)^4431*100000000000000^3407 ≤ 42874670606051^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651791759 1250000000 42874670606051 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-484121491/2500000000 : ℝ), (5439914743/10000000000 : ℝ), (651791759/1250000000 : ℝ)] ![(5911409556353/50000000000000 : ℝ), (906050205377/2000000000000 : ℝ), (42874670606051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-484121491/2500000000 : ℝ)|^4431 ≤ (5911409556353/50000000000000 : ℝ)^3407
        have hw : |(-484121491/2500000000 : ℝ)|=(484121491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439914743/10000000000 : ℝ)|^4431 ≤ (906050205377/2000000000000 : ℝ)^3407
        have hw : |(5439914743/10000000000 : ℝ)|=(5439914743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651791759/1250000000 : ℝ)|^4431 ≤ (42874670606051/100000000000000 : ℝ)^3407
        have hw : |(651791759/1250000000 : ℝ)|=(651791759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s4_1 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677083387/5000000000 : ℝ)*x 0 + (-513036633/2500000000 : ℝ)*x 1 + (1303583517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677083387/5000000000 : ℝ)^4431 ≤ (44376000852227/100000000000000 : ℝ)^3407 := by
    have hnat : (2677083387 : ℕ)^4431*100000000000000^3407 ≤ 44376000852227^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677083387 5000000000 44376000852227 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513036633/2500000000 : ℝ)^4431 ≤ (6374664288869/50000000000000 : ℝ)^3407 := by
    have hnat : (513036633 : ℕ)^4431*50000000000000^3407 ≤ 6374664288869^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513036633 2500000000 6374664288869 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303583517/2500000000 : ℝ)^4431 ≤ (10718667640819/25000000000000 : ℝ)^3407 := by
    have hnat : (1303583517 : ℕ)^4431*25000000000000^3407 ≤ 10718667640819^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303583517 2500000000 10718667640819 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677083387/5000000000 : ℝ), (-513036633/2500000000 : ℝ), (1303583517/2500000000 : ℝ)] ![(44376000852227/100000000000000 : ℝ), (6374664288869/50000000000000 : ℝ), (10718667640819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677083387/5000000000 : ℝ)|^4431 ≤ (44376000852227/100000000000000 : ℝ)^3407
        have hw : |(2677083387/5000000000 : ℝ)|=(2677083387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513036633/2500000000 : ℝ)|^4431 ≤ (6374664288869/50000000000000 : ℝ)^3407
        have hw : |(-513036633/2500000000 : ℝ)|=(513036633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303583517/2500000000 : ℝ)|^4431 ≤ (10718667640819/25000000000000 : ℝ)^3407
        have hw : |(1303583517/2500000000 : ℝ)|=(1303583517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s4_2 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677083389/5000000000 : ℝ)*x 0 + (521433407/1000000000 : ℝ)*x 1 + (-1026073261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677083389/5000000000 : ℝ)^4431 ≤ (2773500055959/6250000000000 : ℝ)^3407 := by
    have hnat : (2677083389 : ℕ)^4431*6250000000000^3407 ≤ 2773500055959^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677083389 5000000000 2773500055959 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521433407/1000000000 : ℝ)^4431 ≤ (42874670584663/100000000000000 : ℝ)^3407 := by
    have hnat : (521433407 : ℕ)^4431*100000000000000^3407 ≤ 42874670584663^3407*1000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521433407 1000000000 42874670584663 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026073261/5000000000 : ℝ)^4431 ≤ (12749328496939/100000000000000 : ℝ)^3407 := by
    have hnat : (1026073261 : ℕ)^4431*100000000000000^3407 ≤ 12749328496939^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026073261 5000000000 12749328496939 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677083389/5000000000 : ℝ), (521433407/1000000000 : ℝ), (-1026073261/5000000000 : ℝ)] ![(2773500055959/6250000000000 : ℝ), (42874670584663/100000000000000 : ℝ), (12749328496939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677083389/5000000000 : ℝ)|^4431 ≤ (2773500055959/6250000000000 : ℝ)^3407
        have hw : |(2677083389/5000000000 : ℝ)|=(2677083389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521433407/1000000000 : ℝ)|^4431 ≤ (42874670584663/100000000000000 : ℝ)^3407
        have hw : |(521433407/1000000000 : ℝ)|=(521433407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026073261/5000000000 : ℝ)|^4431 ≤ (12749328496939/100000000000000 : ℝ)^3407
        have hw : |(-1026073261/5000000000 : ℝ)|=(1026073261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s4_3 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2145563291/5000000000 : ℝ)*x 0 + (2024878027/5000000000 : ℝ)*x 1 + (4545102317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145563291/5000000000 : ℝ)^4431 ≤ (33276513513827/100000000000000 : ℝ)^3407 := by
    have hnat : (2145563291 : ℕ)^4431*100000000000000^3407 ≤ 33276513513827^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145563291 5000000000 33276513513827 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024878027/5000000000 : ℝ)^4431 ≤ (15431516210351/50000000000000 : ℝ)^3407 := by
    have hnat : (2024878027 : ℕ)^4431*50000000000000^3407 ≤ 15431516210351^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024878027 5000000000 15431516210351 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4545102317/10000000000 : ℝ)^4431 ≤ (4482556756101/12500000000000 : ℝ)^3407 := by
    have hnat : (4545102317 : ℕ)^4431*12500000000000^3407 ≤ 4482556756101^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545102317 10000000000 4482556756101 12500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145563291/5000000000 : ℝ), (2024878027/5000000000 : ℝ), (4545102317/10000000000 : ℝ)] ![(33276513513827/100000000000000 : ℝ), (15431516210351/50000000000000 : ℝ), (4482556756101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145563291/5000000000 : ℝ)|^4431 ≤ (33276513513827/100000000000000 : ℝ)^3407
        have hw : |(2145563291/5000000000 : ℝ)|=(2145563291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2024878027/5000000000 : ℝ)|^4431 ≤ (15431516210351/50000000000000 : ℝ)^3407
        have hw : |(2024878027/5000000000 : ℝ)|=(2024878027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4545102317/10000000000 : ℝ)|^4431 ≤ (4482556756101/12500000000000 : ℝ)^3407
        have hw : |(4545102317/10000000000 : ℝ)|=(4545102317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s4_4 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-242064687/1250000000 : ℝ)*x 0 + (5215492647/10000000000 : ℝ)*x 1 + (5438747629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242064687/1250000000 : ℝ)^4431 ≤ (1182306948651/10000000000000 : ℝ)^3407 := by
    have hnat : (242064687 : ℕ)^4431*10000000000000^3407 ≤ 1182306948651^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242064687 1250000000 1182306948651 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215492647/10000000000 : ℝ)^4431 ≤ (4288706057489/10000000000000 : ℝ)^3407 := by
    have hnat : (5215492647 : ℕ)^4431*10000000000000^3407 ≤ 4288706057489^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215492647 10000000000 4288706057489 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438747629/10000000000 : ℝ)^4431 ≤ (22644934959911/50000000000000 : ℝ)^3407 := by
    have hnat : (5438747629 : ℕ)^4431*50000000000000^3407 ≤ 22644934959911^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438747629 10000000000 22644934959911 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-242064687/1250000000 : ℝ), (5215492647/10000000000 : ℝ), (5438747629/10000000000 : ℝ)] ![(1182306948651/10000000000000 : ℝ), (4288706057489/10000000000000 : ℝ), (22644934959911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-242064687/1250000000 : ℝ)|^4431 ≤ (1182306948651/10000000000000 : ℝ)^3407
        have hw : |(-242064687/1250000000 : ℝ)|=(242064687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215492647/10000000000 : ℝ)|^4431 ≤ (4288706057489/10000000000000 : ℝ)^3407
        have hw : |(5215492647/10000000000 : ℝ)|=(5215492647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438747629/10000000000 : ℝ)|^4431 ≤ (22644934959911/50000000000000 : ℝ)^3407
        have hw : |(5438747629/10000000000 : ℝ)|=(5438747629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s4_5 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661923433/1250000000 : ℝ)*x 0 + (-1827732937/10000000000 : ℝ)*x 1 + (5438747619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661923433/1250000000 : ℝ)^4431 ≤ (2733965990339/6250000000000 : ℝ)^3407 := by
    have hnat : (661923433 : ℕ)^4431*6250000000000^3407 ≤ 2733965990339^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661923433 1250000000 2733965990339 6250000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1827732937/10000000000 : ℝ)^4431 ≤ (10966674326243/100000000000000 : ℝ)^3407 := by
    have hnat : (1827732937 : ℕ)^4431*100000000000000^3407 ≤ 10966674326243^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1827732937 10000000000 10966674326243 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438747619/10000000000 : ℝ)^4431 ≤ (45289869811521/100000000000000 : ℝ)^3407 := by
    have hnat : (5438747619 : ℕ)^4431*100000000000000^3407 ≤ 45289869811521^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438747619 10000000000 45289869811521 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661923433/1250000000 : ℝ), (-1827732937/10000000000 : ℝ), (5438747619/10000000000 : ℝ)] ![(2733965990339/6250000000000 : ℝ), (10966674326243/100000000000000 : ℝ), (45289869811521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661923433/1250000000 : ℝ)|^4431 ≤ (2733965990339/6250000000000 : ℝ)^3407
        have hw : |(661923433/1250000000 : ℝ)|=(661923433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1827732937/10000000000 : ℝ)|^4431 ≤ (10966674326243/100000000000000 : ℝ)^3407
        have hw : |(-1827732937/10000000000 : ℝ)|=(1827732937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438747619/10000000000 : ℝ)|^4431 ≤ (45289869811521/100000000000000 : ℝ)^3407
        have hw : |(5438747619/10000000000 : ℝ)|=(5438747619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s4_6 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059077489/2000000000 : ℝ)*x 0 + (5438747649/10000000000 : ℝ)*x 1 + (-913866461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059077489/2000000000 : ℝ)^4431 ≤ (21871727820649/50000000000000 : ℝ)^3407 := by
    have hnat : (1059077489 : ℕ)^4431*50000000000000^3407 ≤ 21871727820649^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059077489 2000000000 21871727820649 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438747649/10000000000 : ℝ)^4431 ≤ (45289870136423/100000000000000 : ℝ)^3407 := by
    have hnat : (5438747649 : ℕ)^4431*100000000000000^3407 ≤ 45289870136423^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438747649 10000000000 45289870136423 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (913866461/5000000000 : ℝ)^4431 ≤ (1096667420919/10000000000000 : ℝ)^3407 := by
    have hnat : (913866461 : ℕ)^4431*10000000000000^3407 ≤ 1096667420919^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913866461 5000000000 1096667420919 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059077489/2000000000 : ℝ), (5438747649/10000000000 : ℝ), (-913866461/5000000000 : ℝ)] ![(21871727820649/50000000000000 : ℝ), (45289870136423/100000000000000 : ℝ), (1096667420919/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059077489/2000000000 : ℝ)|^4431 ≤ (21871727820649/50000000000000 : ℝ)^3407
        have hw : |(1059077489/2000000000 : ℝ)|=(1059077489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438747649/10000000000 : ℝ)|^4431 ≤ (45289870136423/100000000000000 : ℝ)^3407
        have hw : |(5438747649/10000000000 : ℝ)|=(5438747649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-913866461/5000000000 : ℝ)|^4431 ≤ (1096667420919/10000000000000 : ℝ)^3407
        have hw : |(-913866461/5000000000 : ℝ)|=(913866461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s4_7 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536399483/1250000000 : ℝ)*x 0 + (567819783/1250000000 : ℝ)*x 1 + (2026159463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536399483/1250000000 : ℝ)^4431 ≤ (33277212257/100000000000 : ℝ)^3407 := by
    have hnat : (536399483 : ℕ)^4431*100000000000^3407 ≤ 33277212257^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536399483 1250000000 33277212257 100000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (567819783/1250000000 : ℝ)^4431 ≤ (35834350992909/100000000000000 : ℝ)^3407 := by
    have hnat : (567819783 : ℕ)^4431*100000000000000^3407 ≤ 35834350992909^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567819783 1250000000 35834350992909 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026159463/5000000000 : ℝ)^4431 ≤ (3088843673981/10000000000000 : ℝ)^3407 := by
    have hnat : (2026159463 : ℕ)^4431*10000000000000^3407 ≤ 3088843673981^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026159463 5000000000 3088843673981 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536399483/1250000000 : ℝ), (567819783/1250000000 : ℝ), (2026159463/5000000000 : ℝ)] ![(33277212257/100000000000 : ℝ), (35834350992909/100000000000000 : ℝ), (3088843673981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536399483/1250000000 : ℝ)|^4431 ≤ (33277212257/100000000000 : ℝ)^3407
        have hw : |(536399483/1250000000 : ℝ)|=(536399483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(567819783/1250000000 : ℝ)|^4431 ≤ (35834350992909/100000000000000 : ℝ)^3407
        have hw : |(567819783/1250000000 : ℝ)|=(567819783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2026159463/5000000000 : ℝ)|^4431 ≤ (3088843673981/10000000000000 : ℝ)^3407
        have hw : |(2026159463/5000000000 : ℝ)|=(2026159463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1467_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3117/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/160 : ℝ)*pair X i i ≤ pair X i h) :
    (2143/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3117/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (17/160 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3117/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (17/160 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3117/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (17/160 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3117/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (17/160 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3117/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (17/160 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3117/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (17/160 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (17/160 : ℝ) ^ (4429/1024 : ℝ) ≤ (384204553039191/6250000000000000000 : ℝ) := by
    have hpowers : (17/160 : ℝ)^4429 ≤ (384204553039191/6250000000000000000 : ℝ)^1024 := by
      have hnat : (17 : ℕ)^4429*6250000000000000000^1024 ≤ 384204553039191^1024*160^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17 160 384204553039191 6250000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17/160 : ℝ)) (X := (384204553039191/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3117/20000 : ℝ) ^ (4429/1024 : ℝ) ≤ (1007277854386933/3125000000000000000 : ℝ) := by
    have hpowers : (3117/20000 : ℝ)^4429 ≤ (1007277854386933/3125000000000000000 : ℝ)^1024 := by
      have hnat : (3117 : ℕ)^4429*3125000000000000000^1024 ≤ 1007277854386933^1024*20000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3117 20000 1007277854386933 3125000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3117/20000 : ℝ)) (X := (1007277854386933/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125384204553039191/3125000000000000000 : ℝ) ≤ (2500071060170759/2500000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (3125384204553039191/3125000000000000000 : ℝ)^1024 ≤ (2500071060170759/2500000000000000 : ℝ)^4429 := by
      have hnat : (3125384204553039191 : ℕ)^1024*2500000000000000^4429 ≤ 2500071060170759^4429*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125384204553039191 3125000000000000000 2500071060170759 2500000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500071060170759/2500000000000000 : ℝ)) (X := (3125384204553039191/3125000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252398760261813057/6250000000000000000 : ℝ) ≤ (5000443615841233/5000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (6252398760261813057/6250000000000000000 : ℝ)^1024 ≤ (5000443615841233/5000000000000000 : ℝ)^4429 := by
      have hnat : (6252398760261813057 : ℕ)^1024*5000000000000000^4429 ≤ 5000443615841233^4429*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252398760261813057 6250000000000000000 5000443615841233 5000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000443615841233/5000000000000000 : ℝ)) (X := (6252398760261813057/6250000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563507277854386933/1562500000000000000 : ℝ) ≤ (1250186277835237/1250000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (1563507277854386933/1562500000000000000 : ℝ)^1024 ≤ (1250186277835237/1250000000000000 : ℝ)^4429 := by
      have hnat : (1563507277854386933 : ℕ)^1024*1250000000000000^4429 ≤ 1250186277835237^4429*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563507277854386933 1562500000000000000 1250186277835237 1250000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250186277835237/1250000000000000 : ℝ)) (X := (1563507277854386933/1562500000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(384204553039191/6250000000000000000 : ℝ) ≤ ((2479429813752498553/2480000000000000000 : ℝ)+2*(60299099943/49600000000000 : ℝ)*(17/160 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (2479429813752498553/2480000000000000000 : ℝ)+2*(60299099943/49600000000000 : ℝ)*(17/160 : ℝ)=(2500071060170759/2500000000000000 : ℝ) by norm_num, show 1+2*(384204553039191/6250000000000000000 : ℝ)=(3125384204553039191/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1007277854386933/3125000000000000000 : ℝ)+(384204553039191/6250000000000000000 : ℝ) ≤ ((2479429813752498553/2480000000000000000 : ℝ)+(60299099943/49600000000000 : ℝ)*((3117/20000 : ℝ)+(17/160 : ℝ)))^(4429/1024 : ℝ) := by
    rw [show (2479429813752498553/2480000000000000000 : ℝ)+(60299099943/49600000000000 : ℝ)*((3117/20000 : ℝ)+(17/160 : ℝ))=(5000443615841233/5000000000000000 : ℝ) by norm_num, show 1+(1007277854386933/3125000000000000000 : ℝ)+(384204553039191/6250000000000000000 : ℝ)=(6252398760261813057/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1007277854386933/3125000000000000000 : ℝ) ≤ ((2479429813752498553/2480000000000000000 : ℝ)+2*(60299099943/49600000000000 : ℝ)*(3117/20000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (2479429813752498553/2480000000000000000 : ℝ)+2*(60299099943/49600000000000 : ℝ)*(3117/20000 : ℝ)=(1250186277835237/1250000000000000 : ℝ) by norm_num, show 1+2*(1007277854386933/3125000000000000000 : ℝ)=(1563507277854386933/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2479429813752498553/2480000000000000000 : ℝ)*(X 1 0+X 2 0)+(60299099943/49600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (17/160 : ℝ)) (hi := (3117/20000 : ℝ)) (c := (2479429813752498553/2480000000000000000 : ℝ)) (alpha := (60299099943/49600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2479429813752498553/2480000000000000000 : ℝ)*(X 0 1+X 2 1)+(60299099943/49600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (17/160 : ℝ)) (hi := (3117/20000 : ℝ)) (c := (2479429813752498553/2480000000000000000 : ℝ)) (alpha := (60299099943/49600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2479429813752498553/2480000000000000000 : ℝ)*(X 0 2+X 1 2)+(60299099943/49600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (17/160 : ℝ)) (hi := (3117/20000 : ℝ)) (c := (2479429813752498553/2480000000000000000 : ℝ)) (alpha := (60299099943/49600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-484121491/2500000000 : ℝ)*X 0 0+(5439914743/10000000000 : ℝ)*X 0 1+(651791759/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677083387/5000000000 : ℝ)*X 1 0+(-513036633/2500000000 : ℝ)*X 1 1+(1303583517/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677083389/5000000000 : ℝ)*X 2 0+(521433407/1000000000 : ℝ)*X 2 1+(-1026073261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2145563291/5000000000 : ℝ)*X 0 0+(2024878027/5000000000 : ℝ)*X 0 1+(4545102317/10000000000 : ℝ)*X 0 2+(2145563291/5000000000 : ℝ)*X 1 0+(2024878027/5000000000 : ℝ)*X 1 1+(4545102317/10000000000 : ℝ)*X 1 2+(2145563291/5000000000 : ℝ)*X 2 0+(2024878027/5000000000 : ℝ)*X 2 1+(4545102317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-242064687/1250000000 : ℝ)*X 0 0+(5215492647/10000000000 : ℝ)*X 0 1+(5438747629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661923433/1250000000 : ℝ)*X 1 0+(-1827732937/10000000000 : ℝ)*X 1 1+(5438747619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059077489/2000000000 : ℝ)*X 2 0+(5438747649/10000000000 : ℝ)*X 2 1+(-913866461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((536399483/1250000000 : ℝ)*X 0 0+(567819783/1250000000 : ℝ)*X 0 1+(2026159463/5000000000 : ℝ)*X 0 2+(536399483/1250000000 : ℝ)*X 1 0+(567819783/1250000000 : ℝ)*X 1 1+(2026159463/5000000000 : ℝ)*X 1 2+(536399483/1250000000 : ℝ)*X 2 0+(567819783/1250000000 : ℝ)*X 2 1+(2026159463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20273346461052622679662377/4000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (466405067/50000000000000 : ℝ)*(base19) + (215123/24414062500 : ℝ)*(base23) + (1177449/4000000000000 : ℝ)*(lower2) + (129220627/100000000000000 : ℝ)*(upper3) + (9737649/10000000000000 : ℝ)*(upper5) + (3225917854053769/100000000000000 : ℝ)*(major0) + (3225917854053769/100000000000000 : ℝ)*(major1) + (3225917854053769/100000000000000 : ℝ)*(major2) + (221650909519841/5000000000000 : ℝ)*(sp0) + (443303131279493/10000000000000 : ℝ)*(sp1) + (554128920557657/12500000000000 : ℝ)*(sp2) + (2018796268352983/100000000000000 : ℝ)*(sp3) + (2811041649/20000000000000 : ℝ)*(sp4) + (7025204929/100000000000000 : ℝ)*(sp7) + (2018803293557913/100000000000000 : ℝ)*(f.failure) + (554129030700633/12500000000000 : ℝ)*(f.sum) + (487398590497/80000000000000000000000000 : ℝ)*base65 + (16479496938420847/8000000000000000000000000000000 : ℝ)*base67 + (69515369762420847/8000000000000000000000000000000 : ℝ)*base69 + (55192461186420847/8000000000000000000000000000000 : ℝ)*base71 + (97216674783/80000000000000000000000000 : ℝ)*base74 + (81713585002420847/8000000000000000000000000000000 : ℝ)*base75 + (43498882402420847/8000000000000000000000000000000 : ℝ)*base77 + (29549895778420847/8000000000000000000000000000000 : ℝ)*base79 + (422048392817/80000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2001941/1000000000000000000000 : ℝ)*base89 + (2001941/1000000000000000000000 : ℝ)*base91 + (2001941/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9171429593362058804398557/968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1620441223/100000000000000 : ℝ)*(base19) + (1758671823/100000000000000 : ℝ)*(base23) + (204870091/100000000000000 : ℝ)*(upper3) + (66316649/100000000000000 : ℝ)*(lower4) + (185790183/100000000000000 : ℝ)*(upper5) + (50929701992623/1562500000000 : ℝ)*(major0) + (50929701992623/1562500000000 : ℝ)*(major1) + (50929701992623/1562500000000 : ℝ)*(major2) + (2360708001/10000000000000 : ℝ)*(sp1) + (6556430217/25000000000000 : ℝ)*(sp2) + (2239590854864073/50000000000000 : ℝ)*(sp4) + (2239578241103457/50000000000000 : ℝ)*(sp5) + (139973553916733/3125000000000 : ℝ)*(sp6) + (1019909914875759/50000000000000 : ℝ)*(sp7) + (1019909914875759/50000000000000 : ℝ)*(f.failure) + (2239590854864073/50000000000000 : ℝ)*(f.sum) + (196670596031/38750000000000000000000000 : ℝ)*base66 + (32042857905625481/3875000000000000000000000000000 : ℝ)*base68 + (23168884978374519/3875000000000000000000000000000 : ℝ)*base69 + (40470007079875481/3875000000000000000000000000000 : ℝ)*base72 + (142691767607/77500000000000000000000000 : ℝ)*base74 + (20368881393125481/3875000000000000000000000000000 : ℝ)*base76 + (3701524708375481/3875000000000000000000000000000 : ℝ)*base78 + (38036604218375481/3875000000000000000000000000000 : ℝ)*base80 + (45078041859/9687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3706963/500000000000000000000 : ℝ)*base89 + (3706963/500000000000000000000 : ℝ)*base91 + (3706963/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1467_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3117/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (17/160 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2143/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1467_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1467_s5_0 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1936592979/10000000000 : ℝ)*x 0 + (5439245159/10000000000 : ℝ)*x 1 + (20859731/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936592979/10000000000 : ℝ)^4431 ≤ (11823668849787/100000000000000 : ℝ)^3407 := by
    have hnat : (1936592979 : ℕ)^4431*100000000000000^3407 ≤ 11823668849787^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936592979 10000000000 11823668849787 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439245159/10000000000 : ℝ)^4431 ≤ (22647629142531/50000000000000 : ℝ)^3407 := by
    have hnat : (5439245159 : ℕ)^4431*50000000000000^3407 ≤ 22647629142531^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439245159 10000000000 22647629142531 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20859731/40000000 : ℝ)^4431 ≤ (21440536425993/50000000000000 : ℝ)^3407 := by
    have hnat : (20859731 : ℕ)^4431*50000000000000^3407 ≤ 21440536425993^3407*40000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20859731 40000000 21440536425993 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1936592979/10000000000 : ℝ), (5439245159/10000000000 : ℝ), (20859731/40000000 : ℝ)] ![(11823668849787/100000000000000 : ℝ), (22647629142531/50000000000000 : ℝ), (21440536425993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1936592979/10000000000 : ℝ)|^4431 ≤ (11823668849787/100000000000000 : ℝ)^3407
        have hw : |(-1936592979/10000000000 : ℝ)|=(1936592979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439245159/10000000000 : ℝ)|^4431 ≤ (22647629142531/50000000000000 : ℝ)^3407
        have hw : |(5439245159/10000000000 : ℝ)|=(5439245159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20859731/40000000 : ℝ)|^4431 ≤ (21440536425993/50000000000000 : ℝ)^3407
        have hw : |(20859731/40000000 : ℝ)|=(20859731/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s5_1 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353984603/10000000000 : ℝ)*x 0 + (-205158953/1000000000 : ℝ)*x 1 + (5214938521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353984603/10000000000 : ℝ)^4431 ≤ (887480744151/2000000000000 : ℝ)^3407 := by
    have hnat : (5353984603 : ℕ)^4431*2000000000000^3407 ≤ 887480744151^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353984603 10000000000 887480744151 2000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205158953/1000000000 : ℝ)^4431 ≤ (12744828214163/100000000000000 : ℝ)^3407 := by
    have hnat : (205158953 : ℕ)^4431*100000000000000^3407 ≤ 12744828214163^3407*1000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205158953 1000000000 12744828214163 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214938521/10000000000 : ℝ)^4431 ≤ (1715245382719/4000000000000 : ℝ)^3407 := by
    have hnat : (5214938521 : ℕ)^4431*4000000000000^3407 ≤ 1715245382719^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214938521 10000000000 1715245382719 4000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353984603/10000000000 : ℝ), (-205158953/1000000000 : ℝ), (5214938521/10000000000 : ℝ)] ![(887480744151/2000000000000 : ℝ), (12744828214163/100000000000000 : ℝ), (1715245382719/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353984603/10000000000 : ℝ)|^4431 ≤ (887480744151/2000000000000 : ℝ)^3407
        have hw : |(5353984603/10000000000 : ℝ)|=(5353984603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205158953/1000000000 : ℝ)|^4431 ≤ (12744828214163/100000000000000 : ℝ)^3407
        have hw : |(-205158953/1000000000 : ℝ)|=(205158953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214938521/10000000000 : ℝ)|^4431 ≤ (1715245382719/4000000000000 : ℝ)^3407
        have hw : |(5214938521/10000000000 : ℝ)|=(5214938521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s5_2 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353990693/10000000000 : ℝ)*x 0 + (5214938067/10000000000 : ℝ)*x 1 + (-1025791003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353990693/10000000000 : ℝ)^4431 ≤ (1109352571303/2500000000000 : ℝ)^3407 := by
    have hnat : (5353990693 : ℕ)^4431*2500000000000^3407 ≤ 1109352571303^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353990693 10000000000 1109352571303 2500000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214938067/10000000000 : ℝ)^4431 ≤ (42881129712827/100000000000000 : ℝ)^3407 := by
    have hnat : (5214938067 : ℕ)^4431*100000000000000^3407 ≤ 42881129712827^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214938067 10000000000 42881129712827 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025791003/5000000000 : ℝ)^4431 ≤ (12744767425629/100000000000000 : ℝ)^3407 := by
    have hnat : (1025791003 : ℕ)^4431*100000000000000^3407 ≤ 12744767425629^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025791003 5000000000 12744767425629 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353990693/10000000000 : ℝ), (5214938067/10000000000 : ℝ), (-1025791003/5000000000 : ℝ)] ![(1109352571303/2500000000000 : ℝ), (42881129712827/100000000000000 : ℝ), (12744767425629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353990693/10000000000 : ℝ)|^4431 ≤ (1109352571303/2500000000000 : ℝ)^3407
        have hw : |(5353990693/10000000000 : ℝ)|=(5353990693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214938067/10000000000 : ℝ)|^4431 ≤ (42881129712827/100000000000000 : ℝ)^3407
        have hw : |(5214938067/10000000000 : ℝ)|=(5214938067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025791003/5000000000 : ℝ)|^4431 ≤ (12744767425629/100000000000000 : ℝ)^3407
        have hw : |(-1025791003/5000000000 : ℝ)|=(1025791003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s5_3 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291195981/10000000000 : ℝ)*x 0 + (2025570281/5000000000 : ℝ)*x 1 + (227184833/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291195981/10000000000 : ℝ)^4431 ≤ (16638606718503/50000000000000 : ℝ)^3407 := by
    have hnat : (4291195981 : ℕ)^4431*50000000000000^3407 ≤ 16638606718503^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291195981 10000000000 16638606718503 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025570281/5000000000 : ℝ)^4431 ≤ (7719188918883/25000000000000 : ℝ)^3407 := by
    have hnat : (2025570281 : ℕ)^4431*25000000000000^3407 ≤ 7719188918883^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025570281 5000000000 7719188918883 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227184833/500000000 : ℝ)^4431 ≤ (35846030872593/100000000000000 : ℝ)^3407 := by
    have hnat : (227184833 : ℕ)^4431*100000000000000^3407 ≤ 35846030872593^3407*500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227184833 500000000 35846030872593 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291195981/10000000000 : ℝ), (2025570281/5000000000 : ℝ), (227184833/500000000 : ℝ)] ![(16638606718503/50000000000000 : ℝ), (7719188918883/25000000000000 : ℝ), (35846030872593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291195981/10000000000 : ℝ)|^4431 ≤ (16638606718503/50000000000000 : ℝ)^3407
        have hw : |(4291195981/10000000000 : ℝ)|=(4291195981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2025570281/5000000000 : ℝ)|^4431 ≤ (7719188918883/25000000000000 : ℝ)^3407
        have hw : |(2025570281/5000000000 : ℝ)|=(2025570281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227184833/500000000 : ℝ)|^4431 ≤ (35846030872593/100000000000000 : ℝ)^3407
        have hw : |(227184833/500000000 : ℝ)|=(227184833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s5_4 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-484154699/2500000000 : ℝ)*x 0 + (32600503/62500000 : ℝ)*x 1 + (2719046431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (484154699/2500000000 : ℝ)^4431 ≤ (11823873848043/100000000000000 : ℝ)^3407 := by
    have hnat : (484154699 : ℕ)^4431*100000000000000^3407 ≤ 11823873848043^3407*2500000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484154699 2500000000 11823873848043 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32600503/62500000 : ℝ)^4431 ≤ (42893347262479/100000000000000 : ℝ)^3407 := by
    have hnat : (32600503 : ℕ)^4431*100000000000000^3407 ≤ 42893347262479^3407*62500000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32600503 62500000 42893347262479 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719046431/5000000000 : ℝ)^4431 ≤ (45282778867199/100000000000000 : ℝ)^3407 := by
    have hnat : (2719046431 : ℕ)^4431*100000000000000^3407 ≤ 45282778867199^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719046431 5000000000 45282778867199 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-484154699/2500000000 : ℝ), (32600503/62500000 : ℝ), (2719046431/5000000000 : ℝ)] ![(11823873848043/100000000000000 : ℝ), (42893347262479/100000000000000 : ℝ), (45282778867199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-484154699/2500000000 : ℝ)|^4431 ≤ (11823873848043/100000000000000 : ℝ)^3407
        have hw : |(-484154699/2500000000 : ℝ)|=(484154699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32600503/62500000 : ℝ)|^4431 ≤ (42893347262479/100000000000000 : ℝ)^3407
        have hw : |(32600503/62500000 : ℝ)|=(32600503/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719046431/5000000000 : ℝ)|^4431 ≤ (45282778867199/100000000000000 : ℝ)^3407
        have hw : |(2719046431/5000000000 : ℝ)|=(2719046431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s5_5 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647772801/5000000000 : ℝ)*x 0 + (-1828423873/10000000000 : ℝ)*x 1 + (679761607/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647772801/5000000000 : ℝ)^4431 ≤ (43745154805427/100000000000000 : ℝ)^3407 := by
    have hnat : (2647772801 : ℕ)^4431*100000000000000^3407 ≤ 43745154805427^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647772801 5000000000 43745154805427 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1828423873/10000000000 : ℝ)^4431 ≤ (10972066381269/100000000000000 : ℝ)^3407 := by
    have hnat : (1828423873 : ℕ)^4431*100000000000000^3407 ≤ 10972066381269^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828423873 10000000000 10972066381269 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679761607/1250000000 : ℝ)^4431 ≤ (45282778802221/100000000000000 : ℝ)^3407 := by
    have hnat : (679761607 : ℕ)^4431*100000000000000^3407 ≤ 45282778802221^3407*1250000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679761607 1250000000 45282778802221 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647772801/5000000000 : ℝ), (-1828423873/10000000000 : ℝ), (679761607/1250000000 : ℝ)] ![(43745154805427/100000000000000 : ℝ), (10972066381269/100000000000000 : ℝ), (45282778802221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647772801/5000000000 : ℝ)|^4431 ≤ (43745154805427/100000000000000 : ℝ)^3407
        have hw : |(2647772801/5000000000 : ℝ)|=(2647772801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1828423873/10000000000 : ℝ)|^4431 ≤ (10972066381269/100000000000000 : ℝ)^3407
        have hw : |(-1828423873/10000000000 : ℝ)|=(1828423873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679761607/1250000000 : ℝ)|^4431 ≤ (45282778802221/100000000000000 : ℝ)^3407
        have hw : |(679761607/1250000000 : ℝ)|=(679761607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s5_6 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647772819/5000000000 : ℝ)*x 0 + (5438092843/10000000000 : ℝ)*x 1 + (-11427649/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647772819/5000000000 : ℝ)^4431 ≤ (10936288798049/25000000000000 : ℝ)^3407 := by
    have hnat : (2647772819 : ℕ)^4431*25000000000000^3407 ≤ 10936288798049^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647772819 5000000000 10936288798049 25000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438092843/10000000000 : ℝ)^4431 ≤ (9056555732287/20000000000000 : ℝ)^3407 := by
    have hnat : (5438092843 : ℕ)^4431*20000000000000^3407 ≤ 9056555732287^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438092843 10000000000 9056555732287 20000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11427649/62500000 : ℝ)^4431 ≤ (10972066123723/100000000000000 : ℝ)^3407 := by
    have hnat : (11427649 : ℕ)^4431*100000000000000^3407 ≤ 10972066123723^3407*62500000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11427649 62500000 10972066123723 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647772819/5000000000 : ℝ), (5438092843/10000000000 : ℝ), (-11427649/62500000 : ℝ)] ![(10936288798049/25000000000000 : ℝ), (9056555732287/20000000000000 : ℝ), (10972066123723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647772819/5000000000 : ℝ)|^4431 ≤ (10936288798049/25000000000000 : ℝ)^3407
        have hw : |(2647772819/5000000000 : ℝ)|=(2647772819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438092843/10000000000 : ℝ)|^4431 ≤ (9056555732287/20000000000000 : ℝ)^3407
        have hw : |(5438092843/10000000000 : ℝ)|=(5438092843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11427649/62500000 : ℝ)|^4431 ≤ (10972066123723/100000000000000 : ℝ)^3407
        have hw : |(-11427649/62500000 : ℝ)|=(11427649/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s5_7 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291257867/10000000000 : ℝ)*x 0 + (908237251/2000000000 : ℝ)*x 1 + (4053675633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291257867/10000000000 : ℝ)^4431 ≤ (33277837590741/100000000000000 : ℝ)^3407 := by
    have hnat : (4291257867 : ℕ)^4431*100000000000000^3407 ≤ 33277837590741^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291257867 10000000000 33277837590741 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908237251/2000000000 : ℝ)^4431 ≤ (35820275425877/100000000000000 : ℝ)^3407 := by
    have hnat : (908237251 : ℕ)^4431*100000000000000^3407 ≤ 35820275425877^3407*2000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908237251 2000000000 35820275425877 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4053675633/10000000000 : ℝ)^4431 ≤ (3090188697387/10000000000000 : ℝ)^3407 := by
    have hnat : (4053675633 : ℕ)^4431*10000000000000^3407 ≤ 3090188697387^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053675633 10000000000 3090188697387 10000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291257867/10000000000 : ℝ), (908237251/2000000000 : ℝ), (4053675633/10000000000 : ℝ)] ![(33277837590741/100000000000000 : ℝ), (35820275425877/100000000000000 : ℝ), (3090188697387/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291257867/10000000000 : ℝ)|^4431 ≤ (33277837590741/100000000000000 : ℝ)^3407
        have hw : |(4291257867/10000000000 : ℝ)|=(4291257867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(908237251/2000000000 : ℝ)|^4431 ≤ (35820275425877/100000000000000 : ℝ)^3407
        have hw : |(908237251/2000000000 : ℝ)|=(908237251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4053675633/10000000000 : ℝ)|^4431 ≤ (3090188697387/10000000000000 : ℝ)^3407
        have hw : |(4053675633/10000000000 : ℝ)|=(4053675633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1467_s5_8 (p : ℝ) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8352460977/10000000000 : ℝ)*x 0 + (-592296273/10000000000 : ℝ)*x 1 + (1357158703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8352460977/10000000000 : ℝ)^4431 ≤ (39562633608909/50000000000000 : ℝ)^3407 := by
    have hnat : (8352460977 : ℕ)^4431*50000000000000^3407 ≤ 39562633608909^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8352460977 10000000000 39562633608909 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (592296273/10000000000 : ℝ)^4431 ≤ (1266444549993/50000000000000 : ℝ)^3407 := by
    have hnat : (592296273 : ℕ)^4431*50000000000000^3407 ≤ 1266444549993^3407*10000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592296273 10000000000 1266444549993 50000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357158703/5000000000 : ℝ)^4431 ≤ (18341843674093/100000000000000 : ℝ)^3407 := by
    have hnat : (1357158703 : ℕ)^4431*100000000000000^3407 ≤ 18341843674093^3407*5000000000^4431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357158703 5000000000 18341843674093 100000000000000 4431 3407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4431/1024 : ℝ)) 4431 3407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8352460977/10000000000 : ℝ), (-592296273/10000000000 : ℝ), (1357158703/5000000000 : ℝ)] ![(39562633608909/50000000000000 : ℝ), (1266444549993/50000000000000 : ℝ), (18341843674093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8352460977/10000000000 : ℝ)|^4431 ≤ (39562633608909/50000000000000 : ℝ)^3407
        have hw : |(8352460977/10000000000 : ℝ)|=(8352460977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-592296273/10000000000 : ℝ)|^4431 ≤ (1266444549993/50000000000000 : ℝ)^3407
        have hw : |(-592296273/10000000000 : ℝ)|=(592296273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357158703/5000000000 : ℝ)|^4431 ≤ (18341843674093/100000000000000 : ℝ)^3407
        have hw : |(1357158703/5000000000 : ℝ)|=(1357158703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1467_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2143/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1341/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7737/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2143/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2143/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2143/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2143/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2143/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2143/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2143/20000 : ℝ) ^ (4429/1024 : ℝ) ≤ (255027313025953/4000000000000000000 : ℝ) := by
    have hpowers : (2143/20000 : ℝ)^4429 ≤ (255027313025953/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2143 : ℕ)^4429*4000000000000000000^1024 ≤ 255027313025953^1024*20000^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2143 20000 255027313025953 4000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2143/20000 : ℝ)) (X := (255027313025953/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4429/1024 : ℝ) ≤ (7843531589329827/25000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4429 ≤ (7843531589329827/25000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4429*25000000000000000000^1024 ≤ 7843531589329827^1024*3125^4429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 7843531589329827 25000000000000000000 4429 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (7843531589329827/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000255027313025953/2000000000000000000 : ℝ) ≤ (10000294801500411/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (2000255027313025953/2000000000000000000 : ℝ)^1024 ≤ (10000294801500411/10000000000000000 : ℝ)^4429 := by
      have hnat : (2000255027313025953 : ℕ)^1024*10000000000000000^4429 ≤ 10000294801500411^4429*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000255027313025953 2000000000000000000 10000294801500411 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000294801500411/10000000000000000 : ℝ)) (X := (2000255027313025953/2000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037749809182968133/100000000000000000000 : ℝ) ≤ (5000436330960967/5000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (100037749809182968133/100000000000000000000 : ℝ)^1024 ≤ (5000436330960967/5000000000000000 : ℝ)^4429 := by
      have hnat : (100037749809182968133 : ℕ)^1024*5000000000000000^4429 ≤ 5000436330960967^4429*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037749809182968133 100000000000000000000 5000436330960967 5000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000436330960967/5000000000000000 : ℝ)) (X := (100037749809182968133/100000000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507843531589329827/12500000000000000000 : ℝ) ≤ (10001450522343457/10000000000000000 : ℝ) ^ (4429/1024 : ℝ) := by
    have hpowers : (12507843531589329827/12500000000000000000 : ℝ)^1024 ≤ (10001450522343457/10000000000000000 : ℝ)^4429 := by
      have hnat : (12507843531589329827 : ℕ)^1024*10000000000000000^4429 ≤ 10001450522343457^4429*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507843531589329827 12500000000000000000 10001450522343457 10000000000000000 1024 4429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001450522343457/10000000000000000 : ℝ)) (X := (12507843531589329827/12500000000000000000 : ℝ)) (by norm_num) 4429 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(255027313025953/4000000000000000000 : ℝ) ≤ ((47719023538728223813/47730000000000000000 : ℝ)+2*(577860421523/477300000000000 : ℝ)*(2143/20000 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (47719023538728223813/47730000000000000000 : ℝ)+2*(577860421523/477300000000000 : ℝ)*(2143/20000 : ℝ)=(10000294801500411/10000000000000000 : ℝ) by norm_num, show 1+2*(255027313025953/4000000000000000000 : ℝ)=(2000255027313025953/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7843531589329827/25000000000000000000 : ℝ)+(255027313025953/4000000000000000000 : ℝ) ≤ ((47719023538728223813/47730000000000000000 : ℝ)+(577860421523/477300000000000 : ℝ)*((484/3125 : ℝ)+(2143/20000 : ℝ)))^(4429/1024 : ℝ) := by
    rw [show (47719023538728223813/47730000000000000000 : ℝ)+(577860421523/477300000000000 : ℝ)*((484/3125 : ℝ)+(2143/20000 : ℝ))=(5000436330960967/5000000000000000 : ℝ) by norm_num, show 1+(7843531589329827/25000000000000000000 : ℝ)+(255027313025953/4000000000000000000 : ℝ)=(100037749809182968133/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7843531589329827/25000000000000000000 : ℝ) ≤ ((47719023538728223813/47730000000000000000 : ℝ)+2*(577860421523/477300000000000 : ℝ)*(484/3125 : ℝ))^(4429/1024 : ℝ) := by
    rw [show (47719023538728223813/47730000000000000000 : ℝ)+2*(577860421523/477300000000000 : ℝ)*(484/3125 : ℝ)=(10001450522343457/10000000000000000 : ℝ) by norm_num, show 1+2*(7843531589329827/25000000000000000000 : ℝ)=(12507843531589329827/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47719023538728223813/47730000000000000000 : ℝ)*(X 1 0+X 2 0)+(577860421523/477300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (2143/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47719023538728223813/47730000000000000000 : ℝ)) (alpha := (577860421523/477300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47719023538728223813/47730000000000000000 : ℝ)*(X 0 1+X 2 1)+(577860421523/477300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (2143/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47719023538728223813/47730000000000000000 : ℝ)) (alpha := (577860421523/477300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47719023538728223813/47730000000000000000 : ℝ)*(X 0 2+X 1 2)+(577860421523/477300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4429/1024 : ℝ)) (lo := (2143/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (47719023538728223813/47730000000000000000 : ℝ)) (alpha := (577860421523/477300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1936592979/10000000000 : ℝ)*X 0 0+(5439245159/10000000000 : ℝ)*X 0 1+(20859731/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353984603/10000000000 : ℝ)*X 1 0+(-205158953/1000000000 : ℝ)*X 1 1+(5214938521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353990693/10000000000 : ℝ)*X 2 0+(5214938067/10000000000 : ℝ)*X 2 1+(-1025791003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4291195981/10000000000 : ℝ)*X 0 0+(2025570281/5000000000 : ℝ)*X 0 1+(227184833/500000000 : ℝ)*X 0 2+(4291195981/10000000000 : ℝ)*X 1 0+(2025570281/5000000000 : ℝ)*X 1 1+(227184833/500000000 : ℝ)*X 1 2+(4291195981/10000000000 : ℝ)*X 2 0+(2025570281/5000000000 : ℝ)*X 2 1+(227184833/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-484154699/2500000000 : ℝ)*X 0 0+(32600503/62500000 : ℝ)*X 0 1+(2719046431/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647772801/5000000000 : ℝ)*X 1 0+(-1828423873/10000000000 : ℝ)*X 1 1+(679761607/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647772819/5000000000 : ℝ)*X 2 0+(5438092843/10000000000 : ℝ)*X 2 1+(-11427649/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4291257867/10000000000 : ℝ)*X 0 0+(908237251/2000000000 : ℝ)*X 0 1+(4053675633/10000000000 : ℝ)*X 0 2+(4291257867/10000000000 : ℝ)*X 1 0+(908237251/2000000000 : ℝ)*X 1 1+(4053675633/10000000000 : ℝ)*X 1 2+(4291257867/10000000000 : ℝ)*X 2 0+(908237251/2000000000 : ℝ)*X 2 1+(4053675633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((8352460977/10000000000 : ℝ)*X 1 0+(-592296273/10000000000 : ℝ)*X 1 1+(1357158703/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1467_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1114559356952524449969267847/795500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139031491/50000000000000 : ℝ)*(lower2) + (559504247/50000000000000 : ℝ)*(upper3) + (1309124191/100000000000000 : ℝ)*(upper4) + (1331176077/50000000000000 : ℝ)*(upper5) + (3244176382264727/100000000000000 : ℝ)*(major0) + (3244176382264727/100000000000000 : ℝ)*(major1) + (3244176382264727/100000000000000 : ℝ)*(major2) + (2229027378232839/50000000000000 : ℝ)*(sp0) + (4458060189753847/100000000000000 : ℝ)*(sp1) + (2229061551019447/50000000000000 : ℝ)*(sp2) + (2030229615787873/100000000000000 : ℝ)*(sp3) + (2135799163/3125000000000 : ℝ)*(sp4) + (1813131873/3125000000000 : ℝ)*(sp5) + (4892065111/100000000000000 : ℝ)*(sp8) + (2030229615787873/100000000000000 : ℝ)*(f.failure) + (2229061551019447/50000000000000 : ℝ)*(f.sum) + (4405547359627/11932500000000000000000000000 : ℝ)*base66 + (14586900971503148017/1591000000000000000000000000000000 : ℝ)*base67 + (6058565404979148017/1591000000000000000000000000000000 : ℝ)*base69 + (16672749757188148017/1591000000000000000000000000000000 : ℝ)*base71 + (6335771785337/2983125000000000000000000000 : ℝ)*base73 + (18579574909672148017/1591000000000000000000000000000000 : ℝ)*base75 + (21646532553926148017/1591000000000000000000000000000000 : ℝ)*base77 + (7848059118647148017/1591000000000000000000000000000000 : ℝ)*base79 + (22628144584619/23865000000000000000000000000 : ℝ)*base82 + (11062339/1000000000000000000000 : ℝ)*base90 + (11062339/1000000000000000000000 : ℝ)*base92 + (11062339/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (862675232539974513337/99437500000000000000000000 : ℝ) := by norm_num
    linear_combination (1436740997/100000000000000 : ℝ)*(base19) + (1631675331/100000000000000 : ℝ)*(base23) + (176390663/100000000000000 : ℝ)*(upper3) + (35485351/50000000000000 : ℝ)*(lower4) + (36125461/20000000000000 : ℝ)*(upper5) + (163887245682023/5000000000000 : ℝ)*(major0) + (163887245682023/5000000000000 : ℝ)*(major1) + (163887245682023/5000000000000 : ℝ)*(major2) + (10672763467/50000000000000 : ℝ)*(sp1) + (24088177883/100000000000000 : ℝ)*(sp2) + (2252126243333629/50000000000000 : ℝ)*(sp4) + (4504229704399327/100000000000000 : ℝ)*(sp5) + (1126056691703511/25000000000000 : ℝ)*(sp6) + (2051237051428577/100000000000000 : ℝ)*(sp7) + (2051237051428577/100000000000000 : ℝ)*(f.failure) + (2252126243333629/50000000000000 : ℝ)*(f.sum) + (21994831512373/4773000000000000000000000000 : ℝ)*base65 + (276621319397921233/79550000000000000000000000000000 : ℝ)*base67 + (176140978914178767/79550000000000000000000000000000 : ℝ)*base70 + (1032096584900921233/79550000000000000000000000000000 : ℝ)*base71 + (369851771981/298312500000000000000000000 : ℝ)*base74 + (589054810255678767/79550000000000000000000000000000 : ℝ)*base76 + (469886829271671233/79550000000000000000000000000000 : ℝ)*base77 + (89589922706228767/79550000000000000000000000000000 : ℝ)*base80 + (6829783680743/4773000000000000000000000000 : ℝ)*base82 + (8115011/1000000000000000000000 : ℝ)*base90 + (8115011/1000000000000000000000 : ℝ)*base92 + (8115011/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1467_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2143/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1467_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1467_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1467_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1467_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1467_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4429/1024 : ℝ) ≤ p) (hpb : p ≤ (4431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15979357/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1341/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1467_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

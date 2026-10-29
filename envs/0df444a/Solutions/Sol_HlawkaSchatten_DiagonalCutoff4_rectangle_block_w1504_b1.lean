-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1504_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:39.083222+00:00
-- url     : https://prove2.me/submissions/ce3d47bb-938c-405a-a976-4b46047ad610

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
theorem support_rectangle_w1504_s3_0 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-939677/5000000 : ℝ)*x 0 + (2718930329/5000000000 : ℝ)*x 1 + (2606999291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939677/5000000 : ℝ)^4505 ≤ (11493304256651/100000000000000 : ℝ)^3481 := by
    have hnat : (939677 : ℕ)^4505*100000000000000^3481 ≤ 11493304256651^3481*5000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939677 5000000 11493304256651 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718930329/5000000000 : ℝ)^4505 ≤ (45456855529373/100000000000000 : ℝ)^3481 := by
    have hnat : (2718930329 : ℕ)^4505*100000000000000^3481 ≤ 45456855529373^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718930329 5000000000 45456855529373 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606999291/5000000000 : ℝ)^4505 ≤ (21524920102347/50000000000000 : ℝ)^3481 := by
    have hnat : (2606999291 : ℕ)^4505*50000000000000^3481 ≤ 21524920102347^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606999291 5000000000 21524920102347 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-939677/5000000 : ℝ), (2718930329/5000000000 : ℝ), (2606999291/5000000000 : ℝ)] ![(11493304256651/100000000000000 : ℝ), (45456855529373/100000000000000 : ℝ), (21524920102347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-939677/5000000 : ℝ)|^4505 ≤ (11493304256651/100000000000000 : ℝ)^3481
        have hw : |(-939677/5000000 : ℝ)|=(939677/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718930329/5000000000 : ℝ)|^4505 ≤ (45456855529373/100000000000000 : ℝ)^3481
        have hw : |(2718930329/5000000000 : ℝ)|=(2718930329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606999291/5000000000 : ℝ)|^4505 ≤ (21524920102347/50000000000000 : ℝ)^3481
        have hw : |(2606999291/5000000000 : ℝ)|=(2606999291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s3_1 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338241989/2500000000 : ℝ)*x 0 + (-99705489/500000000 : ℝ)*x 1 + (325874909/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338241989/2500000000 : ℝ)^4505 ≤ (5567571368679/12500000000000 : ℝ)^3481 := by
    have hnat : (1338241989 : ℕ)^4505*12500000000000^3481 ≤ 5567571368679^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338241989 2500000000 5567571368679 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99705489/500000000 : ℝ)^4505 ≤ (620479461557/5000000000000 : ℝ)^3481 := by
    have hnat : (99705489 : ℕ)^4505*5000000000000^3481 ≤ 620479461557^3481*500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99705489 500000000 620479461557 5000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325874909/625000000 : ℝ)^4505 ≤ (5381229974831/12500000000000 : ℝ)^3481 := by
    have hnat : (325874909 : ℕ)^4505*12500000000000^3481 ≤ 5381229974831^3481*625000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325874909 625000000 5381229974831 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338241989/2500000000 : ℝ), (-99705489/500000000 : ℝ), (325874909/625000000 : ℝ)] ![(5567571368679/12500000000000 : ℝ), (620479461557/5000000000000 : ℝ), (5381229974831/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338241989/2500000000 : ℝ)|^4505 ≤ (5567571368679/12500000000000 : ℝ)^3481
        have hw : |(1338241989/2500000000 : ℝ)|=(1338241989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99705489/500000000 : ℝ)|^4505 ≤ (620479461557/5000000000000 : ℝ)^3481
        have hw : |(-99705489/500000000 : ℝ)|=(99705489/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325874909/625000000 : ℝ)|^4505 ≤ (5381229974831/12500000000000 : ℝ)^3481
        have hw : |(325874909/625000000 : ℝ)|=(325874909/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s3_2 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338241983/2500000000 : ℝ)*x 0 + (651749821/1250000000 : ℝ)*x 1 + (-1994109781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338241983/2500000000 : ℝ)^4505 ≤ (4454057069099/10000000000000 : ℝ)^3481 := by
    have hnat : (1338241983 : ℕ)^4505*10000000000000^3481 ≤ 4454057069099^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338241983 2500000000 4454057069099 10000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651749821/1250000000 : ℝ)^4505 ≤ (21524920027549/50000000000000 : ℝ)^3481 := by
    have hnat : (651749821 : ℕ)^4505*50000000000000^3481 ≤ 21524920027549^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651749821 1250000000 21524920027549 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1994109781/10000000000 : ℝ)^4505 ≤ (12409589239193/100000000000000 : ℝ)^3481 := by
    have hnat : (1994109781 : ℕ)^4505*100000000000000^3481 ≤ 12409589239193^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994109781 10000000000 12409589239193 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338241983/2500000000 : ℝ), (651749821/1250000000 : ℝ), (-1994109781/10000000000 : ℝ)] ![(4454057069099/10000000000000 : ℝ), (21524920027549/50000000000000 : ℝ), (12409589239193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338241983/2500000000 : ℝ)|^4505 ≤ (4454057069099/10000000000000 : ℝ)^3481
        have hw : |(1338241983/2500000000 : ℝ)|=(1338241983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651749821/1250000000 : ℝ)|^4505 ≤ (21524920027549/50000000000000 : ℝ)^3481
        have hw : |(651749821/1250000000 : ℝ)|=(651749821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1994109781/10000000000 : ℝ)|^4505 ≤ (12409589239193/100000000000000 : ℝ)^3481
        have hw : |(-1994109781/10000000000 : ℝ)|=(1994109781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s3_3 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427317071/1000000000 : ℝ)*x 0 + (805431397/2000000000 : ℝ)*x 1 + (2265961493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427317071/1000000000 : ℝ)^4505 ≤ (6655162276513/20000000000000 : ℝ)^3481 := by
    have hnat : (427317071 : ℕ)^4505*20000000000000^3481 ≤ 6655162276513^3481*1000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427317071 1000000000 6655162276513 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805431397/2000000000 : ℝ)^4505 ≤ (7704450142389/25000000000000 : ℝ)^3481 := by
    have hnat : (805431397 : ℕ)^4505*25000000000000^3481 ≤ 7704450142389^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805431397 2000000000 7704450142389 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265961493/5000000000 : ℝ)^4505 ≤ (35906388035333/100000000000000 : ℝ)^3481 := by
    have hnat : (2265961493 : ℕ)^4505*100000000000000^3481 ≤ 35906388035333^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265961493 5000000000 35906388035333 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427317071/1000000000 : ℝ), (805431397/2000000000 : ℝ), (2265961493/5000000000 : ℝ)] ![(6655162276513/20000000000000 : ℝ), (7704450142389/25000000000000 : ℝ), (35906388035333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427317071/1000000000 : ℝ)|^4505 ≤ (6655162276513/20000000000000 : ℝ)^3481
        have hw : |(427317071/1000000000 : ℝ)|=(427317071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805431397/2000000000 : ℝ)|^4505 ≤ (7704450142389/25000000000000 : ℝ)^3481
        have hw : |(805431397/2000000000 : ℝ)|=(805431397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265961493/5000000000 : ℝ)|^4505 ≤ (35906388035333/100000000000000 : ℝ)^3481
        have hw : |(2265961493/5000000000 : ℝ)|=(2265961493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s3_4 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1879385961/10000000000 : ℝ)*x 0 + (5215185141/10000000000 : ℝ)*x 1 + (5436665221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879385961/10000000000 : ℝ)^4505 ≤ (2298711442943/20000000000000 : ℝ)^3481 := by
    have hnat : (1879385961 : ℕ)^4505*20000000000000^3481 ≤ 2298711442943^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879385961 10000000000 2298711442943 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215185141/10000000000 : ℝ)^4505 ≤ (43062519504781/100000000000000 : ℝ)^3481 := by
    have hnat : (5215185141 : ℕ)^4505*100000000000000^3481 ≤ 43062519504781^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215185141 10000000000 43062519504781 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436665221/10000000000 : ℝ)^4505 ≤ (2840245203759/6250000000000 : ℝ)^3481 := by
    have hnat : (5436665221 : ℕ)^4505*6250000000000^3481 ≤ 2840245203759^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436665221 10000000000 2840245203759 6250000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1879385961/10000000000 : ℝ), (5215185141/10000000000 : ℝ), (5436665221/10000000000 : ℝ)] ![(2298711442943/20000000000000 : ℝ), (43062519504781/100000000000000 : ℝ), (2840245203759/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1879385961/10000000000 : ℝ)|^4505 ≤ (2298711442943/20000000000000 : ℝ)^3481
        have hw : |(-1879385961/10000000000 : ℝ)|=(1879385961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215185141/10000000000 : ℝ)|^4505 ≤ (43062519504781/100000000000000 : ℝ)^3481
        have hw : |(5215185141/10000000000 : ℝ)|=(5215185141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436665221/10000000000 : ℝ)|^4505 ≤ (2840245203759/6250000000000 : ℝ)^3481
        have hw : |(5436665221/10000000000 : ℝ)|=(5436665221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s3_5 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529427191/1000000000 : ℝ)*x 0 + (-177144269/1000000000 : ℝ)*x 1 + (679583167/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529427191/1000000000 : ℝ)^4505 ≤ (5488691177551/12500000000000 : ℝ)^3481 := by
    have hnat : (529427191 : ℕ)^4505*12500000000000^3481 ≤ 5488691177551^3481*1000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529427191 1000000000 5488691177551 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177144269/1000000000 : ℝ)^4505 ≤ (5323273031137/50000000000000 : ℝ)^3481 := by
    have hnat : (177144269 : ℕ)^4505*50000000000000^3481 ≤ 5323273031137^3481*1000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177144269 1000000000 5323273031137 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679583167/1250000000 : ℝ)^4505 ≤ (45443924504177/100000000000000 : ℝ)^3481 := by
    have hnat : (679583167 : ℕ)^4505*100000000000000^3481 ≤ 45443924504177^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679583167 1250000000 45443924504177 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529427191/1000000000 : ℝ), (-177144269/1000000000 : ℝ), (679583167/1250000000 : ℝ)] ![(5488691177551/12500000000000 : ℝ), (5323273031137/50000000000000 : ℝ), (45443924504177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529427191/1000000000 : ℝ)|^4505 ≤ (5488691177551/12500000000000 : ℝ)^3481
        have hw : |(529427191/1000000000 : ℝ)|=(529427191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177144269/1000000000 : ℝ)|^4505 ≤ (5323273031137/50000000000000 : ℝ)^3481
        have hw : |(-177144269/1000000000 : ℝ)|=(177144269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679583167/1250000000 : ℝ)|^4505 ≤ (45443924504177/100000000000000 : ℝ)^3481
        have hw : |(679583167/1250000000 : ℝ)|=(679583167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s3_6 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323567949/2500000000 : ℝ)*x 0 + (16989579/31250000 : ℝ)*x 1 + (-442860731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323567949/2500000000 : ℝ)^4505 ≤ (43909528196783/100000000000000 : ℝ)^3481 := by
    have hnat : (1323567949 : ℕ)^4505*100000000000000^3481 ≤ 43909528196783^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323567949 2500000000 43909528196783 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16989579/31250000 : ℝ)^4505 ≤ (45443923898387/100000000000000 : ℝ)^3481 := by
    have hnat : (16989579 : ℕ)^4505*100000000000000^3481 ≤ 45443923898387^3481*31250000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16989579 31250000 45443923898387 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442860731/2500000000 : ℝ)^4505 ≤ (1330818485293/12500000000000 : ℝ)^3481 := by
    have hnat : (442860731 : ℕ)^4505*12500000000000^3481 ≤ 1330818485293^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442860731 2500000000 1330818485293 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323567949/2500000000 : ℝ), (16989579/31250000 : ℝ), (-442860731/2500000000 : ℝ)] ![(43909528196783/100000000000000 : ℝ), (45443923898387/100000000000000 : ℝ), (1330818485293/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323567949/2500000000 : ℝ)|^4505 ≤ (43909528196783/100000000000000 : ℝ)^3481
        have hw : |(1323567949/2500000000 : ℝ)|=(1323567949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16989579/31250000 : ℝ)|^4505 ≤ (45443923898387/100000000000000 : ℝ)^3481
        have hw : |(16989579/31250000 : ℝ)|=(16989579/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442860731/2500000000 : ℝ)|^4505 ≤ (1330818485293/12500000000000 : ℝ)^3481
        have hw : |(-442860731/2500000000 : ℝ)|=(442860731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s3_7 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2136621727/5000000000 : ℝ)*x 0 + (2264623907/5000000000 : ℝ)*x 1 + (1007463047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136621727/5000000000 : ℝ)^4505 ≤ (4159568061213/12500000000000 : ℝ)^3481 := by
    have hnat : (2136621727 : ℕ)^4505*12500000000000^3481 ≤ 4159568061213^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136621727 5000000000 4159568061213 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264623907/5000000000 : ℝ)^4505 ≤ (35878960046277/100000000000000 : ℝ)^3481 := by
    have hnat : (2264623907 : ℕ)^4505*100000000000000^3481 ≤ 35878960046277^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264623907 5000000000 35878960046277 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007463047/2500000000 : ℝ)^4505 ≤ (15422247727953/50000000000000 : ℝ)^3481 := by
    have hnat : (1007463047 : ℕ)^4505*50000000000000^3481 ≤ 15422247727953^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007463047 2500000000 15422247727953 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136621727/5000000000 : ℝ), (2264623907/5000000000 : ℝ), (1007463047/2500000000 : ℝ)] ![(4159568061213/12500000000000 : ℝ), (35878960046277/100000000000000 : ℝ), (15422247727953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136621727/5000000000 : ℝ)|^4505 ≤ (4159568061213/12500000000000 : ℝ)^3481
        have hw : |(2136621727/5000000000 : ℝ)|=(2136621727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264623907/5000000000 : ℝ)|^4505 ≤ (35878960046277/100000000000000 : ℝ)^3481
        have hw : |(2264623907/5000000000 : ℝ)|=(2264623907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007463047/2500000000 : ℝ)|^4505 ≤ (15422247727953/50000000000000 : ℝ)^3481
        have hw : |(1007463047/2500000000 : ℝ)|=(1007463047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1504_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (338/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3111/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5191/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5191/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5191/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5191/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5191/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5191/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5191/50000 : ℝ) ^ (4503/1024 : ℝ) ≤ (4722089692884433/100000000000000000000 : ℝ) := by
    have hpowers : (5191/50000 : ℝ)^4503 ≤ (4722089692884433/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5191 : ℕ)^4503*100000000000000000000^1024 ≤ 4722089692884433^1024*50000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5191 50000 4722089692884433 100000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5191/50000 : ℝ)) (X := (4722089692884433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16027/100000 : ℝ) ^ (4503/1024 : ℝ) ≤ (15934512333673077/50000000000000000000 : ℝ) := by
    have hpowers : (16027/100000 : ℝ)^4503 ≤ (15934512333673077/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16027 : ℕ)^4503*50000000000000000000^1024 ≤ 15934512333673077^1024*100000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16027 100000 15934512333673077 50000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16027/100000 : ℝ)) (X := (15934512333673077/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004722089692884433/50000000000000000000 : ℝ) ≤ (10000214756537699/10000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (50004722089692884433/50000000000000000000 : ℝ)^1024 ≤ (10000214756537699/10000000000000000 : ℝ)^4503 := by
      have hnat : (50004722089692884433 : ℕ)^1024*10000000000000000^4503 ≤ 10000214756537699^4503*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004722089692884433 50000000000000000000 10000214756537699 10000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000214756537699/10000000000000000 : ℝ)) (X := (50004722089692884433/50000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036591114360230587/100000000000000000000 : ℝ) ≤ (10000831978812699/10000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (100036591114360230587/100000000000000000000 : ℝ)^1024 ≤ (10000831978812699/10000000000000000 : ℝ)^4503 := by
      have hnat : (100036591114360230587 : ℕ)^1024*10000000000000000^4503 ≤ 10000831978812699^4503*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036591114360230587 100000000000000000000 10000831978812699 10000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000831978812699/10000000000000000 : ℝ)) (X := (100036591114360230587/100000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015934512333673077/25000000000000000000 : ℝ) ≤ (10001449201087699/10000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (25015934512333673077/25000000000000000000 : ℝ)^1024 ≤ (10001449201087699/10000000000000000 : ℝ)^4503 := by
      have hnat : (25015934512333673077 : ℕ)^1024*10000000000000000^4503 ≤ 10001449201087699^4503*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015934512333673077 25000000000000000000 10001449201087699 10000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001449201087699/10000000000000000 : ℝ)) (X := (25015934512333673077/25000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4722089692884433/100000000000000000000 : ℝ) ≤ ((11287679259467442171/11290000000000000000 : ℝ)+2*(24688891/22580000000 : ℝ)*(5191/50000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (11287679259467442171/11290000000000000000 : ℝ)+2*(24688891/22580000000 : ℝ)*(5191/50000 : ℝ)=(10000214756537699/10000000000000000 : ℝ) by norm_num, show 1+2*(4722089692884433/100000000000000000000 : ℝ)=(50004722089692884433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15934512333673077/50000000000000000000 : ℝ)+(4722089692884433/100000000000000000000 : ℝ) ≤ ((11287679259467442171/11290000000000000000 : ℝ)+(24688891/22580000000 : ℝ)*((16027/100000 : ℝ)+(5191/50000 : ℝ)))^(4503/1024 : ℝ) := by
    rw [show (11287679259467442171/11290000000000000000 : ℝ)+(24688891/22580000000 : ℝ)*((16027/100000 : ℝ)+(5191/50000 : ℝ))=(10000831978812699/10000000000000000 : ℝ) by norm_num, show 1+(15934512333673077/50000000000000000000 : ℝ)+(4722089692884433/100000000000000000000 : ℝ)=(100036591114360230587/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15934512333673077/50000000000000000000 : ℝ) ≤ ((11287679259467442171/11290000000000000000 : ℝ)+2*(24688891/22580000000 : ℝ)*(16027/100000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (11287679259467442171/11290000000000000000 : ℝ)+2*(24688891/22580000000 : ℝ)*(16027/100000 : ℝ)=(10001449201087699/10000000000000000 : ℝ) by norm_num, show 1+2*(15934512333673077/50000000000000000000 : ℝ)=(25015934512333673077/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11287679259467442171/11290000000000000000 : ℝ)*(X 1 0+X 2 0)+(24688891/22580000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (5191/50000 : ℝ)) (hi := (16027/100000 : ℝ)) (c := (11287679259467442171/11290000000000000000 : ℝ)) (alpha := (24688891/22580000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11287679259467442171/11290000000000000000 : ℝ)*(X 0 1+X 2 1)+(24688891/22580000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (5191/50000 : ℝ)) (hi := (16027/100000 : ℝ)) (c := (11287679259467442171/11290000000000000000 : ℝ)) (alpha := (24688891/22580000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11287679259467442171/11290000000000000000 : ℝ)*(X 0 2+X 1 2)+(24688891/22580000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (5191/50000 : ℝ)) (hi := (16027/100000 : ℝ)) (c := (11287679259467442171/11290000000000000000 : ℝ)) (alpha := (24688891/22580000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-939677/5000000 : ℝ)*X 0 0+(2718930329/5000000000 : ℝ)*X 0 1+(2606999291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338241989/2500000000 : ℝ)*X 1 0+(-99705489/500000000 : ℝ)*X 1 1+(325874909/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338241983/2500000000 : ℝ)*X 2 0+(651749821/1250000000 : ℝ)*X 2 1+(-1994109781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((427317071/1000000000 : ℝ)*X 0 0+(805431397/2000000000 : ℝ)*X 0 1+(2265961493/5000000000 : ℝ)*X 0 2+(427317071/1000000000 : ℝ)*X 1 0+(805431397/2000000000 : ℝ)*X 1 1+(2265961493/5000000000 : ℝ)*X 1 2+(427317071/1000000000 : ℝ)*X 2 0+(805431397/2000000000 : ℝ)*X 2 1+(2265961493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1879385961/10000000000 : ℝ)*X 0 0+(5215185141/10000000000 : ℝ)*X 0 1+(5436665221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529427191/1000000000 : ℝ)*X 1 0+(-177144269/1000000000 : ℝ)*X 1 1+(679583167/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323567949/2500000000 : ℝ)*X 2 0+(16989579/31250000 : ℝ)*X 2 1+(-442860731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2136621727/5000000000 : ℝ)*X 0 0+(2264623907/5000000000 : ℝ)*X 0 1+(1007463047/2500000000 : ℝ)*X 0 2+(2136621727/5000000000 : ℝ)*X 1 0+(2264623907/5000000000 : ℝ)*X 1 1+(1007463047/2500000000 : ℝ)*X 1 2+(2136621727/5000000000 : ℝ)*X 2 0+(2264623907/5000000000 : ℝ)*X 2 1+(1007463047/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (782376624574471448623974411/282250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108016333/20000000000000 : ℝ)*(base19) + (480352563/100000000000000 : ℝ)*(base23) + (21251871/100000000000000 : ℝ)*(lower2) + (17293987/25000000000000 : ℝ)*(upper3) + (17906179/50000000000000 : ℝ)*(upper5) + (1612043857993049/50000000000000 : ℝ)*(major0) + (1612043857993049/50000000000000 : ℝ)*(major1) + (1612043857993049/50000000000000 : ℝ)*(major2) + (2233522280751079/50000000000000 : ℝ)*(sp0) + (34898841882041/781250000000 : ℝ)*(sp1) + (4467051820630349/100000000000000 : ℝ)*(sp2) + (247639911306087/12500000000000 : ℝ)*(sp3) + (3869740377/50000000000000 : ℝ)*(sp4) + (749628597/20000000000000 : ℝ)*(sp7) + (1981123038591681/100000000000000 : ℝ)*(f.failure) + (34898846101429/781250000000 : ℝ)*(f.sum) + (1132548352131/282250000000000000000000000 : ℝ)*base66 + (4766244776478530621/564500000000000000000000000000000 : ℝ)*base68 + (5020733455649530621/564500000000000000000000000000000 : ℝ)*base70 + (1653688198723530621/564500000000000000000000000000000 : ℝ)*base72 + (38821208939/112900000000000000000000000 : ℝ)*base74 + (8253730134418530621/564500000000000000000000000000000 : ℝ)*base76 + (7297874855833530621/564500000000000000000000000000000 : ℝ)*base78 + (9765888028511530621/564500000000000000000000000000000 : ℝ)*base80 + (2808367432157/1129000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (13918231/1250000000000000000000 : ℝ)*base89 + (13918231/1250000000000000000000 : ℝ)*base91 + (13918231/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93178145137696629318075231/35281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (674318309/100000000000000 : ℝ)*(base19) + (442773071/50000000000000 : ℝ)*(base23) + (4975271/6250000000000 : ℝ)*(upper3) + (156250603/100000000000000 : ℝ)*(lower4) + (407343334348963/12500000000000 : ℝ)*(major0) + (407343334348963/12500000000000 : ℝ)*(major1) + (407343334348963/12500000000000 : ℝ)*(major2) + (12576326029/100000000000000 : ℝ)*(sp1) + (13777574781/100000000000000 : ℝ)*(sp2) + (112761/3125000000000 : ℝ)*(sp3) + (282192071284273/6250000000000 : ℝ)*(sp4) + (451505988990403/10000000000000 : ℝ)*(sp5) + (903011695485489/20000000000000 : ℝ)*(sp6) + (1001210058696503/50000000000000 : ℝ)*(sp7) + (1001210060500679/50000000000000 : ℝ)*(f.failure) + (282192071284273/6250000000000 : ℝ)*(f.sum) + (570215607379/282250000000000000000000000 : ℝ)*base65 + (1084597849327818673/141125000000000000000000000000000 : ℝ)*base67 + (160146953502681327/141125000000000000000000000000000 : ℝ)*base70 + (415743084364818673/141125000000000000000000000000000 : ℝ)*base71 + (493716744091/282250000000000000000000000 : ℝ)*base73 + (803864298983318673/141125000000000000000000000000000 : ℝ)*base75 + (125838451945818673/141125000000000000000000000000000 : ℝ)*base77 + (1195786945792818673/141125000000000000000000000000000 : ℝ)*base79 + (3202461671389/1129000000000000000000000000 : ℝ)*base81 + (1907871/625000000000000000000 : ℝ)*base90 + (1907871/625000000000000000000 : ℝ)*base92 + (1907871/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1504_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (338/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3111/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1504_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1504_s4_0 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1879833371/10000000000 : ℝ)*x 0 + (339669953/625000000 : ℝ)*x 1 + (1304205877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879833371/10000000000 : ℝ)^4505 ≤ (11497098412209/100000000000000 : ℝ)^3481 := by
    have hnat : (1879833371 : ℕ)^4505*100000000000000^3481 ≤ 11497098412209^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879833371 10000000000 11497098412209 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339669953/625000000 : ℝ)^4505 ≤ (2271143673083/5000000000000 : ℝ)^3481 := by
    have hnat : (339669953 : ℕ)^4505*5000000000000^3481 ≤ 2271143673083^3481*625000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339669953 625000000 2271143673083 5000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304205877/2500000000 : ℝ)^4505 ≤ (21540014058713/50000000000000 : ℝ)^3481 := by
    have hnat : (1304205877 : ℕ)^4505*50000000000000^3481 ≤ 21540014058713^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304205877 2500000000 21540014058713 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1879833371/10000000000 : ℝ), (339669953/625000000 : ℝ), (1304205877/2500000000 : ℝ)] ![(11497098412209/100000000000000 : ℝ), (2271143673083/5000000000000 : ℝ), (21540014058713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1879833371/10000000000 : ℝ)|^4505 ≤ (11497098412209/100000000000000 : ℝ)^3481
        have hw : |(-1879833371/10000000000 : ℝ)|=(1879833371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339669953/625000000 : ℝ)|^4505 ≤ (2271143673083/5000000000000 : ℝ)^3481
        have hw : |(339669953/625000000 : ℝ)|=(339669953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304205877/2500000000 : ℝ)|^4505 ≤ (21540014058713/50000000000000 : ℝ)^3481
        have hw : |(1304205877/2500000000 : ℝ)|=(1304205877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s4_1 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352147777/10000000000 : ℝ)*x 0 + (-995728737/5000000000 : ℝ)*x 1 + (1043364709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352147777/10000000000 : ℝ)^4505 ≤ (44531739118113/100000000000000 : ℝ)^3481 := by
    have hnat : (5352147777 : ℕ)^4505*100000000000000^3481 ≤ 44531739118113^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352147777 10000000000 44531739118113 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995728737/5000000000 : ℝ)^4505 ≤ (12388232354183/100000000000000 : ℝ)^3481 := by
    have hnat : (995728737 : ℕ)^4505*100000000000000^3481 ≤ 12388232354183^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995728737 5000000000 12388232354183 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043364709/2000000000 : ℝ)^4505 ≤ (43080028512849/100000000000000 : ℝ)^3481 := by
    have hnat : (1043364709 : ℕ)^4505*100000000000000^3481 ≤ 43080028512849^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043364709 2000000000 43080028512849 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352147777/10000000000 : ℝ), (-995728737/5000000000 : ℝ), (1043364709/2000000000 : ℝ)] ![(44531739118113/100000000000000 : ℝ), (12388232354183/100000000000000 : ℝ), (43080028512849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352147777/10000000000 : ℝ)|^4505 ≤ (44531739118113/100000000000000 : ℝ)^3481
        have hw : |(5352147777/10000000000 : ℝ)|=(5352147777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-995728737/5000000000 : ℝ)|^4505 ≤ (12388232354183/100000000000000 : ℝ)^3481
        have hw : |(-995728737/5000000000 : ℝ)|=(995728737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043364709/2000000000 : ℝ)|^4505 ≤ (43080028512849/100000000000000 : ℝ)^3481
        have hw : |(1043364709/2000000000 : ℝ)|=(1043364709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s4_2 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352147671/10000000000 : ℝ)*x 0 + (5216823531/10000000000 : ℝ)*x 1 + (-398291527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352147671/10000000000 : ℝ)^4505 ≤ (5566467247089/12500000000000 : ℝ)^3481 := by
    have hnat : (5352147671 : ℕ)^4505*12500000000000^3481 ≤ 5566467247089^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352147671 10000000000 5566467247089 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216823531/10000000000 : ℝ)^4505 ≤ (4308002836323/10000000000000 : ℝ)^3481 := by
    have hnat : (5216823531 : ℕ)^4505*10000000000000^3481 ≤ 4308002836323^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216823531 10000000000 4308002836323 10000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398291527/2000000000 : ℝ)^4505 ≤ (12388233650333/100000000000000 : ℝ)^3481 := by
    have hnat : (398291527 : ℕ)^4505*100000000000000^3481 ≤ 12388233650333^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398291527 2000000000 12388233650333 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352147671/10000000000 : ℝ), (5216823531/10000000000 : ℝ), (-398291527/2000000000 : ℝ)] ![(5566467247089/12500000000000 : ℝ), (4308002836323/10000000000000 : ℝ), (12388233650333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352147671/10000000000 : ℝ)|^4505 ≤ (5566467247089/12500000000000 : ℝ)^3481
        have hw : |(5352147671/10000000000 : ℝ)|=(5352147671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216823531/10000000000 : ℝ)|^4505 ≤ (4308002836323/10000000000000 : ℝ)^3481
        have hw : |(5216823531/10000000000 : ℝ)|=(5216823531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398291527/2000000000 : ℝ)|^4505 ≤ (12388233650333/100000000000000 : ℝ)^3481
        have hw : |(-398291527/2000000000 : ℝ)|=(398291527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s4_3 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273470493/10000000000 : ℝ)*x 0 + (806769839/2000000000 : ℝ)*x 1 + (2262580771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273470493/10000000000 : ℝ)^4505 ≤ (33278832590841/100000000000000 : ℝ)^3481 := by
    have hnat : (4273470493 : ℕ)^4505*100000000000000^3481 ≤ 33278832590841^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273470493 10000000000 33278832590841 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806769839/2000000000 : ℝ)^4505 ≤ (308840938499/1000000000000 : ℝ)^3481 := by
    have hnat : (806769839 : ℕ)^4505*1000000000000^3481 ≤ 308840938499^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806769839 2000000000 308840938499 1000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262580771/5000000000 : ℝ)^4505 ≤ (179185367689/500000000000 : ℝ)^3481 := by
    have hnat : (2262580771 : ℕ)^4505*500000000000^3481 ≤ 179185367689^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262580771 5000000000 179185367689 500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273470493/10000000000 : ℝ), (806769839/2000000000 : ℝ), (2262580771/5000000000 : ℝ)] ![(33278832590841/100000000000000 : ℝ), (308840938499/1000000000000 : ℝ), (179185367689/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273470493/10000000000 : ℝ)|^4505 ≤ (33278832590841/100000000000000 : ℝ)^3481
        have hw : |(4273470493/10000000000 : ℝ)|=(4273470493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806769839/2000000000 : ℝ)|^4505 ≤ (308840938499/1000000000000 : ℝ)^3481
        have hw : |(806769839/2000000000 : ℝ)|=(806769839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262580771/5000000000 : ℝ)|^4505 ≤ (179185367689/500000000000 : ℝ)^3481
        have hw : |(2262580771/5000000000 : ℝ)|=(2262580771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s4_4 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46996581/250000000 : ℝ)*x 0 + (5217947583/10000000000 : ℝ)*x 1 + (1086717339/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46996581/250000000 : ℝ)^4505 ≤ (5748667415329/50000000000000 : ℝ)^3481 := by
    have hnat : (46996581 : ℕ)^4505*50000000000000^3481 ≤ 5748667415329^3481*250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46996581 250000000 5748667415329 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217947583/10000000000 : ℝ)^4505 ≤ (43092041620333/100000000000000 : ℝ)^3481 := by
    have hnat : (5217947583 : ℕ)^4505*100000000000000^3481 ≤ 43092041620333^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217947583 10000000000 43092041620333 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086717339/2000000000 : ℝ)^4505 ≤ (22705311767553/50000000000000 : ℝ)^3481 := by
    have hnat : (1086717339 : ℕ)^4505*50000000000000^3481 ≤ 22705311767553^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086717339 2000000000 22705311767553 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46996581/250000000 : ℝ), (5217947583/10000000000 : ℝ), (1086717339/2000000000 : ℝ)] ![(5748667415329/50000000000000 : ℝ), (43092041620333/100000000000000 : ℝ), (22705311767553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46996581/250000000 : ℝ)|^4505 ≤ (5748667415329/50000000000000 : ℝ)^3481
        have hw : |(-46996581/250000000 : ℝ)|=(46996581/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217947583/10000000000 : ℝ)|^4505 ≤ (43092041620333/100000000000000 : ℝ)^3481
        have hw : |(5217947583/10000000000 : ℝ)|=(5217947583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086717339/2000000000 : ℝ)|^4505 ≤ (22705311767553/50000000000000 : ℝ)^3481
        have hw : |(1086717339/2000000000 : ℝ)|=(1086717339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s4_5 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330938551/625000000 : ℝ)*x 0 + (-354938979/2000000000 : ℝ)*x 1 + (2716793467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330938551/625000000 : ℝ)^4505 ≤ (10979381267587/25000000000000 : ℝ)^3481 := by
    have hnat : (330938551 : ℕ)^4505*25000000000000^3481 ≤ 10979381267587^3481*625000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330938551 625000000 10979381267587 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354938979/2000000000 : ℝ)^4505 ≤ (10671848800559/100000000000000 : ℝ)^3481 := by
    have hnat : (354938979 : ℕ)^4505*100000000000000^3481 ≤ 10671848800559^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354938979 2000000000 10671848800559 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716793467/5000000000 : ℝ)^4505 ≤ (454106261201/1000000000000 : ℝ)^3481 := by
    have hnat : (2716793467 : ℕ)^4505*1000000000000^3481 ≤ 454106261201^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716793467 5000000000 454106261201 1000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330938551/625000000 : ℝ), (-354938979/2000000000 : ℝ), (2716793467/5000000000 : ℝ)] ![(10979381267587/25000000000000 : ℝ), (10671848800559/100000000000000 : ℝ), (454106261201/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330938551/625000000 : ℝ)|^4505 ≤ (10979381267587/25000000000000 : ℝ)^3481
        have hw : |(330938551/625000000 : ℝ)|=(330938551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-354938979/2000000000 : ℝ)|^4505 ≤ (10671848800559/100000000000000 : ℝ)^3481
        have hw : |(-354938979/2000000000 : ℝ)|=(354938979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716793467/5000000000 : ℝ)|^4505 ≤ (454106261201/1000000000000 : ℝ)^3481
        have hw : |(2716793467/5000000000 : ℝ)|=(2716793467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s4_6 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647508979/5000000000 : ℝ)*x 0 + (5433586027/10000000000 : ℝ)*x 1 + (-88734729/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647508979/5000000000 : ℝ)^4505 ≤ (5489692166071/12500000000000 : ℝ)^3481 := by
    have hnat : (2647508979 : ℕ)^4505*12500000000000^3481 ≤ 5489692166071^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647508979 5000000000 5489692166071 12500000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433586027/10000000000 : ℝ)^4505 ≤ (22705308155051/50000000000000 : ℝ)^3481 := by
    have hnat : (5433586027 : ℕ)^4505*50000000000000^3481 ≤ 22705308155051^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433586027 10000000000 22705308155051 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88734729/500000000 : ℝ)^4505 ≤ (5335923174571/50000000000000 : ℝ)^3481 := by
    have hnat : (88734729 : ℕ)^4505*50000000000000^3481 ≤ 5335923174571^3481*500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88734729 500000000 5335923174571 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647508979/5000000000 : ℝ), (5433586027/10000000000 : ℝ), (-88734729/500000000 : ℝ)] ![(5489692166071/12500000000000 : ℝ), (22705308155051/50000000000000 : ℝ), (5335923174571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647508979/5000000000 : ℝ)|^4505 ≤ (5489692166071/12500000000000 : ℝ)^3481
        have hw : |(2647508979/5000000000 : ℝ)|=(2647508979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433586027/10000000000 : ℝ)|^4505 ≤ (22705308155051/50000000000000 : ℝ)^3481
        have hw : |(5433586027/10000000000 : ℝ)|=(5433586027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88734729/500000000 : ℝ)|^4505 ≤ (5335923174571/50000000000000 : ℝ)^3481
        have hw : |(-88734729/500000000 : ℝ)|=(88734729/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s4_7 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854707491/2000000000 : ℝ)*x 0 + (904525417/2000000000 : ℝ)*x 1 + (1009100561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854707491/2000000000 : ℝ)^4505 ≤ (8319876860331/25000000000000 : ℝ)^3481 := by
    have hnat : (854707491 : ℕ)^4505*25000000000000^3481 ≤ 8319876860331^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854707491 2000000000 8319876860331 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904525417/2000000000 : ℝ)^4505 ≤ (17905549782939/50000000000000 : ℝ)^3481 := by
    have hnat : (904525417 : ℕ)^4505*50000000000000^3481 ≤ 17905549782939^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904525417 2000000000 17905549782939 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009100561/2500000000 : ℝ)^4505 ≤ (30909392977669/100000000000000 : ℝ)^3481 := by
    have hnat : (1009100561 : ℕ)^4505*100000000000000^3481 ≤ 30909392977669^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009100561 2500000000 30909392977669 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854707491/2000000000 : ℝ), (904525417/2000000000 : ℝ), (1009100561/2500000000 : ℝ)] ![(8319876860331/25000000000000 : ℝ), (17905549782939/50000000000000 : ℝ), (30909392977669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854707491/2000000000 : ℝ)|^4505 ≤ (8319876860331/25000000000000 : ℝ)^3481
        have hw : |(854707491/2000000000 : ℝ)|=(854707491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904525417/2000000000 : ℝ)|^4505 ≤ (17905549782939/50000000000000 : ℝ)^3481
        have hw : |(904525417/2000000000 : ℝ)|=(904525417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1009100561/2500000000 : ℝ)|^4505 ≤ (30909392977669/100000000000000 : ℝ)^3481
        have hw : |(1009100561/2500000000 : ℝ)|=(1009100561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1504_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3111/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (338/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2719/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3111/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (338/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3111/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (338/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3111/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (338/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3111/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (338/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3111/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (338/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3111/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (338/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (338/3125 : ℝ) ^ (4503/1024 : ℝ) ≤ (1130774344760117/20000000000000000000 : ℝ) := by
    have hpowers : (338/3125 : ℝ)^4503 ≤ (1130774344760117/20000000000000000000 : ℝ)^1024 := by
      have hnat : (338 : ℕ)^4503*20000000000000000000^1024 ≤ 1130774344760117^1024*3125^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        338 3125 1130774344760117 20000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (338/3125 : ℝ)) (X := (1130774344760117/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3111/20000 : ℝ) ^ (4503/1024 : ℝ) ≤ (1746465366949489/6250000000000000000 : ℝ) := by
    have hpowers : (3111/20000 : ℝ)^4503 ≤ (1746465366949489/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3111 : ℕ)^4503*6250000000000000000^1024 ≤ 1746465366949489^1024*20000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3111 20000 1746465366949489 6250000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3111/20000 : ℝ)) (X := (1746465366949489/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001130774344760117/10000000000000000000 : ℝ) ≤ (2000051426264843/2000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (10001130774344760117/10000000000000000000 : ℝ)^1024 ≤ (2000051426264843/2000000000000000 : ℝ)^4503 := by
      have hnat : (10001130774344760117 : ℕ)^1024*2000000000000000^4503 ≤ 2000051426264843^4503*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001130774344760117 10000000000000000000 2000051426264843 2000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000051426264843/2000000000000000 : ℝ)) (X := (10001130774344760117/10000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033597317594992409/100000000000000000000 : ℝ) ≤ (5000381958572049/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (100033597317594992409/100000000000000000000 : ℝ)^1024 ≤ (5000381958572049/5000000000000000 : ℝ)^4503 := by
      have hnat : (100033597317594992409 : ℕ)^1024*5000000000000000^4503 ≤ 5000381958572049^4503*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033597317594992409 100000000000000000000 5000381958572049 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000381958572049/5000000000000000 : ℝ)) (X := (100033597317594992409/100000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126746465366949489/3125000000000000000 : ℝ) ≤ (10001270702963981/10000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (3126746465366949489/3125000000000000000 : ℝ)^1024 ≤ (10001270702963981/10000000000000000 : ℝ)^4503 := by
      have hnat : (3126746465366949489 : ℕ)^1024*10000000000000000^4503 ≤ 10001270702963981^4503*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126746465366949489 3125000000000000000 10001270702963981 10000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001270702963981/10000000000000000 : ℝ)) (X := (3126746465366949489/3125000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1130774344760117/20000000000000000000 : ℝ) ≤ ((6768607964927106547/6770000000000000000 : ℝ)+2*(72397974269/67700000000000 : ℝ)*(338/3125 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (6768607964927106547/6770000000000000000 : ℝ)+2*(72397974269/67700000000000 : ℝ)*(338/3125 : ℝ)=(2000051426264843/2000000000000000 : ℝ) by norm_num, show 1+2*(1130774344760117/20000000000000000000 : ℝ)=(10001130774344760117/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1746465366949489/6250000000000000000 : ℝ)+(1130774344760117/20000000000000000000 : ℝ) ≤ ((6768607964927106547/6770000000000000000 : ℝ)+(72397974269/67700000000000 : ℝ)*((3111/20000 : ℝ)+(338/3125 : ℝ)))^(4503/1024 : ℝ) := by
    rw [show (6768607964927106547/6770000000000000000 : ℝ)+(72397974269/67700000000000 : ℝ)*((3111/20000 : ℝ)+(338/3125 : ℝ))=(5000381958572049/5000000000000000 : ℝ) by norm_num, show 1+(1746465366949489/6250000000000000000 : ℝ)+(1130774344760117/20000000000000000000 : ℝ)=(100033597317594992409/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1746465366949489/6250000000000000000 : ℝ) ≤ ((6768607964927106547/6770000000000000000 : ℝ)+2*(72397974269/67700000000000 : ℝ)*(3111/20000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (6768607964927106547/6770000000000000000 : ℝ)+2*(72397974269/67700000000000 : ℝ)*(3111/20000 : ℝ)=(10001270702963981/10000000000000000 : ℝ) by norm_num, show 1+2*(1746465366949489/6250000000000000000 : ℝ)=(3126746465366949489/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6768607964927106547/6770000000000000000 : ℝ)*(X 1 0+X 2 0)+(72397974269/67700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (338/3125 : ℝ)) (hi := (3111/20000 : ℝ)) (c := (6768607964927106547/6770000000000000000 : ℝ)) (alpha := (72397974269/67700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6768607964927106547/6770000000000000000 : ℝ)*(X 0 1+X 2 1)+(72397974269/67700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (338/3125 : ℝ)) (hi := (3111/20000 : ℝ)) (c := (6768607964927106547/6770000000000000000 : ℝ)) (alpha := (72397974269/67700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6768607964927106547/6770000000000000000 : ℝ)*(X 0 2+X 1 2)+(72397974269/67700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (338/3125 : ℝ)) (hi := (3111/20000 : ℝ)) (c := (6768607964927106547/6770000000000000000 : ℝ)) (alpha := (72397974269/67700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1879833371/10000000000 : ℝ)*X 0 0+(339669953/625000000 : ℝ)*X 0 1+(1304205877/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352147777/10000000000 : ℝ)*X 1 0+(-995728737/5000000000 : ℝ)*X 1 1+(1043364709/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352147671/10000000000 : ℝ)*X 2 0+(5216823531/10000000000 : ℝ)*X 2 1+(-398291527/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273470493/10000000000 : ℝ)*X 0 0+(806769839/2000000000 : ℝ)*X 0 1+(2262580771/5000000000 : ℝ)*X 0 2+(4273470493/10000000000 : ℝ)*X 1 0+(806769839/2000000000 : ℝ)*X 1 1+(2262580771/5000000000 : ℝ)*X 1 2+(4273470493/10000000000 : ℝ)*X 2 0+(806769839/2000000000 : ℝ)*X 2 1+(2262580771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-46996581/250000000 : ℝ)*X 0 0+(5217947583/10000000000 : ℝ)*X 0 1+(1086717339/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330938551/625000000 : ℝ)*X 1 0+(-354938979/2000000000 : ℝ)*X 1 1+(2716793467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647508979/5000000000 : ℝ)*X 2 0+(5433586027/10000000000 : ℝ)*X 2 1+(-88734729/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((854707491/2000000000 : ℝ)*X 0 0+(904525417/2000000000 : ℝ)*X 0 1+(1009100561/2500000000 : ℝ)*X 0 2+(854707491/2000000000 : ℝ)*X 1 0+(904525417/2000000000 : ℝ)*X 1 1+(1009100561/2500000000 : ℝ)*X 1 2+(854707491/2000000000 : ℝ)*X 2 0+(904525417/2000000000 : ℝ)*X 2 1+(1009100561/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1707480340006560365229/211562500000000000000000000 : ℝ) := by norm_num
    linear_combination (683482377/50000000000000 : ℝ)*(base19) + (1192478253/100000000000000 : ℝ)*(base23) + (62439923/100000000000000 : ℝ)*(lower2) + (57340151/25000000000000 : ℝ)*(upper3) + (8849887/50000000000000 : ℝ)*(lower4) + (3312390487600643/100000000000000 : ℝ)*(major0) + (3312390487600643/100000000000000 : ℝ)*(major1) + (3312390487600643/100000000000000 : ℝ)*(major2) + (1147344352047651/25000000000000 : ℝ)*(sp0) + (2294698203696513/50000000000000 : ℝ)*(sp1) + (4589396581879527/100000000000000 : ℝ)*(sp2) + (2035372730153237/100000000000000 : ℝ)*(sp3) + (2545770897/12500000000000 : ℝ)*(sp4) + (1020166333/10000000000000 : ℝ)*(sp7) + (2035382931816567/100000000000000 : ℝ)*(f.failure) + (229469888717889/5000000000000 : ℝ)*(f.sum) + (48569389293/846250000000000000000000000 : ℝ)*base65 + (785814970261590279/677000000000000000000000000000000 : ℝ)*base68 + (308866751358590279/677000000000000000000000000000000 : ℝ)*base70 + (7327152957282409721/677000000000000000000000000000000 : ℝ)*base71 + (2216688590159/1692500000000000000000000000 : ℝ)*base74 + (142565098544590279/677000000000000000000000000000000 : ℝ)*base76 + (39634920327409721/677000000000000000000000000000000 : ℝ)*base77 + (2419056697889409721/677000000000000000000000000000000 : ℝ)*base79 + (1567446258151/1692500000000000000000000000 : ℝ)*base81 + (657583/1250000000000000000000 : ℝ)*base90 + (657583/1250000000000000000000 : ℝ)*base92 + (657583/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (749558813157450442061138637/84625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14756297/1562500000000 : ℝ)*(base19) + (2065444021/100000000000000 : ℝ)*(base23) + (20281891/10000000000000 : ℝ)*(upper3) + (5806007/100000000000000 : ℝ)*(lower4) + (24472463/12500000000000 : ℝ)*(upper5) + (1673512003719843/50000000000000 : ℝ)*(major0) + (1673512003719843/50000000000000 : ℝ)*(major1) + (1673512003719843/50000000000000 : ℝ)*(major2) + (7825767479/50000000000000 : ℝ)*(sp1) + (5167779381/20000000000000 : ℝ)*(sp2) + (37099066696229/800000000000 : ℝ)*(sp4) + (2318683370545329/50000000000000 : ℝ)*(sp5) + (2318677716343849/50000000000000 : ℝ)*(sp6) + (1028332191301771/50000000000000 : ℝ)*(sp7) + (1028332191301771/50000000000000 : ℝ)*(f.failure) + (37099066696229/800000000000 : ℝ)*(f.sum) + (2756794668671/846250000000000000000000000 : ℝ)*base65 + (1767936355143312121/338500000000000000000000000000000 : ℝ)*base67 + (1381100525890312121/338500000000000000000000000000000 : ℝ)*base69 + (249171760228187879/338500000000000000000000000000000 : ℝ)*base72 + (8031102764677/1692500000000000000000000000 : ℝ)*base73 + (5825908717970812121/338500000000000000000000000000000 : ℝ)*base75 + (416811538939312121/338500000000000000000000000000000 : ℝ)*base77 + (6583402142342312121/338500000000000000000000000000000 : ℝ)*base79 + (449092176671/3385000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4542179/625000000000000000000 : ℝ)*base90 + (4542179/625000000000000000000 : ℝ)*base92 + (4542179/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1504_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3111/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (338/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1504_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1504_s5_0 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-939946711/5000000000 : ℝ)*x 0 + (2717162609/5000000000 : ℝ)*x 1 + (208687113/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939946711/5000000000 : ℝ)^4505 ≤ (35929917899/312500000000 : ℝ)^3481 := by
    have hnat : (939946711 : ℕ)^4505*312500000000^3481 ≤ 35929917899^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939946711 5000000000 35929917899 312500000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717162609/5000000000 : ℝ)^4505 ≤ (22709305733409/50000000000000 : ℝ)^3481 := by
    have hnat : (2717162609 : ℕ)^4505*50000000000000^3481 ≤ 22709305733409^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717162609 5000000000 22709305733409 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208687113/400000000 : ℝ)^4505 ≤ (10770953695713/25000000000000 : ℝ)^3481 := by
    have hnat : (208687113 : ℕ)^4505*25000000000000^3481 ≤ 10770953695713^3481*400000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208687113 400000000 10770953695713 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-939946711/5000000000 : ℝ), (2717162609/5000000000 : ℝ), (208687113/400000000 : ℝ)] ![(35929917899/312500000000 : ℝ), (22709305733409/50000000000000 : ℝ), (10770953695713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-939946711/5000000000 : ℝ)|^4505 ≤ (35929917899/312500000000 : ℝ)^3481
        have hw : |(-939946711/5000000000 : ℝ)|=(939946711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717162609/5000000000 : ℝ)|^4505 ≤ (22709305733409/50000000000000 : ℝ)^3481
        have hw : |(2717162609/5000000000 : ℝ)|=(2717162609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208687113/400000000 : ℝ)|^4505 ≤ (10770953695713/25000000000000 : ℝ)^3481
        have hw : |(208687113/400000000 : ℝ)|=(208687113/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s5_1 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107040893/200000000 : ℝ)*x 0 + (-398225027/2000000000 : ℝ)*x 1 + (5217177793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107040893/200000000 : ℝ)^4505 ≤ (22265314328333/50000000000000 : ℝ)^3481 := by
    have hnat : (107040893 : ℕ)^4505*50000000000000^3481 ≤ 22265314328333^3481*200000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107040893 200000000 22265314328333 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398225027/2000000000 : ℝ)^4505 ≤ (3870486527/31250000000 : ℝ)^3481 := by
    have hnat : (398225027 : ℕ)^4505*31250000000^3481 ≤ 3870486527^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398225027 2000000000 3870486527 31250000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217177793/10000000000 : ℝ)^4505 ≤ (21541907220429/50000000000000 : ℝ)^3481 := by
    have hnat : (5217177793 : ℕ)^4505*50000000000000^3481 ≤ 21541907220429^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217177793 10000000000 21541907220429 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107040893/200000000 : ℝ), (-398225027/2000000000 : ℝ), (5217177793/10000000000 : ℝ)] ![(22265314328333/50000000000000 : ℝ), (3870486527/31250000000 : ℝ), (21541907220429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107040893/200000000 : ℝ)|^4505 ≤ (22265314328333/50000000000000 : ℝ)^3481
        have hw : |(107040893/200000000 : ℝ)|=(107040893/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-398225027/2000000000 : ℝ)|^4505 ≤ (3870486527/31250000000 : ℝ)^3481
        have hw : |(-398225027/2000000000 : ℝ)|=(398225027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217177793/10000000000 : ℝ)|^4505 ≤ (21541907220429/50000000000000 : ℝ)^3481
        have hw : |(5217177793/10000000000 : ℝ)|=(5217177793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s5_2 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669005577/1250000000 : ℝ)*x 0 + (163036807/312500000 : ℝ)*x 1 + (-1991125141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669005577/1250000000 : ℝ)^4505 ≤ (44530628290559/100000000000000 : ℝ)^3481 := by
    have hnat : (669005577 : ℕ)^4505*100000000000000^3481 ≤ 44530628290559^3481*1250000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669005577 1250000000 44530628290559 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163036807/312500000 : ℝ)^4505 ≤ (8616762954433/20000000000000 : ℝ)^3481 := by
    have hnat : (163036807 : ℕ)^4505*20000000000000^3481 ≤ 8616762954433^3481*312500000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163036807 312500000 8616762954433 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991125141/10000000000 : ℝ)^4505 ≤ (6192778467351/50000000000000 : ℝ)^3481 := by
    have hnat : (1991125141 : ℕ)^4505*50000000000000^3481 ≤ 6192778467351^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991125141 10000000000 6192778467351 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669005577/1250000000 : ℝ), (163036807/312500000 : ℝ), (-1991125141/10000000000 : ℝ)] ![(44530628290559/100000000000000 : ℝ), (8616762954433/20000000000000 : ℝ), (6192778467351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669005577/1250000000 : ℝ)|^4505 ≤ (44530628290559/100000000000000 : ℝ)^3481
        have hw : |(669005577/1250000000 : ℝ)|=(669005577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163036807/312500000 : ℝ)|^4505 ≤ (8616762954433/20000000000000 : ℝ)^3481
        have hw : |(163036807/312500000 : ℝ)|=(163036807/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1991125141/10000000000 : ℝ)|^4505 ≤ (6192778467351/50000000000000 : ℝ)^3481
        have hw : |(-1991125141/10000000000 : ℝ)|=(1991125141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s5_3 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273507709/10000000000 : ℝ)*x 0 + (2017344037/5000000000 : ℝ)*x 1 + (1131078477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273507709/10000000000 : ℝ)^4505 ≤ (8319801914361/25000000000000 : ℝ)^3481 := by
    have hnat : (4273507709 : ℕ)^4505*25000000000000^3481 ≤ 8319801914361^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273507709 10000000000 8319801914361 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017344037/5000000000 : ℝ)^4505 ≤ (7723101524911/25000000000000 : ℝ)^3481 := by
    have hnat : (2017344037 : ℕ)^4505*25000000000000^3481 ≤ 7723101524911^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017344037 5000000000 7723101524911 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131078477/2500000000 : ℝ)^4505 ≤ (8957096555421/25000000000000 : ℝ)^3481 := by
    have hnat : (1131078477 : ℕ)^4505*25000000000000^3481 ≤ 8957096555421^3481*2500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131078477 2500000000 8957096555421 25000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273507709/10000000000 : ℝ), (2017344037/5000000000 : ℝ), (1131078477/2500000000 : ℝ)] ![(8319801914361/25000000000000 : ℝ), (7723101524911/25000000000000 : ℝ), (8957096555421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273507709/10000000000 : ℝ)|^4505 ≤ (8319801914361/25000000000000 : ℝ)^3481
        have hw : |(4273507709/10000000000 : ℝ)|=(4273507709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2017344037/5000000000 : ℝ)|^4505 ≤ (7723101524911/25000000000000 : ℝ)^3481
        have hw : |(2017344037/5000000000 : ℝ)|=(2017344037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131078477/2500000000 : ℝ)|^4505 ≤ (8957096555421/25000000000000 : ℝ)^3481
        have hw : |(1131078477/2500000000 : ℝ)|=(1131078477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s5_4 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1879922891/10000000000 : ℝ)*x 0 + (260914713/500000000 : ℝ)*x 1 + (5433200463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879922891/10000000000 : ℝ)^4505 ≤ (5748903491121/50000000000000 : ℝ)^3481 := by
    have hnat : (1879922891 : ℕ)^4505*50000000000000^3481 ≤ 5748903491121^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879922891 10000000000 5748903491121 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260914713/500000000 : ℝ)^4505 ≤ (2154787343469/5000000000000 : ℝ)^3481 := by
    have hnat : (260914713 : ℕ)^4505*5000000000000^3481 ≤ 2154787343469^3481*500000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260914713 500000000 2154787343469 5000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433200463/10000000000 : ℝ)^4505 ≤ (4540644614197/10000000000000 : ℝ)^3481 := by
    have hnat : (5433200463 : ℕ)^4505*10000000000000^3481 ≤ 4540644614197^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433200463 10000000000 4540644614197 10000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1879922891/10000000000 : ℝ), (260914713/500000000 : ℝ), (5433200463/10000000000 : ℝ)] ![(5748903491121/50000000000000 : ℝ), (2154787343469/5000000000000 : ℝ), (4540644614197/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1879922891/10000000000 : ℝ)|^4505 ≤ (5748903491121/50000000000000 : ℝ)^3481
        have hw : |(-1879922891/10000000000 : ℝ)|=(1879922891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260914713/500000000 : ℝ)|^4505 ≤ (2154787343469/5000000000000 : ℝ)^3481
        have hw : |(260914713/500000000 : ℝ)|=(260914713/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433200463/10000000000 : ℝ)|^4505 ≤ (4540644614197/10000000000000 : ℝ)^3481
        have hw : |(5433200463/10000000000 : ℝ)|=(5433200463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s5_5 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647555361/5000000000 : ℝ)*x 0 + (-887551221/5000000000 : ℝ)*x 1 + (1086640097/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647555361/5000000000 : ℝ)^4505 ≤ (21959266529637/50000000000000 : ℝ)^3481 := by
    have hnat : (2647555361 : ℕ)^4505*50000000000000^3481 ≤ 21959266529637^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647555361 5000000000 21959266529637 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887551221/5000000000 : ℝ)^4505 ≤ (667188784481/6250000000000 : ℝ)^3481 := by
    have hnat : (887551221 : ℕ)^4505*6250000000000^3481 ≤ 667188784481^3481*5000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887551221 5000000000 667188784481 6250000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086640097/2000000000 : ℝ)^4505 ≤ (22703223189957/50000000000000 : ℝ)^3481 := by
    have hnat : (1086640097 : ℕ)^4505*50000000000000^3481 ≤ 22703223189957^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086640097 2000000000 22703223189957 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647555361/5000000000 : ℝ), (-887551221/5000000000 : ℝ), (1086640097/2000000000 : ℝ)] ![(21959266529637/50000000000000 : ℝ), (667188784481/6250000000000 : ℝ), (22703223189957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647555361/5000000000 : ℝ)|^4505 ≤ (21959266529637/50000000000000 : ℝ)^3481
        have hw : |(2647555361/5000000000 : ℝ)|=(2647555361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-887551221/5000000000 : ℝ)|^4505 ≤ (667188784481/6250000000000 : ℝ)^3481
        have hw : |(-887551221/5000000000 : ℝ)|=(887551221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086640097/2000000000 : ℝ)|^4505 ≤ (22703223189957/50000000000000 : ℝ)^3481
        have hw : |(1086640097/2000000000 : ℝ)|=(1086640097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s5_6 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295110839/10000000000 : ℝ)*x 0 + (5433200517/10000000000 : ℝ)*x 1 + (-355020447/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295110839/10000000000 : ℝ)^4505 ≤ (21959267157579/50000000000000 : ℝ)^3481 := by
    have hnat : (5295110839 : ℕ)^4505*50000000000000^3481 ≤ 21959267157579^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295110839 10000000000 21959267157579 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433200517/10000000000 : ℝ)^4505 ≤ (9081289345203/20000000000000 : ℝ)^3481 := by
    have hnat : (5433200517 : ℕ)^4505*20000000000000^3481 ≤ 9081289345203^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433200517 10000000000 9081289345203 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355020447/2000000000 : ℝ)^4505 ≤ (2135003788131/20000000000000 : ℝ)^3481 := by
    have hnat : (355020447 : ℕ)^4505*20000000000000^3481 ≤ 2135003788131^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355020447 2000000000 2135003788131 20000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295110839/10000000000 : ℝ), (5433200517/10000000000 : ℝ), (-355020447/2000000000 : ℝ)] ![(21959267157579/50000000000000 : ℝ), (9081289345203/20000000000000 : ℝ), (2135003788131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295110839/10000000000 : ℝ)|^4505 ≤ (21959267157579/50000000000000 : ℝ)^3481
        have hw : |(5295110839/10000000000 : ℝ)|=(5295110839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433200517/10000000000 : ℝ)|^4505 ≤ (9081289345203/20000000000000 : ℝ)^3481
        have hw : |(5433200517/10000000000 : ℝ)|=(5433200517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355020447/2000000000 : ℝ)|^4505 ≤ (2135003788131/20000000000000 : ℝ)^3481
        have hw : |(-355020447/2000000000 : ℝ)|=(355020447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1504_s5_7 (p : ℝ) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854714767/2000000000 : ℝ)*x 0 + (4521796377/10000000000 : ℝ)*x 1 + (4037224173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854714767/2000000000 : ℝ)^4505 ≤ (16639937042157/50000000000000 : ℝ)^3481 := by
    have hnat : (854714767 : ℕ)^4505*50000000000000^3481 ≤ 16639937042157^3481*2000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854714767 2000000000 16639937042157 50000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521796377/10000000000 : ℝ)^4505 ≤ (35802587121091/100000000000000 : ℝ)^3481 := by
    have hnat : (4521796377 : ℕ)^4505*100000000000000^3481 ≤ 35802587121091^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521796377 10000000000 35802587121091 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4037224173/10000000000 : ℝ)^4505 ≤ (30917538784737/100000000000000 : ℝ)^3481 := by
    have hnat : (4037224173 : ℕ)^4505*100000000000000^3481 ≤ 30917538784737^3481*10000000000^4505 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037224173 10000000000 30917538784737 100000000000000 4505 3481 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4505/1024 : ℝ)) 4505 3481 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854714767/2000000000 : ℝ), (4521796377/10000000000 : ℝ), (4037224173/10000000000 : ℝ)] ![(16639937042157/50000000000000 : ℝ), (35802587121091/100000000000000 : ℝ), (30917538784737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854714767/2000000000 : ℝ)|^4505 ≤ (16639937042157/50000000000000 : ℝ)^3481
        have hw : |(854714767/2000000000 : ℝ)|=(854714767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521796377/10000000000 : ℝ)|^4505 ≤ (35802587121091/100000000000000 : ℝ)^3481
        have hw : |(4521796377/10000000000 : ℝ)|=(4521796377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4037224173/10000000000 : ℝ)|^4505 ≤ (30917538784737/100000000000000 : ℝ)^3481
        have hw : |(4037224173/10000000000 : ℝ)|=(4037224173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1504_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2721/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2719/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2719/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2719/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2719/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2719/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2719/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2719/25000 : ℝ) ^ (4503/1024 : ℝ) ≤ (5793098863967893/100000000000000000000 : ℝ) := by
    have hpowers : (2719/25000 : ℝ)^4503 ≤ (5793098863967893/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2719 : ℕ)^4503*100000000000000000000^1024 ≤ 5793098863967893^1024*25000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2719 25000 5793098863967893 100000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2719/25000 : ℝ)) (X := (5793098863967893/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4503/1024 : ℝ) ≤ (27433596599401013/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4503 ≤ (27433596599401013/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4503*100000000000000000000^1024 ≤ 27433596599401013^1024*10000^4503 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 27433596599401013 100000000000000000000 4503 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (27433596599401013/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005793098863967893/50000000000000000000 : ℝ) ≤ (2500065865731167/2500000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (50005793098863967893/50000000000000000000 : ℝ)^1024 ≤ (2500065865731167/2500000000000000 : ℝ)^4503 := by
      have hnat : (50005793098863967893 : ℕ)^1024*2500000000000000^4503 ≤ 2500065865731167^4503*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005793098863967893 50000000000000000000 2500065865731167 2500000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500065865731167/2500000000000000 : ℝ)) (X := (50005793098863967893/50000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016613347731684453/50000000000000000000 : ℝ) ≤ (10000755491225303/10000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (50016613347731684453/50000000000000000000 : ℝ)^1024 ≤ (10000755491225303/10000000000000000 : ℝ)^4503 := by
      have hnat : (50016613347731684453 : ℕ)^1024*10000000000000000^4503 ≤ 10000755491225303^4503*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016613347731684453 50000000000000000000 10000755491225303 10000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000755491225303/10000000000000000 : ℝ)) (X := (50016613347731684453/50000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027433596599401013/50000000000000000000 : ℝ) ≤ (5000623759762969/5000000000000000 : ℝ) ^ (4503/1024 : ℝ) := by
    have hpowers : (50027433596599401013/50000000000000000000 : ℝ)^1024 ≤ (5000623759762969/5000000000000000 : ℝ)^4503 := by
      have hnat : (50027433596599401013 : ℕ)^1024*5000000000000000^4503 ≤ 5000623759762969^4503*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027433596599401013 50000000000000000000 5000623759762969 5000000000000000 1024 4503 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000623759762969/5000000000000000 : ℝ)) (X := (50027433596599401013/50000000000000000000 : ℝ)) (by norm_num) 4503 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5793098863967893/100000000000000000000 : ℝ) ≤ ((240263088637182321/240312500000000000 : ℝ)+2*(32801886709/30760000000000 : ℝ)*(2719/25000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (240263088637182321/240312500000000000 : ℝ)+2*(32801886709/30760000000000 : ℝ)*(2719/25000 : ℝ)=(2500065865731167/2500000000000000 : ℝ) by norm_num, show 1+2*(5793098863967893/100000000000000000000 : ℝ)=(50005793098863967893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27433596599401013/100000000000000000000 : ℝ)+(5793098863967893/100000000000000000000 : ℝ) ≤ ((240263088637182321/240312500000000000 : ℝ)+(32801886709/30760000000000 : ℝ)*((1549/10000 : ℝ)+(2719/25000 : ℝ)))^(4503/1024 : ℝ) := by
    rw [show (240263088637182321/240312500000000000 : ℝ)+(32801886709/30760000000000 : ℝ)*((1549/10000 : ℝ)+(2719/25000 : ℝ))=(10000755491225303/10000000000000000 : ℝ) by norm_num, show 1+(27433596599401013/100000000000000000000 : ℝ)+(5793098863967893/100000000000000000000 : ℝ)=(50016613347731684453/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27433596599401013/100000000000000000000 : ℝ) ≤ ((240263088637182321/240312500000000000 : ℝ)+2*(32801886709/30760000000000 : ℝ)*(1549/10000 : ℝ))^(4503/1024 : ℝ) := by
    rw [show (240263088637182321/240312500000000000 : ℝ)+2*(32801886709/30760000000000 : ℝ)*(1549/10000 : ℝ)=(5000623759762969/5000000000000000 : ℝ) by norm_num, show 1+2*(27433596599401013/100000000000000000000 : ℝ)=(50027433596599401013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (240263088637182321/240312500000000000 : ℝ)*(X 1 0+X 2 0)+(32801886709/30760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (240263088637182321/240312500000000000 : ℝ)) (alpha := (32801886709/30760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (240263088637182321/240312500000000000 : ℝ)*(X 0 1+X 2 1)+(32801886709/30760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (240263088637182321/240312500000000000 : ℝ)) (alpha := (32801886709/30760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (240263088637182321/240312500000000000 : ℝ)*(X 0 2+X 1 2)+(32801886709/30760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4503/1024 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (240263088637182321/240312500000000000 : ℝ)) (alpha := (32801886709/30760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-939946711/5000000000 : ℝ)*X 0 0+(2717162609/5000000000 : ℝ)*X 0 1+(208687113/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107040893/200000000 : ℝ)*X 1 0+(-398225027/2000000000 : ℝ)*X 1 1+(5217177793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669005577/1250000000 : ℝ)*X 2 0+(163036807/312500000 : ℝ)*X 2 1+(-1991125141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273507709/10000000000 : ℝ)*X 0 0+(2017344037/5000000000 : ℝ)*X 0 1+(1131078477/2500000000 : ℝ)*X 0 2+(4273507709/10000000000 : ℝ)*X 1 0+(2017344037/5000000000 : ℝ)*X 1 1+(1131078477/2500000000 : ℝ)*X 1 2+(4273507709/10000000000 : ℝ)*X 2 0+(2017344037/5000000000 : ℝ)*X 2 1+(1131078477/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1879922891/10000000000 : ℝ)*X 0 0+(260914713/500000000 : ℝ)*X 0 1+(5433200463/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647555361/5000000000 : ℝ)*X 1 0+(-887551221/5000000000 : ℝ)*X 1 1+(1086640097/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295110839/10000000000 : ℝ)*X 2 0+(5433200517/10000000000 : ℝ)*X 2 1+(-355020447/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((854714767/2000000000 : ℝ)*X 0 0+(4521796377/10000000000 : ℝ)*X 0 1+(4037224173/10000000000 : ℝ)*X 0 2+(854714767/2000000000 : ℝ)*X 1 0+(4521796377/10000000000 : ℝ)*X 1 1+(4037224173/10000000000 : ℝ)*X 1 2+(854714767/2000000000 : ℝ)*X 2 0+(4521796377/10000000000 : ℝ)*X 2 1+(4037224173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1504_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21794603715647497312134891/6007812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (330535009/50000000000000 : ℝ)*(base19) + (582547847/100000000000000 : ℝ)*(base23) + (3295973/12500000000000 : ℝ)*(lower2) + (97054661/100000000000000 : ℝ)*(upper3) + (12782841/25000000000000 : ℝ)*(upper5) + (3323786105103413/100000000000000 : ℝ)*(major0) + (3323786105103413/100000000000000 : ℝ)*(major1) + (3323786105103413/100000000000000 : ℝ)*(major2) + (4605177367894753/100000000000000 : ℝ)*(sp0) + (2302593084091951/50000000000000 : ℝ)*(sp1) + (4605186246706073/100000000000000 : ℝ)*(sp2) + (510595067431013/25000000000000 : ℝ)*(sp3) + (4730679583/50000000000000 : ℝ)*(sp4) + (311894073/6250000000000 : ℝ)*(sp7) + (102119263001461/5000000000000 : ℝ)*(f.failure) + (28782417682837/625000000000 : ℝ)*(f.sum) + (3354489449729/1538000000000000000000000000 : ℝ)*base65 + (483437943813511229/48062500000000000000000000000000 : ℝ)*base68 + (63688275012573729/48062500000000000000000000000000 : ℝ)*base70 + (429825183910386229/48062500000000000000000000000000 : ℝ)*base72 + (1242940997783/307600000000000000000000000 : ℝ)*base74 + (690833834644261229/48062500000000000000000000000000 : ℝ)*base76 + (84684943016136229/48062500000000000000000000000000 : ℝ)*base78 + (462663256839886229/48062500000000000000000000000000 : ℝ)*base80 + (2695075777811/1538000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (342011/62500000000000000000 : ℝ)*base89 + (342011/62500000000000000000 : ℝ)*base91 + (342011/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31356600711706145270548563/3003906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (25074801/1250000000000 : ℝ)*(base19) + (270784091/12500000000000 : ℝ)*(base23) + (343062951/50000000000000 : ℝ)*(lower1) + (60050941/25000000000000 : ℝ)*(upper3) + (2849203/100000000000000 : ℝ)*(lower4) + (61008051/25000000000000 : ℝ)*(upper5) + (1679206076571509/50000000000000 : ℝ)*(major0) + (1679206076571509/50000000000000 : ℝ)*(major1) + (1679206076571509/50000000000000 : ℝ)*(major2) + (605603653/12500000000000 : ℝ)*(sp2) + (465316183875421/10000000000000 : ℝ)*(sp4) + (465315983277013/10000000000000 : ℝ)*(sp5) + (4653154827652257/100000000000000 : ℝ)*(sp6) + (412732423915641/20000000000000 : ℝ)*(sp7) + (412732423915641/20000000000000 : ℝ)*(f.failure) + (465316183875421/10000000000000 : ℝ)*(f.sum) + (48016180069/48062500000000000000000000 : ℝ)*base66 + (626290383677830847/24031250000000000000000000000000 : ℝ)*base68 + (212879607830643347/24031250000000000000000000000000 : ℝ)*base70 + (245846910345018347/24031250000000000000000000000000 : ℝ)*base72 + (185126850693/96125000000000000000000000 : ℝ)*base74 + (791896086817518347/24031250000000000000000000000000 : ℝ)*base76 + (110979636202612097/24031250000000000000000000000000 : ℝ)*base78 + (86902028671737097/24031250000000000000000000000000 : ℝ)*base80 + (3072212154147/769000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1740191/250000000000000000000 : ℝ)*base89 + (1740191/250000000000000000000 : ℝ)*base91 + (1740191/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1504_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1504_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1504_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1504_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1504_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1504_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4503/1024 : ℝ) ≤ p) (hpb : p ≤ (4505/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20342551/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5191/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2721/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1504_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

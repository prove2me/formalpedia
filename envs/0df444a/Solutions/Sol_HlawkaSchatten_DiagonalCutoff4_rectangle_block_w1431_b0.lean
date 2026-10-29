-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1431_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:54:22.939727+00:00
-- url     : https://prove2.me/submissions/f26f4ae0-f934-4d31-b9c5-f46fa8cc6dac

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
theorem support_rectangle_w1431_s0_0 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-351536429/2000000000 : ℝ)*x 0 + (2979677959/5000000000 : ℝ)*x 1 + (4831695373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351536429/2000000000 : ℝ)^4391 ≤ (10358701715131/100000000000000 : ℝ)^3367 := by
    have hnat : (351536429 : ℕ)^4391*100000000000000^3367 ≤ 10358701715131^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351536429 2000000000 10358701715131 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2979677959/5000000000 : ℝ)^4391 ≤ (50913279902859/100000000000000 : ℝ)^3367 := by
    have hnat : (2979677959 : ℕ)^4391*100000000000000^3367 ≤ 50913279902859^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979677959 5000000000 50913279902859 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4831695373/10000000000 : ℝ)^4391 ≤ (38728018371629/100000000000000 : ℝ)^3367 := by
    have hnat : (4831695373 : ℕ)^4391*100000000000000^3367 ≤ 38728018371629^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4831695373 10000000000 38728018371629 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351536429/2000000000 : ℝ), (2979677959/5000000000 : ℝ), (4831695373/10000000000 : ℝ)] ![(10358701715131/100000000000000 : ℝ), (50913279902859/100000000000000 : ℝ), (38728018371629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351536429/2000000000 : ℝ)|^4391 ≤ (10358701715131/100000000000000 : ℝ)^3367
        have hw : |(-351536429/2000000000 : ℝ)|=(351536429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2979677959/5000000000 : ℝ)|^4391 ≤ (50913279902859/100000000000000 : ℝ)^3367
        have hw : |(2979677959/5000000000 : ℝ)|=(2979677959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4831695373/10000000000 : ℝ)|^4391 ≤ (38728018371629/100000000000000 : ℝ)^3367
        have hw : |(4831695373/10000000000 : ℝ)|=(4831695373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s0_1 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1372969163/2500000000 : ℝ)*x 0 + (-598651379/2500000000 : ℝ)*x 1 + (4831695817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1372969163/2500000000 : ℝ)^4391 ≤ (11442014757577/25000000000000 : ℝ)^3367 := by
    have hnat : (1372969163 : ℕ)^4391*25000000000000^3367 ≤ 11442014757577^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372969163 2500000000 11442014757577 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598651379/2500000000 : ℝ)^4391 ≤ (15503917945657/100000000000000 : ℝ)^3367 := by
    have hnat : (598651379 : ℕ)^4391*100000000000000^3367 ≤ 15503917945657^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598651379 2500000000 15503917945657 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4831695817/10000000000 : ℝ)^4391 ≤ (2420501438301/6250000000000 : ℝ)^3367 := by
    have hnat : (4831695817 : ℕ)^4391*6250000000000^3367 ≤ 2420501438301^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4831695817 10000000000 2420501438301 6250000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1372969163/2500000000 : ℝ), (-598651379/2500000000 : ℝ), (4831695817/10000000000 : ℝ)] ![(11442014757577/25000000000000 : ℝ), (15503917945657/100000000000000 : ℝ), (2420501438301/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1372969163/2500000000 : ℝ)|^4391 ≤ (11442014757577/25000000000000 : ℝ)^3367
        have hw : |(1372969163/2500000000 : ℝ)|=(1372969163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-598651379/2500000000 : ℝ)|^4391 ≤ (15503917945657/100000000000000 : ℝ)^3367
        have hw : |(-598651379/2500000000 : ℝ)|=(598651379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4831695817/10000000000 : ℝ)|^4391 ≤ (2420501438301/6250000000000 : ℝ)^3367
        have hw : |(4831695817/10000000000 : ℝ)|=(4831695817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s0_2 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5491877263/10000000000 : ℝ)*x 0 + (2415847809/5000000000 : ℝ)*x 1 + (-149662811/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5491877263/10000000000 : ℝ)^4391 ≤ (22884032835423/50000000000000 : ℝ)^3367 := by
    have hnat : (5491877263 : ℕ)^4391*50000000000000^3367 ≤ 22884032835423^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491877263 10000000000 22884032835423 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2415847809/5000000000 : ℝ)^4391 ≤ (9682005233161/25000000000000 : ℝ)^3367 := by
    have hnat : (2415847809 : ℕ)^4391*25000000000000^3367 ≤ 9682005233161^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415847809 5000000000 9682005233161 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149662811/625000000 : ℝ)^4391 ≤ (15503913386111/100000000000000 : ℝ)^3367 := by
    have hnat : (149662811 : ℕ)^4391*100000000000000^3367 ≤ 15503913386111^3367*625000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149662811 625000000 15503913386111 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5491877263/10000000000 : ℝ), (2415847809/5000000000 : ℝ), (-149662811/625000000 : ℝ)] ![(22884032835423/50000000000000 : ℝ), (9682005233161/25000000000000 : ℝ), (15503913386111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5491877263/10000000000 : ℝ)|^4391 ≤ (22884032835423/50000000000000 : ℝ)^3367
        have hw : |(5491877263/10000000000 : ℝ)|=(5491877263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2415847809/5000000000 : ℝ)|^4391 ≤ (9682005233161/25000000000000 : ℝ)^3367
        have hw : |(2415847809/5000000000 : ℝ)|=(2415847809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-149662811/625000000 : ℝ)|^4391 ≤ (15503913386111/100000000000000 : ℝ)^3367
        have hw : |(-149662811/625000000 : ℝ)|=(149662811/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s0_3 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2082856879/5000000000 : ℝ)*x 0 + (3103308091/10000000000 : ℝ)*x 1 + (2772301863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082856879/5000000000 : ℝ)^4391 ≤ (3989663130121/12500000000000 : ℝ)^3367 := by
    have hnat : (2082856879 : ℕ)^4391*12500000000000^3367 ≤ 3989663130121^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082856879 5000000000 3989663130121 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103308091/10000000000 : ℝ)^4391 ≤ (543518672903/2500000000000 : ℝ)^3367 := by
    have hnat : (3103308091 : ℕ)^4391*2500000000000^3367 ≤ 543518672903^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103308091 10000000000 543518672903 2500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2772301863/5000000000 : ℝ)^4391 ≤ (46341948025587/100000000000000 : ℝ)^3367 := by
    have hnat : (2772301863 : ℕ)^4391*100000000000000^3367 ≤ 46341948025587^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772301863 5000000000 46341948025587 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082856879/5000000000 : ℝ), (3103308091/10000000000 : ℝ), (2772301863/5000000000 : ℝ)] ![(3989663130121/12500000000000 : ℝ), (543518672903/2500000000000 : ℝ), (46341948025587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082856879/5000000000 : ℝ)|^4391 ≤ (3989663130121/12500000000000 : ℝ)^3367
        have hw : |(2082856879/5000000000 : ℝ)|=(2082856879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103308091/10000000000 : ℝ)|^4391 ≤ (543518672903/2500000000000 : ℝ)^3367
        have hw : |(3103308091/10000000000 : ℝ)|=(3103308091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2772301863/5000000000 : ℝ)|^4391 ≤ (46341948025587/100000000000000 : ℝ)^3367
        have hw : |(2772301863/5000000000 : ℝ)|=(2772301863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s0_4 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-68816/390625 : ℝ)*x 0 + (4860543191/10000000000 : ℝ)*x 1 + (2964739139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68816/390625 : ℝ)^4391 ≤ (10389512618093/100000000000000 : ℝ)^3367 := by
    have hnat : (68816 : ℕ)^4391*100000000000000^3367 ≤ 10389512618093^3367*390625^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68816 390625 10389512618093 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4860543191/10000000000 : ℝ)^4391 ≤ (4878730194387/12500000000000 : ℝ)^3367 := by
    have hnat : (4860543191 : ℕ)^4391*12500000000000^3367 ≤ 4878730194387^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4860543191 10000000000 4878730194387 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2964739139/5000000000 : ℝ)^4391 ≤ (25290322908339/50000000000000 : ℝ)^3367 := by
    have hnat : (2964739139 : ℕ)^4391*50000000000000^3367 ≤ 25290322908339^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2964739139 5000000000 25290322908339 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68816/390625 : ℝ), (4860543191/10000000000 : ℝ), (2964739139/5000000000 : ℝ)] ![(10389512618093/100000000000000 : ℝ), (4878730194387/12500000000000 : ℝ), (25290322908339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68816/390625 : ℝ)|^4391 ≤ (10389512618093/100000000000000 : ℝ)^3367
        have hw : |(-68816/390625 : ℝ)|=(68816/390625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4860543191/10000000000 : ℝ)|^4391 ≤ (4878730194387/12500000000000 : ℝ)^3367
        have hw : |(4860543191/10000000000 : ℝ)|=(4860543191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2964739139/5000000000 : ℝ)|^4391 ≤ (25290322908339/50000000000000 : ℝ)^3367
        have hw : |(2964739139/5000000000 : ℝ)|=(2964739139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s0_5 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036816911/2000000000 : ℝ)*x 0 + (-1296822313/10000000000 : ℝ)*x 1 + (118589567/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036816911/2000000000 : ℝ)^4391 ≤ (21225883845807/50000000000000 : ℝ)^3367 := by
    have hnat : (1036816911 : ℕ)^4391*50000000000000^3367 ≤ 21225883845807^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036816911 2000000000 21225883845807 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296822313/10000000000 : ℝ)^4391 ≤ (6967585672323/100000000000000 : ℝ)^3367 := by
    have hnat : (1296822313 : ℕ)^4391*100000000000000^3367 ≤ 6967585672323^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296822313 10000000000 6967585672323 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118589567/200000000 : ℝ)^4391 ≤ (6322580827207/12500000000000 : ℝ)^3367 := by
    have hnat : (118589567 : ℕ)^4391*12500000000000^3367 ≤ 6322580827207^3367*200000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118589567 200000000 6322580827207 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036816911/2000000000 : ℝ), (-1296822313/10000000000 : ℝ), (118589567/200000000 : ℝ)] ![(21225883845807/50000000000000 : ℝ), (6967585672323/100000000000000 : ℝ), (6322580827207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036816911/2000000000 : ℝ)|^4391 ≤ (21225883845807/50000000000000 : ℝ)^3367
        have hw : |(1036816911/2000000000 : ℝ)|=(1036816911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1296822313/10000000000 : ℝ)|^4391 ≤ (6967585672323/100000000000000 : ℝ)^3367
        have hw : |(-1296822313/10000000000 : ℝ)|=(1296822313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118589567/200000000 : ℝ)|^4391 ≤ (6322580827207/12500000000000 : ℝ)^3367
        have hw : |(118589567/200000000 : ℝ)|=(118589567/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s0_6 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184084577/10000000000 : ℝ)*x 0 + (5929478191/10000000000 : ℝ)*x 1 + (-1296822533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184084577/10000000000 : ℝ)^4391 ≤ (42451767926559/100000000000000 : ℝ)^3367 := by
    have hnat : (5184084577 : ℕ)^4391*100000000000000^3367 ≤ 42451767926559^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184084577 10000000000 42451767926559 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5929478191/10000000000 : ℝ)^4391 ≤ (50580644848829/100000000000000 : ℝ)^3367 := by
    have hnat : (5929478191 : ℕ)^4391*100000000000000^3367 ≤ 50580644848829^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5929478191 10000000000 50580644848829 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296822533/10000000000 : ℝ)^4391 ≤ (1741896803457/25000000000000 : ℝ)^3367 := by
    have hnat : (1296822533 : ℕ)^4391*25000000000000^3367 ≤ 1741896803457^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296822533 10000000000 1741896803457 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184084577/10000000000 : ℝ), (5929478191/10000000000 : ℝ), (-1296822533/10000000000 : ℝ)] ![(42451767926559/100000000000000 : ℝ), (50580644848829/100000000000000 : ℝ), (1741896803457/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184084577/10000000000 : ℝ)|^4391 ≤ (42451767926559/100000000000000 : ℝ)^3367
        have hw : |(5184084577/10000000000 : ℝ)|=(5184084577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5929478191/10000000000 : ℝ)|^4391 ≤ (50580644848829/100000000000000 : ℝ)^3367
        have hw : |(5929478191/10000000000 : ℝ)|=(5929478191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1296822533/10000000000 : ℝ)|^4391 ≤ (1741896803457/25000000000000 : ℝ)^3367
        have hw : |(-1296822533/10000000000 : ℝ)|=(1296822533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s0_7 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (417439199/1000000000 : ℝ)*x 0 + (5482150099/10000000000 : ℝ)*x 1 + (3167991491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417439199/1000000000 : ℝ)^4391 ≤ (1600202316359/5000000000000 : ℝ)^3367 := by
    have hnat : (417439199 : ℕ)^4391*5000000000000^3367 ≤ 1600202316359^3367*1000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417439199 1000000000 1600202316359 5000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482150099/10000000000 : ℝ)^4391 ≤ (4566237631289/10000000000000 : ℝ)^3367 := by
    have hnat : (5482150099 : ℕ)^4391*10000000000000^3367 ≤ 4566237631289^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482150099 10000000000 4566237631289 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167991491/10000000000 : ℝ)^4391 ≤ (2233357734021/10000000000000 : ℝ)^3367 := by
    have hnat : (3167991491 : ℕ)^4391*10000000000000^3367 ≤ 2233357734021^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167991491 10000000000 2233357734021 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417439199/1000000000 : ℝ), (5482150099/10000000000 : ℝ), (3167991491/10000000000 : ℝ)] ![(1600202316359/5000000000000 : ℝ), (4566237631289/10000000000000 : ℝ), (2233357734021/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417439199/1000000000 : ℝ)|^4391 ≤ (1600202316359/5000000000000 : ℝ)^3367
        have hw : |(417439199/1000000000 : ℝ)|=(417439199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482150099/10000000000 : ℝ)|^4391 ≤ (4566237631289/10000000000000 : ℝ)^3367
        have hw : |(5482150099/10000000000 : ℝ)|=(5482150099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167991491/10000000000 : ℝ)|^4391 ≤ (2233357734021/10000000000000 : ℝ)^3367
        have hw : |(3167991491/10000000000 : ℝ)|=(3167991491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1431_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1031/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6561/25000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2195/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2195 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2195*1^512 ≤ 0^512*1^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2195/512 : ℝ) ≤ (491957591681060159/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2195 ≤ (491957591681060159/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2195*25000000000000000000^512 ≤ 491957591681060159^512*5^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 491957591681060159 25000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (491957591681060159/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2195 := by
      have hnat : (1 : ℕ)^512*1^2195 ≤ 1^2195*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25491957591681060159/25000000000000000000 : ℝ) ≤ (10045558776965533/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (25491957591681060159/25000000000000000000 : ℝ)^512 ≤ (10045558776965533/10000000000000000 : ℝ)^2195 := by
      have hnat : (25491957591681060159 : ℕ)^512*10000000000000000^2195 ≤ 10045558776965533^2195*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25491957591681060159 25000000000000000000 10045558776965533 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045558776965533/10000000000000000 : ℝ)) (X := (25491957591681060159/25000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12991957591681060159/12500000000000000000 : ℝ) ≤ (5045558776965533/5000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (12991957591681060159/12500000000000000000 : ℝ)^512 ≤ (5045558776965533/5000000000000000 : ℝ)^2195 := by
      have hnat : (12991957591681060159 : ℕ)^512*5000000000000000^2195 ≤ 5045558776965533^2195*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12991957591681060159 12500000000000000000 5045558776965533 5000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045558776965533/5000000000000000 : ℝ)) (X := (12991957591681060159/12500000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45558776965533/4000000000000000 : ℝ)*(0 : ℝ))^(2195/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(45558776965533/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(491957591681060159/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45558776965533/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2195/512 : ℝ) := by
    rw [show (1 : ℝ)+(45558776965533/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10045558776965533/10000000000000000 : ℝ) by norm_num, show 1+(491957591681060159/25000000000000000000 : ℝ)+(0 : ℝ)=(25491957591681060159/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(491957591681060159/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45558776965533/4000000000000000 : ℝ)*(2/5 : ℝ))^(2195/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(45558776965533/4000000000000000 : ℝ)*(2/5 : ℝ)=(5045558776965533/5000000000000000 : ℝ) by norm_num, show 1+2*(491957591681060159/25000000000000000000 : ℝ)=(12991957591681060159/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45558776965533/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45558776965533/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45558776965533/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45558776965533/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45558776965533/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45558776965533/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-351536429/2000000000 : ℝ)*X 0 0+(2979677959/5000000000 : ℝ)*X 0 1+(4831695373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1372969163/2500000000 : ℝ)*X 1 0+(-598651379/2500000000 : ℝ)*X 1 1+(4831695817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5491877263/10000000000 : ℝ)*X 2 0+(2415847809/5000000000 : ℝ)*X 2 1+(-149662811/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2082856879/5000000000 : ℝ)*X 0 0+(3103308091/10000000000 : ℝ)*X 0 1+(2772301863/5000000000 : ℝ)*X 0 2+(2082856879/5000000000 : ℝ)*X 1 0+(3103308091/10000000000 : ℝ)*X 1 1+(2772301863/5000000000 : ℝ)*X 1 2+(2082856879/5000000000 : ℝ)*X 2 0+(3103308091/10000000000 : ℝ)*X 2 1+(2772301863/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-68816/390625 : ℝ)*X 0 0+(4860543191/10000000000 : ℝ)*X 0 1+(2964739139/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1036816911/2000000000 : ℝ)*X 1 0+(-1296822313/10000000000 : ℝ)*X 1 1+(118589567/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5184084577/10000000000 : ℝ)*X 2 0+(5929478191/10000000000 : ℝ)*X 2 1+(-1296822533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((417439199/1000000000 : ℝ)*X 0 0+(5482150099/10000000000 : ℝ)*X 0 1+(3167991491/10000000000 : ℝ)*X 0 2+(417439199/1000000000 : ℝ)*X 1 0+(5482150099/10000000000 : ℝ)*X 1 1+(3167991491/10000000000 : ℝ)*X 1 2+(417439199/1000000000 : ℝ)*X 2 0+(5482150099/10000000000 : ℝ)*X 2 1+(3167991491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (573617636794653007791411/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40706889/5000000000000 : ℝ)*(base19) + (404129619/50000000000000 : ℝ)*(base23) + (14735027/20000000000000 : ℝ)*(upper3) + (5741171/10000000000000 : ℝ)*(upper4) + (77469707/50000000000000 : ℝ)*(upper5) + (648209629248663/100000000000000 : ℝ)*(major0) + (648209629248663/100000000000000 : ℝ)*(major1) + (648209629248663/100000000000000 : ℝ)*(major2) + (88679412264399/10000000000000 : ℝ)*(sp0) + (55424801810257/6250000000000 : ℝ)*(sp1) + (177359366968531/20000000000000 : ℝ)*(sp2) + (81924014588783/20000000000000 : ℝ)*(sp3) + (3520457903/100000000000000 : ℝ)*(sp4) + (144684857/10000000000000 : ℝ)*(sp7) + (102405379948121/25000000000000 : ℝ)*(f.failure) + (886797643101893/100000000000000 : ℝ)*(f.sum) + (378400066667621/200000000000000000000000000000 : ℝ)*base66 + (2171984557867621/400000000000000000000000000000 : ℝ)*base68 + (1680019948267621/400000000000000000000000000000 : ℝ)*base70 + (406853879732379/400000000000000000000000000000 : ℝ)*base71 + (1668322743267621/200000000000000000000000000000 : ℝ)*base74 + (2747047971732379/400000000000000000000000000000 : ℝ)*base75 + (751517783332379/400000000000000000000000000000 : ℝ)*base77 + (828210356667621/400000000000000000000000000000 : ℝ)*base80 + (1242824938667621/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1871521/250000000000000000000 : ℝ)*base90 + (1871521/250000000000000000000 : ℝ)*base92 + (1871521/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (721686342459966266011653/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (409702523/50000000000000 : ℝ)*(base19) + (412826159/50000000000000 : ℝ)*(base23) + (28355143/25000000000000 : ℝ)*(base32) + (128354627/100000000000000 : ℝ)*(upper3) + (60816847/100000000000000 : ℝ)*(upper5) + (683816227771453/100000000000000 : ℝ)*(major0) + (683816227771453/100000000000000 : ℝ)*(major1) + (683816227771453/100000000000000 : ℝ)*(major2) + (1930451953/100000000000000 : ℝ)*(sp1) + (1968802599/100000000000000 : ℝ)*(sp2) + (935510025071581/100000000000000 : ℝ)*(sp4) + (467753637607291/50000000000000 : ℝ)*(sp5) + (116938403827083/12500000000000 : ℝ)*(sp6) + (432122196769691/100000000000000 : ℝ)*(sp7) + (432122310190263/100000000000000 : ℝ)*(f.failure) + (935510025071581/100000000000000 : ℝ)*(f.sum) + (43886884329449/200000000000000000000000000000 : ℝ)*base65 + (2415068630329449/400000000000000000000000000000 : ℝ)*base67 + (2543456337270551/400000000000000000000000000000 : ℝ)*base70 + (8007399929449/400000000000000000000000000000 : ℝ)*base71 + (1306568683329449/200000000000000000000000000000 : ℝ)*base73 + (1290761450470551/400000000000000000000000000000 : ℝ)*base76 + (583798719670551/400000000000000000000000000000 : ℝ)*base78 + (556136216329449/400000000000000000000000000000 : ℝ)*base79 + (477144966670551/200000000000000000000000000000 : ℝ)*base82 + (4320463/1000000000000000000000 : ℝ)*base90 + (4320463/1000000000000000000000 : ℝ)*base92 + (4320463/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1431_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1031/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6561/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1431_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1431_s1_0 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1929756183/10000000000 : ℝ)*x 0 + (5604418749/10000000000 : ℝ)*x 1 + (253815809/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1929756183/10000000000 : ℝ)^4391 ≤ (1170047546347/10000000000000 : ℝ)^3367 := by
    have hnat : (1929756183 : ℕ)^4391*10000000000000^3367 ≤ 1170047546347^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929756183 10000000000 1170047546347 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5604418749/10000000000 : ℝ)^4391 ≤ (46994995052939/100000000000000 : ℝ)^3367 := by
    have hnat : (5604418749 : ℕ)^4391*100000000000000^3367 ≤ 46994995052939^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604418749 10000000000 46994995052939 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253815809/500000000 : ℝ)^4391 ≤ (10326132366153/25000000000000 : ℝ)^3367 := by
    have hnat : (253815809 : ℕ)^4391*25000000000000^3367 ≤ 10326132366153^3367*500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253815809 500000000 10326132366153 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1929756183/10000000000 : ℝ), (5604418749/10000000000 : ℝ), (253815809/500000000 : ℝ)] ![(1170047546347/10000000000000 : ℝ), (46994995052939/100000000000000 : ℝ), (10326132366153/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1929756183/10000000000 : ℝ)|^4391 ≤ (1170047546347/10000000000000 : ℝ)^3367
        have hw : |(-1929756183/10000000000 : ℝ)|=(1929756183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5604418749/10000000000 : ℝ)|^4391 ≤ (46994995052939/100000000000000 : ℝ)^3367
        have hw : |(5604418749/10000000000 : ℝ)|=(5604418749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(253815809/500000000 : ℝ)|^4391 ≤ (10326132366153/25000000000000 : ℝ)^3367
        have hw : |(253815809/500000000 : ℝ)|=(253815809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s1_1 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698303811/5000000000 : ℝ)*x 0 + (-2209547763/10000000000 : ℝ)*x 1 + (2538158829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698303811/5000000000 : ℝ)^4391 ≤ (11183847001961/25000000000000 : ℝ)^3367 := by
    have hnat : (2698303811 : ℕ)^4391*25000000000000^3367 ≤ 11183847001961^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698303811 5000000000 11183847001961 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209547763/10000000000 : ℝ)^4391 ≤ (698003341211/5000000000000 : ℝ)^3367 := by
    have hnat : (2209547763 : ℕ)^4391*5000000000000^3367 ≤ 698003341211^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209547763 10000000000 698003341211 5000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2538158829/5000000000 : ℝ)^4391 ≤ (41304545148141/100000000000000 : ℝ)^3367 := by
    have hnat : (2538158829 : ℕ)^4391*100000000000000^3367 ≤ 41304545148141^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538158829 5000000000 41304545148141 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698303811/5000000000 : ℝ), (-2209547763/10000000000 : ℝ), (2538158829/5000000000 : ℝ)] ![(11183847001961/25000000000000 : ℝ), (698003341211/5000000000000 : ℝ), (41304545148141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698303811/5000000000 : ℝ)|^4391 ≤ (11183847001961/25000000000000 : ℝ)^3367
        have hw : |(2698303811/5000000000 : ℝ)|=(2698303811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2209547763/10000000000 : ℝ)|^4391 ≤ (698003341211/5000000000000 : ℝ)^3367
        have hw : |(-2209547763/10000000000 : ℝ)|=(2209547763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2538158829/5000000000 : ℝ)|^4391 ≤ (41304545148141/100000000000000 : ℝ)^3367
        have hw : |(2538158829/5000000000 : ℝ)|=(2538158829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s1_2 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349152187/2500000000 : ℝ)*x 0 + (5076316403/10000000000 : ℝ)*x 1 + (-2209547903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349152187/2500000000 : ℝ)^4391 ≤ (8947080036121/20000000000000 : ℝ)^3367 := by
    have hnat : (1349152187 : ℕ)^4391*20000000000000^3367 ≤ 8947080036121^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349152187 2500000000 8947080036121 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5076316403/10000000000 : ℝ)^4391 ≤ (5163066478867/12500000000000 : ℝ)^3367 := by
    have hnat : (5076316403 : ℕ)^4391*12500000000000^3367 ≤ 5163066478867^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076316403 10000000000 5163066478867 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209547903/10000000000 : ℝ)^4391 ≤ (13960067977759/100000000000000 : ℝ)^3367 := by
    have hnat : (2209547903 : ℕ)^4391*100000000000000^3367 ≤ 13960067977759^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209547903 10000000000 13960067977759 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349152187/2500000000 : ℝ), (5076316403/10000000000 : ℝ), (-2209547903/10000000000 : ℝ)] ![(8947080036121/20000000000000 : ℝ), (5163066478867/12500000000000 : ℝ), (13960067977759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349152187/2500000000 : ℝ)|^4391 ≤ (8947080036121/20000000000000 : ℝ)^3367
        have hw : |(1349152187/2500000000 : ℝ)|=(1349152187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5076316403/10000000000 : ℝ)|^4391 ≤ (5163066478867/12500000000000 : ℝ)^3367
        have hw : |(5076316403/10000000000 : ℝ)|=(5076316403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2209547903/10000000000 : ℝ)|^4391 ≤ (13960067977759/100000000000000 : ℝ)^3367
        have hw : |(-2209547903/10000000000 : ℝ)|=(2209547903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s1_3 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66816817/156250000 : ℝ)*x 0 + (3738707521/10000000000 : ℝ)*x 1 + (4882004599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66816817/156250000 : ℝ)^4391 ≤ (16513244667977/50000000000000 : ℝ)^3367 := by
    have hnat : (66816817 : ℕ)^4391*50000000000000^3367 ≤ 16513244667977^3367*156250000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66816817 156250000 16513244667977 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3738707521/10000000000 : ℝ)^4391 ≤ (27718773103633/100000000000000 : ℝ)^3367 := by
    have hnat : (3738707521 : ℕ)^4391*100000000000000^3367 ≤ 27718773103633^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3738707521 10000000000 27718773103633 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4882004599/10000000000 : ℝ)^4391 ≤ (7850947509401/20000000000000 : ℝ)^3367 := by
    have hnat : (4882004599 : ℕ)^4391*20000000000000^3367 ≤ 7850947509401^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4882004599 10000000000 7850947509401 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66816817/156250000 : ℝ), (3738707521/10000000000 : ℝ), (4882004599/10000000000 : ℝ)] ![(16513244667977/50000000000000 : ℝ), (27718773103633/100000000000000 : ℝ), (7850947509401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66816817/156250000 : ℝ)|^4391 ≤ (16513244667977/50000000000000 : ℝ)^3367
        have hw : |(66816817/156250000 : ℝ)|=(66816817/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3738707521/10000000000 : ℝ)|^4391 ≤ (27718773103633/100000000000000 : ℝ)^3367
        have hw : |(3738707521/10000000000 : ℝ)|=(3738707521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4882004599/10000000000 : ℝ)|^4391 ≤ (7850947509401/20000000000000 : ℝ)^3367
        have hw : |(4882004599/10000000000 : ℝ)|=(4882004599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s1_4 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-241268921/1250000000 : ℝ)*x 0 + (5082499087/10000000000 : ℝ)*x 1 + (174941601/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241268921/1250000000 : ℝ)^4391 ≤ (11703600358007/100000000000000 : ℝ)^3367 := by
    have hnat : (241268921 : ℕ)^4391*100000000000000^3367 ≤ 11703600358007^3367*1250000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241268921 1250000000 11703600358007 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082499087/10000000000 : ℝ)^4391 ≤ (41370150405971/100000000000000 : ℝ)^3367 := by
    have hnat : (5082499087 : ℕ)^4391*100000000000000^3367 ≤ 41370150405971^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082499087 10000000000 41370150405971 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174941601/312500000 : ℝ)^4391 ≤ (5865781151907/12500000000000 : ℝ)^3367 := by
    have hnat : (174941601 : ℕ)^4391*12500000000000^3367 ≤ 5865781151907^3367*312500000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174941601 312500000 5865781151907 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-241268921/1250000000 : ℝ), (5082499087/10000000000 : ℝ), (174941601/312500000 : ℝ)] ![(11703600358007/100000000000000 : ℝ), (41370150405971/100000000000000 : ℝ), (5865781151907/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-241268921/1250000000 : ℝ)|^4391 ≤ (11703600358007/100000000000000 : ℝ)^3367
        have hw : |(-241268921/1250000000 : ℝ)|=(241268921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082499087/10000000000 : ℝ)|^4391 ≤ (41370150405971/100000000000000 : ℝ)^3367
        have hw : |(5082499087/10000000000 : ℝ)|=(5082499087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(174941601/312500000 : ℝ)|^4391 ≤ (5865781151907/12500000000000 : ℝ)^3367
        have hw : |(174941601/312500000 : ℝ)|=(174941601/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s1_5 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314652213/2500000000 : ℝ)*x 0 + (-84386677/500000000 : ℝ)*x 1 + (5598131249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314652213/2500000000 : ℝ)^4391 ≤ (43249371297109/100000000000000 : ℝ)^3367 := by
    have hnat : (1314652213 : ℕ)^4391*100000000000000^3367 ≤ 43249371297109^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314652213 2500000000 43249371297109 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84386677/500000000 : ℝ)^4391 ≤ (9824379288907/100000000000000 : ℝ)^3367 := by
    have hnat : (84386677 : ℕ)^4391*100000000000000^3367 ≤ 9824379288907^3367*500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84386677 500000000 9824379288907 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5598131249/10000000000 : ℝ)^4391 ≤ (46926249401097/100000000000000 : ℝ)^3367 := by
    have hnat : (5598131249 : ℕ)^4391*100000000000000^3367 ≤ 46926249401097^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598131249 10000000000 46926249401097 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314652213/2500000000 : ℝ), (-84386677/500000000 : ℝ), (5598131249/10000000000 : ℝ)] ![(43249371297109/100000000000000 : ℝ), (9824379288907/100000000000000 : ℝ), (46926249401097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314652213/2500000000 : ℝ)|^4391 ≤ (43249371297109/100000000000000 : ℝ)^3367
        have hw : |(1314652213/2500000000 : ℝ)|=(1314652213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84386677/500000000 : ℝ)|^4391 ≤ (9824379288907/100000000000000 : ℝ)^3367
        have hw : |(-84386677/500000000 : ℝ)|=(84386677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5598131249/10000000000 : ℝ)|^4391 ≤ (46926249401097/100000000000000 : ℝ)^3367
        have hw : |(5598131249/10000000000 : ℝ)|=(5598131249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s1_6 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6573261/12500000 : ℝ)*x 0 + (559813121/1000000000 : ℝ)*x 1 + (-1687733669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6573261/12500000 : ℝ)^4391 ≤ (5406171342421/12500000000000 : ℝ)^3367 := by
    have hnat : (6573261 : ℕ)^4391*12500000000000^3367 ≤ 5406171342421^3367*12500000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6573261 12500000 5406171342421 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559813121/1000000000 : ℝ)^4391 ≤ (9385249794951/20000000000000 : ℝ)^3367 := by
    have hnat : (559813121 : ℕ)^4391*20000000000000^3367 ≤ 9385249794951^3367*1000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559813121 1000000000 9385249794951 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1687733669/10000000000 : ℝ)^4391 ≤ (9824380268197/100000000000000 : ℝ)^3367 := by
    have hnat : (1687733669 : ℕ)^4391*100000000000000^3367 ≤ 9824380268197^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687733669 10000000000 9824380268197 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6573261/12500000 : ℝ), (559813121/1000000000 : ℝ), (-1687733669/10000000000 : ℝ)] ![(5406171342421/12500000000000 : ℝ), (9385249794951/20000000000000 : ℝ), (9824380268197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6573261/12500000 : ℝ)|^4391 ≤ (5406171342421/12500000000000 : ℝ)^3367
        have hw : |(6573261/12500000 : ℝ)|=(6573261/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559813121/1000000000 : ℝ)|^4391 ≤ (9385249794951/20000000000000 : ℝ)^3367
        have hw : |(559813121/1000000000 : ℝ)|=(559813121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1687733669/10000000000 : ℝ)|^4391 ≤ (9824380268197/100000000000000 : ℝ)^3367
        have hw : |(-1687733669/10000000000 : ℝ)|=(1687733669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s1_7 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138566241/5000000000 : ℝ)*x 0 + (4868620249/10000000000 : ℝ)*x 1 + (938079433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138566241/5000000000 : ℝ)^4391 ≤ (6607022641889/20000000000000 : ℝ)^3367 := by
    have hnat : (2138566241 : ℕ)^4391*20000000000000^3367 ≤ 6607022641889^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138566241 5000000000 6607022641889 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4868620249/10000000000 : ℝ)^4391 ≤ (19557223195879/50000000000000 : ℝ)^3367 := by
    have hnat : (4868620249 : ℕ)^4391*50000000000000^3367 ≤ 19557223195879^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4868620249 10000000000 19557223195879 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (938079433/2500000000 : ℝ)^4391 ≤ (27850440374171/100000000000000 : ℝ)^3367 := by
    have hnat : (938079433 : ℕ)^4391*100000000000000^3367 ≤ 27850440374171^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938079433 2500000000 27850440374171 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138566241/5000000000 : ℝ), (4868620249/10000000000 : ℝ), (938079433/2500000000 : ℝ)] ![(6607022641889/20000000000000 : ℝ), (19557223195879/50000000000000 : ℝ), (27850440374171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138566241/5000000000 : ℝ)|^4391 ≤ (6607022641889/20000000000000 : ℝ)^3367
        have hw : |(2138566241/5000000000 : ℝ)|=(2138566241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4868620249/10000000000 : ℝ)|^4391 ≤ (19557223195879/50000000000000 : ℝ)^3367
        have hw : |(4868620249/10000000000 : ℝ)|=(4868620249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(938079433/2500000000 : ℝ)|^4391 ≤ (27850440374171/100000000000000 : ℝ)^3367
        have hw : |(938079433/2500000000 : ℝ)|=(938079433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1431_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6561/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1031/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1917/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18833/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6561/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1031/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6561/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1031/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6561/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1031/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6561/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1031/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6561/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1031/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6561/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1031/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1031/50000 : ℝ) ^ (2195/512 : ℝ) ≤ (5931589869803/100000000000000000000 : ℝ) := by
    have hpowers : (1031/50000 : ℝ)^2195 ≤ (5931589869803/100000000000000000000 : ℝ)^512 := by
      have hnat : (1031 : ℕ)^2195*100000000000000000000^512 ≤ 5931589869803^512*50000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1031 50000 5931589869803 100000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1031/50000 : ℝ)) (X := (5931589869803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hpowhi : (6561/25000 : ℝ) ^ (2195/512 : ℝ) ≤ (323086038365678659/100000000000000000000 : ℝ) := by
    have hpowers : (6561/25000 : ℝ)^2195 ≤ (323086038365678659/100000000000000000000 : ℝ)^512 := by
      have hnat : (6561 : ℕ)^2195*100000000000000000000^512 ≤ 323086038365678659^512*25000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6561 25000 323086038365678659 100000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6561/25000 : ℝ)) (X := (323086038365678659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000005931589869803/50000000000000000000 : ℝ) ≤ (5000000138358719/5000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50000005931589869803/50000000000000000000 : ℝ)^512 ≤ (5000000138358719/5000000000000000 : ℝ)^2195 := by
      have hnat : (50000005931589869803 : ℕ)^512*5000000000000000^2195 ≤ 5000000138358719^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000005931589869803 50000000000000000000 5000000138358719 5000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000138358719/5000000000000000 : ℝ)) (X := (50000005931589869803/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50161545984977774231/50000000000000000000 : ℝ) ≤ (10007527042262087/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50161545984977774231/50000000000000000000 : ℝ)^512 ≤ (10007527042262087/10000000000000000 : ℝ)^2195 := by
      have hnat : (50161545984977774231 : ℕ)^512*10000000000000000^2195 ≤ 10007527042262087^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50161545984977774231 50000000000000000000 10007527042262087 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007527042262087/10000000000000000 : ℝ)) (X := (50161545984977774231/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50323086038365678659/50000000000000000000 : ℝ) ≤ (625940862987921/625000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50323086038365678659/50000000000000000000 : ℝ)^512 ≤ (625940862987921/625000000000000 : ℝ)^2195 := by
      have hnat : (50323086038365678659 : ℕ)^512*625000000000000^2195 ≤ 625940862987921^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50323086038365678659 50000000000000000000 625940862987921 625000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625940862987921/625000000000000 : ℝ)) (X := (50323086038365678659/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5931589869803/100000000000000000000 : ℝ) ≤ ((6044724157761873831/6045500000000000000 : ℝ)+2*(7526765544649/2418200000000000 : ℝ)*(1031/50000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (6044724157761873831/6045500000000000000 : ℝ)+2*(7526765544649/2418200000000000 : ℝ)*(1031/50000 : ℝ)=(5000000138358719/5000000000000000 : ℝ) by norm_num, show 1+2*(5931589869803/100000000000000000000 : ℝ)=(50000005931589869803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(323086038365678659/100000000000000000000 : ℝ)+(5931589869803/100000000000000000000 : ℝ) ≤ ((6044724157761873831/6045500000000000000 : ℝ)+(7526765544649/2418200000000000 : ℝ)*((6561/25000 : ℝ)+(1031/50000 : ℝ)))^(2195/512 : ℝ) := by
    rw [show (6044724157761873831/6045500000000000000 : ℝ)+(7526765544649/2418200000000000 : ℝ)*((6561/25000 : ℝ)+(1031/50000 : ℝ))=(10007527042262087/10000000000000000 : ℝ) by norm_num, show 1+(323086038365678659/100000000000000000000 : ℝ)+(5931589869803/100000000000000000000 : ℝ)=(50161545984977774231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(323086038365678659/100000000000000000000 : ℝ) ≤ ((6044724157761873831/6045500000000000000 : ℝ)+2*(7526765544649/2418200000000000 : ℝ)*(6561/25000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (6044724157761873831/6045500000000000000 : ℝ)+2*(7526765544649/2418200000000000 : ℝ)*(6561/25000 : ℝ)=(625940862987921/625000000000000 : ℝ) by norm_num, show 1+2*(323086038365678659/100000000000000000000 : ℝ)=(50323086038365678659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6044724157761873831/6045500000000000000 : ℝ)*(X 1 0+X 2 0)+(7526765544649/2418200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (1031/50000 : ℝ)) (hi := (6561/25000 : ℝ)) (c := (6044724157761873831/6045500000000000000 : ℝ)) (alpha := (7526765544649/2418200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6044724157761873831/6045500000000000000 : ℝ)*(X 0 1+X 2 1)+(7526765544649/2418200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (1031/50000 : ℝ)) (hi := (6561/25000 : ℝ)) (c := (6044724157761873831/6045500000000000000 : ℝ)) (alpha := (7526765544649/2418200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6044724157761873831/6045500000000000000 : ℝ)*(X 0 2+X 1 2)+(7526765544649/2418200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (1031/50000 : ℝ)) (hi := (6561/25000 : ℝ)) (c := (6044724157761873831/6045500000000000000 : ℝ)) (alpha := (7526765544649/2418200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1929756183/10000000000 : ℝ)*X 0 0+(5604418749/10000000000 : ℝ)*X 0 1+(253815809/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2698303811/5000000000 : ℝ)*X 1 0+(-2209547763/10000000000 : ℝ)*X 1 1+(2538158829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1349152187/2500000000 : ℝ)*X 2 0+(5076316403/10000000000 : ℝ)*X 2 1+(-2209547903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((66816817/156250000 : ℝ)*X 0 0+(3738707521/10000000000 : ℝ)*X 0 1+(4882004599/10000000000 : ℝ)*X 0 2+(66816817/156250000 : ℝ)*X 1 0+(3738707521/10000000000 : ℝ)*X 1 1+(4882004599/10000000000 : ℝ)*X 1 2+(66816817/156250000 : ℝ)*X 2 0+(3738707521/10000000000 : ℝ)*X 2 1+(4882004599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-241268921/1250000000 : ℝ)*X 0 0+(5082499087/10000000000 : ℝ)*X 0 1+(174941601/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314652213/2500000000 : ℝ)*X 1 0+(-84386677/500000000 : ℝ)*X 1 1+(5598131249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((6573261/12500000 : ℝ)*X 2 0+(559813121/1000000000 : ℝ)*X 2 1+(-1687733669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2138566241/5000000000 : ℝ)*X 0 0+(4868620249/10000000000 : ℝ)*X 0 1+(938079433/2500000000 : ℝ)*X 0 2+(2138566241/5000000000 : ℝ)*X 1 0+(4868620249/10000000000 : ℝ)*X 1 1+(938079433/2500000000 : ℝ)*X 1 2+(2138566241/5000000000 : ℝ)*X 2 0+(4868620249/10000000000 : ℝ)*X 2 1+(938079433/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1129129563839868492727495917/151137500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (624248731/50000000000000 : ℝ)*(base19) + (100627803/6250000000000 : ℝ)*(base23) + (146870559/100000000000000 : ℝ)*(upper3) + (18106103/100000000000000 : ℝ)*(upper4) + (144830089/100000000000000 : ℝ)*(upper5) + (1384136506664119/100000000000000 : ℝ)*(major0) + (1384136506664119/100000000000000 : ℝ)*(major1) + (1384136506664119/100000000000000 : ℝ)*(major2) + (1893584450119171/100000000000000 : ℝ)*(sp0) + (946798765454993/50000000000000 : ℝ)*(sp1) + (9467985846813/500000000000 : ℝ)*(sp2) + (874668335533829/100000000000000 : ℝ)*(sp3) + (14329288277/100000000000000 : ℝ)*(sp4) + (353084859/6250000000000 : ℝ)*(sp7) + (218668496222893/25000000000000 : ℝ)*(f.failure) + (236699847425931/12500000000000 : ℝ)*(f.sum) + (136046122010021/120910000000000000000000000000 : ℝ)*base65 + (5475824991414802611/604550000000000000000000000000000 : ℝ)*base68 + (4261661208068802611/604550000000000000000000000000000 : ℝ)*base70 + (936229205079247389/604550000000000000000000000000000 : ℝ)*base71 + (705697222501539/120910000000000000000000000000 : ℝ)*base74 + (8045949992754002611/604550000000000000000000000000000 : ℝ)*base76 + (1300915027082152611/604550000000000000000000000000000 : ℝ)*base78 + (7280822443294902611/604550000000000000000000000000000 : ℝ)*base80 + (155465257955659/120910000000000000000000000000 : ℝ)*base82 + (1155093/250000000000000000000 : ℝ)*base90 + (1155093/250000000000000000000 : ℝ)*base92 + (1155093/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10745065789406305608423/1511375000000000000000000000 : ℝ) := by norm_num
    linear_combination (14622733/25000000000000 : ℝ)*(base1) + (1499614231/100000000000000 : ℝ)*(base19) + (294412391/20000000000000 : ℝ)*(base23) + (172810971/100000000000000 : ℝ)*(upper3) + (7552657/5000000000000 : ℝ)*(upper5) + (35439769185177/2500000000000 : ℝ)*(major0) + (35439769185177/2500000000000 : ℝ)*(major1) + (35439769185177/2500000000000 : ℝ)*(major2) + (8774253311/100000000000000 : ℝ)*(sp1) + (422752519/5000000000000 : ℝ)*(sp2) + (24242083782041/1250000000000 : ℝ)*(sp4) + (969678185102403/50000000000000 : ℝ)*(sp5) + (1939356716960013/100000000000000 : ℝ)*(sp6) + (143330335243/16000000000 : ℝ)*(sp7) + (895814653759681/100000000000000 : ℝ)*(f.failure) + (484841661018087/25000000000000 : ℝ)*(f.sum) + (557347435023/755687500000000000000000000 : ℝ)*base66 + (5324395198426913/15113750000000000000000000000000 : ℝ)*base68 + (17787070271364413/15113750000000000000000000000000 : ℝ)*base70 + (42795177014693087/15113750000000000000000000000000 : ℝ)*base71 + (8143768952851/2418200000000000000000000000 : ℝ)*base74 + (65674796289929413/15113750000000000000000000000000 : ℝ)*base76 + (16908958333160587/15113750000000000000000000000000 : ℝ)*base77 + (53272165052310587/15113750000000000000000000000000 : ℝ)*base79 + (4436316403341/12091000000000000000000000000 : ℝ)*base82 + (5807081/1000000000000000000000 : ℝ)*base90 + (5807081/1000000000000000000000 : ℝ)*base92 + (5807081/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1431_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6561/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1031/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1917/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18833/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1431_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1431_s2_0 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-392547407/2000000000 : ℝ)*x 0 + (545772653/1000000000 : ℝ)*x 1 + (1040355373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (392547407/2000000000 : ℝ)^4391 ≤ (11961935937917/100000000000000 : ℝ)^3367 := by
    have hnat : (392547407 : ℕ)^4391*100000000000000^3367 ≤ 11961935937917^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392547407 2000000000 11961935937917 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545772653/1000000000 : ℝ)^4391 ≤ (45397256361053/100000000000000 : ℝ)^3367 := by
    have hnat : (545772653 : ℕ)^4391*100000000000000^3367 ≤ 45397256361053^3367*1000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545772653 1000000000 45397256361053 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040355373/2000000000 : ℝ)^4391 ≤ (42640807692787/100000000000000 : ℝ)^3367 := by
    have hnat : (1040355373 : ℕ)^4391*100000000000000^3367 ≤ 42640807692787^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040355373 2000000000 42640807692787 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-392547407/2000000000 : ℝ), (545772653/1000000000 : ℝ), (1040355373/2000000000 : ℝ)] ![(11961935937917/100000000000000 : ℝ), (45397256361053/100000000000000 : ℝ), (42640807692787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-392547407/2000000000 : ℝ)|^4391 ≤ (11961935937917/100000000000000 : ℝ)^3367
        have hw : |(-392547407/2000000000 : ℝ)|=(392547407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545772653/1000000000 : ℝ)|^4391 ≤ (45397256361053/100000000000000 : ℝ)^3367
        have hw : |(545772653/1000000000 : ℝ)|=(545772653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040355373/2000000000 : ℝ)|^4391 ≤ (42640807692787/100000000000000 : ℝ)^3367
        have hw : |(1040355373/2000000000 : ℝ)|=(1040355373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s2_1 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360014151/10000000000 : ℝ)*x 0 + (-1047205211/5000000000 : ℝ)*x 1 + (2600888377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360014151/10000000000 : ℝ)^4391 ≤ (44340198374047/100000000000000 : ℝ)^3367 := by
    have hnat : (5360014151 : ℕ)^4391*100000000000000^3367 ≤ 44340198374047^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360014151 10000000000 44340198374047 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047205211/5000000000 : ℝ)^4391 ≤ (13018995113193/100000000000000 : ℝ)^3367 := by
    have hnat : (1047205211 : ℕ)^4391*100000000000000^3367 ≤ 13018995113193^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047205211 5000000000 13018995113193 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2600888377/5000000000 : ℝ)^4391 ≤ (5330100813269/12500000000000 : ℝ)^3367 := by
    have hnat : (2600888377 : ℕ)^4391*12500000000000^3367 ≤ 5330100813269^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600888377 5000000000 5330100813269 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360014151/10000000000 : ℝ), (-1047205211/5000000000 : ℝ), (2600888377/5000000000 : ℝ)] ![(44340198374047/100000000000000 : ℝ), (13018995113193/100000000000000 : ℝ), (5330100813269/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360014151/10000000000 : ℝ)|^4391 ≤ (44340198374047/100000000000000 : ℝ)^3367
        have hw : |(5360014151/10000000000 : ℝ)|=(5360014151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047205211/5000000000 : ℝ)|^4391 ≤ (13018995113193/100000000000000 : ℝ)^3367
        have hw : |(-1047205211/5000000000 : ℝ)|=(1047205211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2600888377/5000000000 : ℝ)|^4391 ≤ (5330100813269/12500000000000 : ℝ)^3367
        have hw : |(2600888377/5000000000 : ℝ)|=(2600888377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s2_2 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360013757/10000000000 : ℝ)*x 0 + (2600888599/5000000000 : ℝ)*x 1 + (-2094410361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360013757/10000000000 : ℝ)^4391 ≤ (44340194123467/100000000000000 : ℝ)^3367 := by
    have hnat : (5360013757 : ℕ)^4391*100000000000000^3367 ≤ 44340194123467^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360013757 10000000000 44340194123467 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2600888599/5000000000 : ℝ)^4391 ≤ (42640811252691/100000000000000 : ℝ)^3367 := by
    have hnat : (2600888599 : ℕ)^4391*100000000000000^3367 ≤ 42640811252691^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600888599 5000000000 42640811252691 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2094410361/10000000000 : ℝ)^4391 ≤ (13018994618693/100000000000000 : ℝ)^3367 := by
    have hnat : (2094410361 : ℕ)^4391*100000000000000^3367 ≤ 13018994618693^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094410361 10000000000 13018994618693 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360013757/10000000000 : ℝ), (2600888599/5000000000 : ℝ), (-2094410361/10000000000 : ℝ)] ![(44340194123467/100000000000000 : ℝ), (42640811252691/100000000000000 : ℝ), (13018994618693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360013757/10000000000 : ℝ)|^4391 ≤ (44340194123467/100000000000000 : ℝ)^3367
        have hw : |(5360013757/10000000000 : ℝ)|=(5360013757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2600888599/5000000000 : ℝ)|^4391 ≤ (42640811252691/100000000000000 : ℝ)^3367
        have hw : |(2600888599/5000000000 : ℝ)|=(2600888599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2094410361/10000000000 : ℝ)|^4391 ≤ (13018994618693/100000000000000 : ℝ)^3367
        have hw : |(-2094410361/10000000000 : ℝ)|=(2094410361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s2_3 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149781513/5000000000 : ℝ)*x 0 + (3224411/8000000 : ℝ)*x 1 + (4584624467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149781513/5000000000 : ℝ)^4391 ≤ (16630614008167/50000000000000 : ℝ)^3367 := by
    have hnat : (2149781513 : ℕ)^4391*50000000000000^3367 ≤ 16630614008167^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149781513 5000000000 16630614008167 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3224411/8000000 : ℝ)^4391 ≤ (15286545076259/50000000000000 : ℝ)^3367 := by
    have hnat : (3224411 : ℕ)^4391*50000000000000^3367 ≤ 15286545076259^3367*8000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3224411 8000000 15286545076259 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4584624467/10000000000 : ℝ)^4391 ≤ (4520710227027/12500000000000 : ℝ)^3367 := by
    have hnat : (4584624467 : ℕ)^4391*12500000000000^3367 ≤ 4520710227027^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584624467 10000000000 4520710227027 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149781513/5000000000 : ℝ), (3224411/8000000 : ℝ), (4584624467/10000000000 : ℝ)] ![(16630614008167/50000000000000 : ℝ), (15286545076259/50000000000000 : ℝ), (4520710227027/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149781513/5000000000 : ℝ)|^4391 ≤ (16630614008167/50000000000000 : ℝ)^3367
        have hw : |(2149781513/5000000000 : ℝ)|=(2149781513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3224411/8000000 : ℝ)|^4391 ≤ (15286545076259/50000000000000 : ℝ)^3367
        have hw : |(3224411/8000000 : ℝ)|=(3224411/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4584624467/10000000000 : ℝ)|^4391 ≤ (4520710227027/12500000000000 : ℝ)^3367
        have hw : |(4584624467/10000000000 : ℝ)|=(4584624467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s2_4 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1962782221/10000000000 : ℝ)*x 0 + (2601619101/5000000000 : ℝ)*x 1 + (2728126577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962782221/10000000000 : ℝ)^4391 ≤ (2392459015801/20000000000000 : ℝ)^3367 := by
    have hnat : (1962782221 : ℕ)^4391*20000000000000^3367 ≤ 2392459015801^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962782221 10000000000 2392459015801 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601619101/5000000000 : ℝ)^4391 ≤ (21328215319831/50000000000000 : ℝ)^3367 := by
    have hnat : (2601619101 : ℕ)^4391*50000000000000^3367 ≤ 21328215319831^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601619101 5000000000 21328215319831 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728126577/5000000000 : ℝ)^4391 ≤ (22690637129161/50000000000000 : ℝ)^3367 := by
    have hnat : (2728126577 : ℕ)^4391*50000000000000^3367 ≤ 22690637129161^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728126577 5000000000 22690637129161 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1962782221/10000000000 : ℝ), (2601619101/5000000000 : ℝ), (2728126577/5000000000 : ℝ)] ![(2392459015801/20000000000000 : ℝ), (21328215319831/50000000000000 : ℝ), (22690637129161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1962782221/10000000000 : ℝ)|^4391 ≤ (2392459015801/20000000000000 : ℝ)^3367
        have hw : |(-1962782221/10000000000 : ℝ)|=(1962782221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601619101/5000000000 : ℝ)|^4391 ≤ (21328215319831/50000000000000 : ℝ)^3367
        have hw : |(2601619101/5000000000 : ℝ)|=(2601619101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728126577/5000000000 : ℝ)|^4391 ≤ (22690637129161/50000000000000 : ℝ)^3367
        have hw : |(2728126577/5000000000 : ℝ)|=(2728126577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s2_5 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646723081/5000000000 : ℝ)*x 0 + (-18399337/100000000 : ℝ)*x 1 + (5456253631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646723081/5000000000 : ℝ)^4391 ≤ (21811702389979/50000000000000 : ℝ)^3367 := by
    have hnat : (2646723081 : ℕ)^4391*50000000000000^3367 ≤ 21811702389979^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646723081 5000000000 21811702389979 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18399337/100000000 : ℝ)^4391 ≤ (10995315763191/100000000000000 : ℝ)^3367 := by
    have hnat : (18399337 : ℕ)^4391*100000000000000^3367 ≤ 10995315763191^3367*100000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18399337 100000000 10995315763191 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456253631/10000000000 : ℝ)^4391 ≤ (709082491129/1562500000000 : ℝ)^3367 := by
    have hnat : (5456253631 : ℕ)^4391*1562500000000^3367 ≤ 709082491129^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456253631 10000000000 709082491129 1562500000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646723081/5000000000 : ℝ), (-18399337/100000000 : ℝ), (5456253631/10000000000 : ℝ)] ![(21811702389979/50000000000000 : ℝ), (10995315763191/100000000000000 : ℝ), (709082491129/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646723081/5000000000 : ℝ)|^4391 ≤ (21811702389979/50000000000000 : ℝ)^3367
        have hw : |(2646723081/5000000000 : ℝ)|=(2646723081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18399337/100000000 : ℝ)|^4391 ≤ (10995315763191/100000000000000 : ℝ)^3367
        have hw : |(-18399337/100000000 : ℝ)|=(18399337/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456253631/10000000000 : ℝ)|^4391 ≤ (709082491129/1562500000000 : ℝ)^3367
        have hw : |(5456253631/10000000000 : ℝ)|=(5456253631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s2_6 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646723013/5000000000 : ℝ)*x 0 + (5456253599/10000000000 : ℝ)*x 1 + (-919966967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646723013/5000000000 : ℝ)^4391 ≤ (21811701659159/50000000000000 : ℝ)^3367 := by
    have hnat : (2646723013 : ℕ)^4391*50000000000000^3367 ≤ 21811701659159^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646723013 5000000000 21811701659159 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456253599/10000000000 : ℝ)^4391 ≤ (22690639542579/50000000000000 : ℝ)^3367 := by
    have hnat : (5456253599 : ℕ)^4391*50000000000000^3367 ≤ 22690639542579^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456253599 10000000000 22690639542579 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919966967/5000000000 : ℝ)^4391 ≤ (5497658793421/50000000000000 : ℝ)^3367 := by
    have hnat : (919966967 : ℕ)^4391*50000000000000^3367 ≤ 5497658793421^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919966967 5000000000 5497658793421 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646723013/5000000000 : ℝ), (5456253599/10000000000 : ℝ), (-919966967/5000000000 : ℝ)] ![(21811701659159/50000000000000 : ℝ), (22690639542579/50000000000000 : ℝ), (5497658793421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646723013/5000000000 : ℝ)|^4391 ≤ (21811701659159/50000000000000 : ℝ)^3367
        have hw : |(2646723013/5000000000 : ℝ)|=(2646723013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456253599/10000000000 : ℝ)|^4391 ≤ (22690639542579/50000000000000 : ℝ)^3367
        have hw : |(5456253599/10000000000 : ℝ)|=(5456253599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-919966967/5000000000 : ℝ)|^4391 ≤ (5497658793421/50000000000000 : ℝ)^3367
        have hw : |(-919966967/5000000000 : ℝ)|=(919966967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s2_7 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299660703/10000000000 : ℝ)*x 0 + (4581461149/10000000000 : ℝ)*x 1 + (403370311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299660703/10000000000 : ℝ)^4391 ≤ (519722085181/1562500000000 : ℝ)^3367 := by
    have hnat : (4299660703 : ℕ)^4391*1562500000000^3367 ≤ 519722085181^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299660703 10000000000 519722085181 1562500000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4581461149/10000000000 : ℝ)^4391 ≤ (36133142345391/100000000000000 : ℝ)^3367 := by
    have hnat : (4581461149 : ℕ)^4391*100000000000000^3367 ≤ 36133142345391^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581461149 10000000000 36133142345391 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403370311/1000000000 : ℝ)^4391 ≤ (3825580524677/12500000000000 : ℝ)^3367 := by
    have hnat : (403370311 : ℕ)^4391*12500000000000^3367 ≤ 3825580524677^3367*1000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403370311 1000000000 3825580524677 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299660703/10000000000 : ℝ), (4581461149/10000000000 : ℝ), (403370311/1000000000 : ℝ)] ![(519722085181/1562500000000 : ℝ), (36133142345391/100000000000000 : ℝ), (3825580524677/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299660703/10000000000 : ℝ)|^4391 ≤ (519722085181/1562500000000 : ℝ)^3367
        have hw : |(4299660703/10000000000 : ℝ)|=(4299660703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4581461149/10000000000 : ℝ)|^4391 ≤ (36133142345391/100000000000000 : ℝ)^3367
        have hw : |(4581461149/10000000000 : ℝ)|=(4581461149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403370311/1000000000 : ℝ)|^4391 ≤ (3825580524677/12500000000000 : ℝ)^3367
        have hw : |(403370311/1000000000 : ℝ)|=(403370311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1431_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1917/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5189/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15793/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18833/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1917/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18833/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1917/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18833/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1917/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18833/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1917/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18833/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1917/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18833/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1917/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1917/25000 : ℝ) ^ (2195/512 : ℝ) ≤ (1653903601223453/100000000000000000000 : ℝ) := by
    have hpowers : (1917/25000 : ℝ)^2195 ≤ (1653903601223453/100000000000000000000 : ℝ)^512 := by
      have hnat : (1917 : ℕ)^2195*100000000000000000000^512 ≤ 1653903601223453^512*25000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1917 25000 1653903601223453 100000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1917/25000 : ℝ)) (X := (1653903601223453/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hpowhi : (18833/100000 : ℝ) ^ (2195/512 : ℝ) ≤ (77893392346524257/100000000000000000000 : ℝ) := by
    have hpowers : (18833/100000 : ℝ)^2195 ≤ (77893392346524257/100000000000000000000 : ℝ)^512 := by
      have hnat : (18833 : ℕ)^2195*100000000000000000000^512 ≤ 77893392346524257^512*100000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18833 100000 77893392346524257 100000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18833/100000 : ℝ)) (X := (77893392346524257/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001653903601223453/50000000000000000000 : ℝ) ≤ (5000038578036703/5000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50001653903601223453/50000000000000000000 : ℝ)^512 ≤ (5000038578036703/5000000000000000 : ℝ)^2195 := by
      have hnat : (50001653903601223453 : ℕ)^512*5000000000000000^2195 ≤ 5000038578036703^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001653903601223453 50000000000000000000 5000038578036703 5000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000038578036703/5000000000000000 : ℝ)) (X := (50001653903601223453/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10007954729594774771/10000000000000000000 : ℝ) ≤ (10001854933977353/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (10007954729594774771/10000000000000000000 : ℝ)^512 ≤ (10001854933977353/10000000000000000 : ℝ)^2195 := by
      have hnat : (10007954729594774771 : ℕ)^512*10000000000000000^2195 ≤ 10001854933977353^2195*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007954729594774771 10000000000000000000 10001854933977353 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001854933977353/10000000000000000 : ℝ)) (X := (10007954729594774771/10000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50077893392346524257/50000000000000000000 : ℝ) ≤ (100036327118813/100000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50077893392346524257/50000000000000000000 : ℝ)^512 ≤ (100036327118813/100000000000000 : ℝ)^2195 := by
      have hnat : (50077893392346524257 : ℕ)^512*100000000000000^2195 ≤ 100036327118813^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50077893392346524257 50000000000000000000 100036327118813 100000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100036327118813/100000000000000 : ℝ)) (X := (50077893392346524257/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1653903601223453/100000000000000000000 : ℝ) ≤ ((1924544783545252531/1925000000000000000 : ℝ)+2*(61302686343/38500000000000 : ℝ)*(1917/25000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (1924544783545252531/1925000000000000000 : ℝ)+2*(61302686343/38500000000000 : ℝ)*(1917/25000 : ℝ)=(5000038578036703/5000000000000000 : ℝ) by norm_num, show 1+2*(1653903601223453/100000000000000000000 : ℝ)=(50001653903601223453/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(77893392346524257/100000000000000000000 : ℝ)+(1653903601223453/100000000000000000000 : ℝ) ≤ ((1924544783545252531/1925000000000000000 : ℝ)+(61302686343/38500000000000 : ℝ)*((18833/100000 : ℝ)+(1917/25000 : ℝ)))^(2195/512 : ℝ) := by
    rw [show (1924544783545252531/1925000000000000000 : ℝ)+(61302686343/38500000000000 : ℝ)*((18833/100000 : ℝ)+(1917/25000 : ℝ))=(10001854933977353/10000000000000000 : ℝ) by norm_num, show 1+(77893392346524257/100000000000000000000 : ℝ)+(1653903601223453/100000000000000000000 : ℝ)=(10007954729594774771/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(77893392346524257/100000000000000000000 : ℝ) ≤ ((1924544783545252531/1925000000000000000 : ℝ)+2*(61302686343/38500000000000 : ℝ)*(18833/100000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (1924544783545252531/1925000000000000000 : ℝ)+2*(61302686343/38500000000000 : ℝ)*(18833/100000 : ℝ)=(100036327118813/100000000000000 : ℝ) by norm_num, show 1+2*(77893392346524257/100000000000000000000 : ℝ)=(50077893392346524257/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1924544783545252531/1925000000000000000 : ℝ)*(X 1 0+X 2 0)+(61302686343/38500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (1917/25000 : ℝ)) (hi := (18833/100000 : ℝ)) (c := (1924544783545252531/1925000000000000000 : ℝ)) (alpha := (61302686343/38500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1924544783545252531/1925000000000000000 : ℝ)*(X 0 1+X 2 1)+(61302686343/38500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (1917/25000 : ℝ)) (hi := (18833/100000 : ℝ)) (c := (1924544783545252531/1925000000000000000 : ℝ)) (alpha := (61302686343/38500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1924544783545252531/1925000000000000000 : ℝ)*(X 0 2+X 1 2)+(61302686343/38500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (1917/25000 : ℝ)) (hi := (18833/100000 : ℝ)) (c := (1924544783545252531/1925000000000000000 : ℝ)) (alpha := (61302686343/38500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-392547407/2000000000 : ℝ)*X 0 0+(545772653/1000000000 : ℝ)*X 0 1+(1040355373/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360014151/10000000000 : ℝ)*X 1 0+(-1047205211/5000000000 : ℝ)*X 1 1+(2600888377/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360013757/10000000000 : ℝ)*X 2 0+(2600888599/5000000000 : ℝ)*X 2 1+(-2094410361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149781513/5000000000 : ℝ)*X 0 0+(3224411/8000000 : ℝ)*X 0 1+(4584624467/10000000000 : ℝ)*X 0 2+(2149781513/5000000000 : ℝ)*X 1 0+(3224411/8000000 : ℝ)*X 1 1+(4584624467/10000000000 : ℝ)*X 1 2+(2149781513/5000000000 : ℝ)*X 2 0+(3224411/8000000 : ℝ)*X 2 1+(4584624467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1962782221/10000000000 : ℝ)*X 0 0+(2601619101/5000000000 : ℝ)*X 0 1+(2728126577/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646723081/5000000000 : ℝ)*X 1 0+(-18399337/100000000 : ℝ)*X 1 1+(5456253631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646723013/5000000000 : ℝ)*X 2 0+(5456253599/10000000000 : ℝ)*X 2 1+(-919966967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4299660703/10000000000 : ℝ)*X 0 0+(4581461149/10000000000 : ℝ)*X 0 1+(403370311/1000000000 : ℝ)*X 0 2+(4299660703/10000000000 : ℝ)*X 1 0+(4581461149/10000000000 : ℝ)*X 1 1+(403370311/1000000000 : ℝ)*X 1 2+(4299660703/10000000000 : ℝ)*X 2 0+(4581461149/10000000000 : ℝ)*X 2 1+(403370311/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (420793010473170042050306049/48125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1253852209/100000000000000 : ℝ)*(base19) + (354397309/50000000000000 : ℝ)*(base23) + (69107043/50000000000000 : ℝ)*(lower2) + (54411067/20000000000000 : ℝ)*(upper3) + (65340503/100000000000000 : ℝ)*(upper5) + (2855876149270607/100000000000000 : ℝ)*(major0) + (2855876149270607/100000000000000 : ℝ)*(major1) + (2855876149270607/100000000000000 : ℝ)*(major2) + (244189622244731/6250000000000 : ℝ)*(sp0) + (3907043948798747/100000000000000 : ℝ)*(sp1) + (1953522246928169/50000000000000 : ℝ)*(sp2) + (902349524584321/50000000000000 : ℝ)*(sp3) + (11246735259/100000000000000 : ℝ)*(sp4) + (7755263247/100000000000000 : ℝ)*(sp7) + (1804706804431889/100000000000000 : ℝ)*(f.failure) + (976761300662739/25000000000000 : ℝ)*(f.sum) + (4525222117749/1925000000000000000000000000 : ℝ)*base66 + (1809606105338206317/192500000000000000000000000000000 : ℝ)*base67 + (1255014681605706317/192500000000000000000000000000000 : ℝ)*base69 + (1347609064255706317/192500000000000000000000000000000 : ℝ)*base71 + (695536170297/240625000000000000000000000 : ℝ)*base73 + (888495199045706317/192500000000000000000000000000000 : ℝ)*base75 + (633326251526793683/192500000000000000000000000000000 : ℝ)*base78 + (234108773083206317/192500000000000000000000000000000 : ℝ)*base79 + (3039330585651/1925000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3762489/1000000000000000000000 : ℝ)*base90 + (3762489/1000000000000000000000 : ℝ)*base92 + (3762489/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (151520839890773600339528211/48125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43281993/100000000000000 : ℝ)*(base15) + (5229029/20000000000000 : ℝ)*(base29) + (25707557/25000000000000 : ℝ)*(upper3) + (37834167/50000000000000 : ℝ)*(lower4) + (1444488892278533/50000000000000 : ℝ)*(major0) + (722244452675553/25000000000000 : ℝ)*(major1) + (722244452675553/25000000000000 : ℝ)*(major2) + (1880578591/100000000000000 : ℝ)*(sp1) + (824190739/50000000000000 : ℝ)*(sp2) + (226277319/50000000000000 : ℝ)*(sp3) + (494041357546523/12500000000000 : ℝ)*(sp4) + (494041113795807/12500000000000 : ℝ)*(sp5) + (1976164592922781/50000000000000 : ℝ)*(sp6) + (456406050882023/25000000000000 : ℝ)*(sp7) + (182562465608273/10000000000000 : ℝ)*(f.failure) + (494041357546523/12500000000000 : ℝ)*(f.sum) + (2532759928571/481250000000000000000000000 : ℝ)*base66 + (596564932659024643/48125000000000000000000000000000 : ℝ)*base67 + (397855892032774643/48125000000000000000000000000000 : ℝ)*base69 + (790443111043132977/96250000000000000000000000000000 : ℝ)*base72 + (7649811678627/1925000000000000000000000000 : ℝ)*base73 + (180112919213641/625000000000000000000000000000 : ℝ)*base76 + (417786821749382977/96250000000000000000000000000000 : ℝ)*base78 + (7151126409536359/625000000000000000000000000000 : ℝ)*base79 + (246869409823/1925000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (307527/100000000000000000000 : ℝ)*base89 + (692473/100000000000000000000 : ℝ)*base92 + (692473/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1431_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1917/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5189/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15793/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1431_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1431_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5189/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15793/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1431_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1431_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1431_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5189/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15793/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1431_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

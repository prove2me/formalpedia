-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1381_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:30.778935+00:00
-- url     : https://prove2.me/submissions/5e6649b8-4554-4fad-ba7c-b59008075afa

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
theorem support_rectangle_w1381_s6_0 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1005374679/5000000000 : ℝ)*x 0 + (67633817/125000000 : ℝ)*x 1 + (5245720157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005374679/5000000000 : ℝ)^4341 ≤ (12254502717961/100000000000000 : ℝ)^3317 := by
    have hnat : (1005374679 : ℕ)^4341*100000000000000^3317 ≤ 12254502717961^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005374679 5000000000 12254502717961 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67633817/125000000 : ℝ)^4341 ≤ (44761638324349/100000000000000 : ℝ)^3317 := by
    have hnat : (67633817 : ℕ)^4341*100000000000000^3317 ≤ 44761638324349^3317*125000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67633817 125000000 44761638324349 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245720157/10000000000 : ℝ)^4341 ≤ (42983858948427/100000000000000 : ℝ)^3317 := by
    have hnat : (5245720157 : ℕ)^4341*100000000000000^3317 ≤ 42983858948427^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245720157 10000000000 42983858948427 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1005374679/5000000000 : ℝ), (67633817/125000000 : ℝ), (5245720157/10000000000 : ℝ)] ![(12254502717961/100000000000000 : ℝ), (44761638324349/100000000000000 : ℝ), (42983858948427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1005374679/5000000000 : ℝ)|^4341 ≤ (12254502717961/100000000000000 : ℝ)^3317
        have hw : |(-1005374679/5000000000 : ℝ)|=(1005374679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67633817/125000000 : ℝ)|^4341 ≤ (44761638324349/100000000000000 : ℝ)^3317
        have hw : |(67633817/125000000 : ℝ)|=(67633817/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245720157/10000000000 : ℝ)|^4341 ≤ (42983858948427/100000000000000 : ℝ)^3317
        have hw : |(5245720157/10000000000 : ℝ)|=(5245720157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s6_1 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674146549/5000000000 : ℝ)*x 0 + (-261847607/1250000000 : ℝ)*x 1 + (5245720151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674146549/5000000000 : ℝ)^4341 ≤ (11021781337053/25000000000000 : ℝ)^3317 := by
    have hnat : (2674146549 : ℕ)^4341*25000000000000^3317 ≤ 11021781337053^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674146549 5000000000 11021781337053 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261847607/1250000000 : ℝ)^4341 ≤ (2585803151157/20000000000000 : ℝ)^3317 := by
    have hnat : (261847607 : ℕ)^4341*20000000000000^3317 ≤ 2585803151157^3317*1250000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261847607 1250000000 2585803151157 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245720151/10000000000 : ℝ)^4341 ≤ (8596771776817/20000000000000 : ℝ)^3317 := by
    have hnat : (5245720151 : ℕ)^4341*20000000000000^3317 ≤ 8596771776817^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245720151 10000000000 8596771776817 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674146549/5000000000 : ℝ), (-261847607/1250000000 : ℝ), (5245720151/10000000000 : ℝ)] ![(11021781337053/25000000000000 : ℝ), (2585803151157/20000000000000 : ℝ), (8596771776817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674146549/5000000000 : ℝ)|^4341 ≤ (11021781337053/25000000000000 : ℝ)^3317
        have hw : |(2674146549/5000000000 : ℝ)|=(2674146549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261847607/1250000000 : ℝ)|^4341 ≤ (2585803151157/20000000000000 : ℝ)^3317
        have hw : |(-261847607/1250000000 : ℝ)|=(261847607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245720151/10000000000 : ℝ)|^4341 ≤ (8596771776817/20000000000000 : ℝ)^3317
        have hw : |(5245720151/10000000000 : ℝ)|=(5245720151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s6_2 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674146547/5000000000 : ℝ)*x 0 + (1311430041/2500000000 : ℝ)*x 1 + (-418956169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674146547/5000000000 : ℝ)^4341 ≤ (2204356265253/5000000000000 : ℝ)^3317 := by
    have hnat : (2674146547 : ℕ)^4341*5000000000000^3317 ≤ 2204356265253^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674146547 5000000000 2204356265253 5000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311430041/2500000000 : ℝ)^4341 ≤ (42983859023493/100000000000000 : ℝ)^3317 := by
    have hnat : (1311430041 : ℕ)^4341*100000000000000^3317 ≤ 42983859023493^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311430041 2500000000 42983859023493 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418956169/2000000000 : ℝ)^4341 ≤ (12929015666933/100000000000000 : ℝ)^3317 := by
    have hnat : (418956169 : ℕ)^4341*100000000000000^3317 ≤ 12929015666933^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418956169 2000000000 12929015666933 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674146547/5000000000 : ℝ), (1311430041/2500000000 : ℝ), (-418956169/2000000000 : ℝ)] ![(2204356265253/5000000000000 : ℝ), (42983859023493/100000000000000 : ℝ), (12929015666933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674146547/5000000000 : ℝ)|^4341 ≤ (2204356265253/5000000000000 : ℝ)^3317
        have hw : |(2674146547/5000000000 : ℝ)|=(2674146547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311430041/2500000000 : ℝ)|^4341 ≤ (42983859023493/100000000000000 : ℝ)^3317
        have hw : |(1311430041/2500000000 : ℝ)|=(1311430041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418956169/2000000000 : ℝ)|^4341 ≤ (12929015666933/100000000000000 : ℝ)^3317
        have hw : |(-418956169/2000000000 : ℝ)|=(418956169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s6_3 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4316523097/10000000000 : ℝ)*x 0 + (1036117057/2500000000 : ℝ)*x 1 + (4495119211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316523097/10000000000 : ℝ)^4341 ≤ (33303917746889/100000000000000 : ℝ)^3317 := by
    have hnat : (4316523097 : ℕ)^4341*100000000000000^3317 ≤ 33303917746889^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316523097 10000000000 33303917746889 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036117057/2500000000 : ℝ)^4341 ≤ (2466985591/7812500000 : ℝ)^3317 := by
    have hnat : (1036117057 : ℕ)^4341*7812500000^3317 ≤ 2466985591^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036117057 2500000000 2466985591 7812500000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495119211/10000000000 : ℝ)^4341 ≤ (1404746666877/4000000000000 : ℝ)^3317 := by
    have hnat : (4495119211 : ℕ)^4341*4000000000000^3317 ≤ 1404746666877^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495119211 10000000000 1404746666877 4000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316523097/10000000000 : ℝ), (1036117057/2500000000 : ℝ), (4495119211/10000000000 : ℝ)] ![(33303917746889/100000000000000 : ℝ), (2466985591/7812500000 : ℝ), (1404746666877/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316523097/10000000000 : ℝ)|^4341 ≤ (33303917746889/100000000000000 : ℝ)^3317
        have hw : |(4316523097/10000000000 : ℝ)|=(4316523097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036117057/2500000000 : ℝ)|^4341 ≤ (2466985591/7812500000 : ℝ)^3317
        have hw : |(1036117057/2500000000 : ℝ)|=(1036117057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495119211/10000000000 : ℝ)|^4341 ≤ (1404746666877/4000000000000 : ℝ)^3317
        have hw : |(4495119211/10000000000 : ℝ)|=(4495119211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s6_4 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010761147/10000000000 : ℝ)*x 0 + (1311578203/2500000000 : ℝ)*x 1 + (2705054819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010761147/10000000000 : ℝ)^4341 ≤ (3063649186611/25000000000000 : ℝ)^3317 := by
    have hnat : (2010761147 : ℕ)^4341*25000000000000^3317 ≤ 3063649186611^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010761147 10000000000 3063649186611 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311578203/2500000000 : ℝ)^4341 ≤ (8598042902567/20000000000000 : ℝ)^3317 := by
    have hnat : (1311578203 : ℕ)^4341*20000000000000^3317 ≤ 8598042902567^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311578203 2500000000 8598042902567 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705054819/5000000000 : ℝ)^4341 ≤ (44755188726129/100000000000000 : ℝ)^3317 := by
    have hnat : (2705054819 : ℕ)^4341*100000000000000^3317 ≤ 44755188726129^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705054819 5000000000 44755188726129 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010761147/10000000000 : ℝ), (1311578203/2500000000 : ℝ), (2705054819/5000000000 : ℝ)] ![(3063649186611/25000000000000 : ℝ), (8598042902567/20000000000000 : ℝ), (44755188726129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010761147/10000000000 : ℝ)|^4341 ≤ (3063649186611/25000000000000 : ℝ)^3317
        have hw : |(-2010761147/10000000000 : ℝ)|=(2010761147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311578203/2500000000 : ℝ)|^4341 ≤ (8598042902567/20000000000000 : ℝ)^3317
        have hw : |(1311578203/2500000000 : ℝ)|=(1311578203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705054819/5000000000 : ℝ)|^4341 ≤ (44755188726129/100000000000000 : ℝ)^3317
        have hw : |(2705054819/5000000000 : ℝ)|=(2705054819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s6_5 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8488979/16000000 : ℝ)*x 0 + (-1930391359/10000000000 : ℝ)*x 1 + (2705054821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8488979/16000000 : ℝ)^4341 ≤ (21813624294151/50000000000000 : ℝ)^3317 := by
    have hnat : (8488979 : ℕ)^4341*50000000000000^3317 ≤ 21813624294151^3317*16000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8488979 16000000 21813624294151 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930391359/10000000000 : ℝ)^4341 ≤ (2904390656549/25000000000000 : ℝ)^3317 := by
    have hnat : (1930391359 : ℕ)^4341*25000000000000^3317 ≤ 2904390656549^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930391359 10000000000 2904390656549 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705054821/5000000000 : ℝ)^4341 ≤ (8951037753887/20000000000000 : ℝ)^3317 := by
    have hnat : (2705054821 : ℕ)^4341*20000000000000^3317 ≤ 8951037753887^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705054821 5000000000 8951037753887 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8488979/16000000 : ℝ), (-1930391359/10000000000 : ℝ), (2705054821/5000000000 : ℝ)] ![(21813624294151/50000000000000 : ℝ), (2904390656549/25000000000000 : ℝ), (8951037753887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8488979/16000000 : ℝ)|^4341 ≤ (21813624294151/50000000000000 : ℝ)^3317
        have hw : |(8488979/16000000 : ℝ)|=(8488979/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1930391359/10000000000 : ℝ)|^4341 ≤ (2904390656549/25000000000000 : ℝ)^3317
        have hw : |(-1930391359/10000000000 : ℝ)|=(1930391359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705054821/5000000000 : ℝ)|^4341 ≤ (8951037753887/20000000000000 : ℝ)^3317
        have hw : |(2705054821/5000000000 : ℝ)|=(2705054821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s6_6 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326402971/2500000000 : ℝ)*x 0 + (5410109637/10000000000 : ℝ)*x 1 + (-1930391353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326402971/2500000000 : ℝ)^4341 ≤ (8725449737031/20000000000000 : ℝ)^3317 := by
    have hnat : (1326402971 : ℕ)^4341*20000000000000^3317 ≤ 8725449737031^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326402971 2500000000 8725449737031 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410109637/10000000000 : ℝ)^4341 ≤ (44755188715303/100000000000000 : ℝ)^3317 := by
    have hnat : (5410109637 : ℕ)^4341*100000000000000^3317 ≤ 44755188715303^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410109637 10000000000 44755188715303 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1930391353/10000000000 : ℝ)^4341 ≤ (11617562578939/100000000000000 : ℝ)^3317 := by
    have hnat : (1930391353 : ℕ)^4341*100000000000000^3317 ≤ 11617562578939^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930391353 10000000000 11617562578939 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326402971/2500000000 : ℝ), (5410109637/10000000000 : ℝ), (-1930391353/10000000000 : ℝ)] ![(8725449737031/20000000000000 : ℝ), (44755188715303/100000000000000 : ℝ), (11617562578939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326402971/2500000000 : ℝ)|^4341 ≤ (8725449737031/20000000000000 : ℝ)^3317
        have hw : |(1326402971/2500000000 : ℝ)|=(1326402971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410109637/10000000000 : ℝ)|^4341 ≤ (44755188715303/100000000000000 : ℝ)^3317
        have hw : |(5410109637/10000000000 : ℝ)|=(5410109637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1930391353/10000000000 : ℝ)|^4341 ≤ (11617562578939/100000000000000 : ℝ)^3317
        have hw : |(-1930391353/10000000000 : ℝ)|=(1930391353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s6_7 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539568517/1250000000 : ℝ)*x 0 + (2246929793/5000000000 : ℝ)*x 1 + (1036433591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539568517/1250000000 : ℝ)^4341 ≤ (33304170573591/100000000000000 : ℝ)^3317 := by
    have hnat : (539568517 : ℕ)^4341*100000000000000^3317 ≤ 33304170573591^3317*1250000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539568517 1250000000 33304170573591 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246929793/5000000000 : ℝ)^4341 ≤ (8776447055419/25000000000000 : ℝ)^3317 := by
    have hnat : (2246929793 : ℕ)^4341*25000000000000^3317 ≤ 8776447055419^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246929793 5000000000 8776447055419 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036433591/2500000000 : ℝ)^4341 ≤ (1974377574419/6250000000000 : ℝ)^3317 := by
    have hnat : (1036433591 : ℕ)^4341*6250000000000^3317 ≤ 1974377574419^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036433591 2500000000 1974377574419 6250000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539568517/1250000000 : ℝ), (2246929793/5000000000 : ℝ), (1036433591/2500000000 : ℝ)] ![(33304170573591/100000000000000 : ℝ), (8776447055419/25000000000000 : ℝ), (1974377574419/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539568517/1250000000 : ℝ)|^4341 ≤ (33304170573591/100000000000000 : ℝ)^3317
        have hw : |(539568517/1250000000 : ℝ)|=(539568517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246929793/5000000000 : ℝ)|^4341 ≤ (8776447055419/25000000000000 : ℝ)^3317
        have hw : |(2246929793/5000000000 : ℝ)|=(2246929793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036433591/2500000000 : ℝ)|^4341 ≤ (1974377574419/6250000000000 : ℝ)^3317
        have hw : |(1036433591/2500000000 : ℝ)|=(1036433591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1381_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5619/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14731/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (351/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (351/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (351/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (351/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (351/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (351/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (351/3125 : ℝ) ^ (1085/256 : ℝ) ≤ (9453009813710049/100000000000000000000 : ℝ) := by
    have hpowers : (351/3125 : ℝ)^1085 ≤ (9453009813710049/100000000000000000000 : ℝ)^256 := by
      have hnat : (351 : ℕ)^1085*100000000000000000000^256 ≤ 9453009813710049^256*3125^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 3125 9453009813710049 100000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/3125 : ℝ)) (X := (9453009813710049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14737/100000 : ℝ) ^ (1085/256 : ℝ) ≤ (29887102361512359/100000000000000000000 : ℝ) := by
    have hpowers : (14737/100000 : ℝ)^1085 ≤ (29887102361512359/100000000000000000000 : ℝ)^256 := by
      have hnat : (14737 : ℕ)^1085*100000000000000000000^256 ≤ 29887102361512359^256*100000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14737 100000 29887102361512359 100000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14737/100000 : ℝ)) (X := (29887102361512359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009453009813710049/50000000000000000000 : ℝ) ≤ (5000223022649439/5000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50009453009813710049/50000000000000000000 : ℝ)^256 ≤ (5000223022649439/5000000000000000 : ℝ)^1085 := by
      have hnat : (50009453009813710049 : ℕ)^256*5000000000000000^1085 ≤ 5000223022649439^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009453009813710049 50000000000000000000 5000223022649439 5000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000223022649439/5000000000000000 : ℝ)) (X := (50009453009813710049/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504917514021902801/12500000000000000000 : ℝ) ≤ (5000464034814973/5000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (12504917514021902801/12500000000000000000 : ℝ)^256 ≤ (5000464034814973/5000000000000000 : ℝ)^1085 := by
      have hnat : (12504917514021902801 : ℕ)^256*5000000000000000^1085 ≤ 5000464034814973^1085*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504917514021902801 12500000000000000000 5000464034814973 5000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000464034814973/5000000000000000 : ℝ)) (X := (12504917514021902801/12500000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029887102361512359/50000000000000000000 : ℝ) ≤ (5000705046980507/5000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50029887102361512359/50000000000000000000 : ℝ)^256 ≤ (5000705046980507/5000000000000000 : ℝ)^1085 := by
      have hnat : (50029887102361512359 : ℕ)^256*5000000000000000^1085 ≤ 5000705046980507^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029887102361512359 50000000000000000000 5000705046980507 5000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000705046980507/5000000000000000 : ℝ)) (X := (50029887102361512359/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9453009813710049/100000000000000000000 : ℝ) ≤ ((17520367597099727919/17525000000000000000 : ℝ)+2*(120506082767/87625000000000 : ℝ)*(351/3125 : ℝ))^(1085/256 : ℝ) := by
    rw [show (17520367597099727919/17525000000000000000 : ℝ)+2*(120506082767/87625000000000 : ℝ)*(351/3125 : ℝ)=(5000223022649439/5000000000000000 : ℝ) by norm_num, show 1+2*(9453009813710049/100000000000000000000 : ℝ)=(50009453009813710049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29887102361512359/100000000000000000000 : ℝ)+(9453009813710049/100000000000000000000 : ℝ) ≤ ((17520367597099727919/17525000000000000000 : ℝ)+(120506082767/87625000000000 : ℝ)*((14737/100000 : ℝ)+(351/3125 : ℝ)))^(1085/256 : ℝ) := by
    rw [show (17520367597099727919/17525000000000000000 : ℝ)+(120506082767/87625000000000 : ℝ)*((14737/100000 : ℝ)+(351/3125 : ℝ))=(5000464034814973/5000000000000000 : ℝ) by norm_num, show 1+(29887102361512359/100000000000000000000 : ℝ)+(9453009813710049/100000000000000000000 : ℝ)=(12504917514021902801/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29887102361512359/100000000000000000000 : ℝ) ≤ ((17520367597099727919/17525000000000000000 : ℝ)+2*(120506082767/87625000000000 : ℝ)*(14737/100000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (17520367597099727919/17525000000000000000 : ℝ)+2*(120506082767/87625000000000 : ℝ)*(14737/100000 : ℝ)=(5000705046980507/5000000000000000 : ℝ) by norm_num, show 1+2*(29887102361512359/100000000000000000000 : ℝ)=(50029887102361512359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17520367597099727919/17525000000000000000 : ℝ)*(X 1 0+X 2 0)+(120506082767/87625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (17520367597099727919/17525000000000000000 : ℝ)) (alpha := (120506082767/87625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17520367597099727919/17525000000000000000 : ℝ)*(X 0 1+X 2 1)+(120506082767/87625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (17520367597099727919/17525000000000000000 : ℝ)) (alpha := (120506082767/87625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17520367597099727919/17525000000000000000 : ℝ)*(X 0 2+X 1 2)+(120506082767/87625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (351/3125 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (17520367597099727919/17525000000000000000 : ℝ)) (alpha := (120506082767/87625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1005374679/5000000000 : ℝ)*X 0 0+(67633817/125000000 : ℝ)*X 0 1+(5245720157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674146549/5000000000 : ℝ)*X 1 0+(-261847607/1250000000 : ℝ)*X 1 1+(5245720151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674146547/5000000000 : ℝ)*X 2 0+(1311430041/2500000000 : ℝ)*X 2 1+(-418956169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4316523097/10000000000 : ℝ)*X 0 0+(1036117057/2500000000 : ℝ)*X 0 1+(4495119211/10000000000 : ℝ)*X 0 2+(4316523097/10000000000 : ℝ)*X 1 0+(1036117057/2500000000 : ℝ)*X 1 1+(4495119211/10000000000 : ℝ)*X 1 2+(4316523097/10000000000 : ℝ)*X 2 0+(1036117057/2500000000 : ℝ)*X 2 1+(4495119211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2010761147/10000000000 : ℝ)*X 0 0+(1311578203/2500000000 : ℝ)*X 0 1+(2705054819/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((8488979/16000000 : ℝ)*X 1 0+(-1930391359/10000000000 : ℝ)*X 1 1+(2705054821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326402971/2500000000 : ℝ)*X 2 0+(5410109637/10000000000 : ℝ)*X 2 1+(-1930391353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539568517/1250000000 : ℝ)*X 0 0+(2246929793/5000000000 : ℝ)*X 0 1+(1036433591/2500000000 : ℝ)*X 0 2+(539568517/1250000000 : ℝ)*X 1 0+(2246929793/5000000000 : ℝ)*X 1 1+(1036433591/2500000000 : ℝ)*X 1 2+(539568517/1250000000 : ℝ)*X 2 0+(2246929793/5000000000 : ℝ)*X 2 1+(1036433591/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1162299892138933379164572123/438125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469845021/100000000000000 : ℝ)*(base19) + (423096299/100000000000000 : ℝ)*(base23) + (22578119/100000000000000 : ℝ)*(lower2) + (32496273/50000000000000 : ℝ)*(upper3) + (370901/781250000000 : ℝ)*(upper5) + (2228254125458613/50000000000000 : ℝ)*(major0) + (2228254125458613/50000000000000 : ℝ)*(major1) + (2228254125458613/50000000000000 : ℝ)*(major2) + (1515289788766903/25000000000000 : ℝ)*(sp0) + (6061168098733933/100000000000000 : ℝ)*(sp1) + (1212233629096531/20000000000000 : ℝ)*(sp2) + (178240186728797/6250000000000 : ℝ)*(sp3) + (9413511343/100000000000000 : ℝ)*(sp4) + (4857164883/100000000000000 : ℝ)*(sp7) + (570369568965127/20000000000000 : ℝ)*(f.failure) + (1212233713715791/20000000000000 : ℝ)*(f.sum) + (28425528826993/17525000000000000000000000000 : ℝ)*base65 + (9069438736833183653/876250000000000000000000000000000 : ℝ)*base68 + (7609599465173183653/876250000000000000000000000000000 : ℝ)*base70 + (4767628454253183653/876250000000000000000000000000000 : ℝ)*base72 + (46509658304391/8762500000000000000000000000 : ℝ)*base74 + (3029182190754433653/876250000000000000000000000000000 : ℝ)*base76 + (8825533560923183653/876250000000000000000000000000000 : ℝ)*base78 + (4466259658563183653/876250000000000000000000000000000 : ℝ)*base80 + (59486690045357/17525000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (119053/15625000000000000000 : ℝ)*base89 + (119053/15625000000000000000 : ℝ)*base91 + (119053/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (251095971056930788417244097/43812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30751489/3125000000000 : ℝ)*(base19) + (1080718639/100000000000000 : ℝ)*(base23) + (23804139/20000000000000 : ℝ)*(upper3) + (7687909/20000000000000 : ℝ)*(lower4) + (122143913/100000000000000 : ℝ)*(upper5) + (448882665941379/10000000000000 : ℝ)*(major0) + (448882665941379/10000000000000 : ℝ)*(major1) + (448882665941379/10000000000000 : ℝ)*(major2) + (1273988203/6250000000000 : ℝ)*(sp1) + (11053613573/50000000000000 : ℝ)*(sp2) + (610512380355649/10000000000000 : ℝ)*(sp4) + (3052551217848797/50000000000000 : ℝ)*(sp5) + (381568788475669/6250000000000 : ℝ)*(sp6) + (2872529324232781/100000000000000 : ℝ)*(sp7) + (2872529324232781/100000000000000 : ℝ)*(f.failure) + (610512380355649/10000000000000 : ℝ)*(f.sum) + (307799743193/1752500000000000000000000000 : ℝ)*base66 + (1921280538144239699/175250000000000000000000000000000 : ℝ)*base68 + (832633299616260301/175250000000000000000000000000000 : ℝ)*base69 + (483043834474760301/175250000000000000000000000000000 : ℝ)*base71 + (1753737796779/876250000000000000000000000 : ℝ)*base74 + (677850891522260301/175250000000000000000000000000000 : ℝ)*base75 + (88268498173260301/175250000000000000000000000000000 : ℝ)*base77 + (252103978127760301/175250000000000000000000000000000 : ℝ)*base79 + (5190891195767/1752500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (685759/78125000000000000000 : ℝ)*base89 + (685759/78125000000000000000 : ℝ)*base91 + (685759/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1381_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1381_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1381_s7_0 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348281381/10000000000 : ℝ)*x 0 + (81965061/156250000 : ℝ)*x 1 + (-130921151/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348281381/10000000000 : ℝ)^4341 ≤ (44086998945271/100000000000000 : ℝ)^3317 := by
    have hnat : (5348281381 : ℕ)^4341*100000000000000^3317 ≤ 44086998945271^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348281381 10000000000 44086998945271 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81965061/156250000 : ℝ)^4341 ≤ (2686520504917/6250000000000 : ℝ)^3317 := by
    have hnat : (81965061 : ℕ)^4341*6250000000000^3317 ≤ 2686520504917^3317*156250000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81965061 156250000 2686520504917 6250000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130921151/625000000 : ℝ)^4341 ≤ (6464336476161/50000000000000 : ℝ)^3317 := by
    have hnat : (130921151 : ℕ)^4341*50000000000000^3317 ≤ 6464336476161^3317*625000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130921151 625000000 6464336476161 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348281381/10000000000 : ℝ), (81965061/156250000 : ℝ), (-130921151/625000000 : ℝ)] ![(44086998945271/100000000000000 : ℝ), (2686520504917/6250000000000 : ℝ), (6464336476161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348281381/10000000000 : ℝ)|^4341 ≤ (44086998945271/100000000000000 : ℝ)^3317
        have hw : |(5348281381/10000000000 : ℝ)|=(5348281381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81965061/156250000 : ℝ)|^4341 ≤ (2686520504917/6250000000000 : ℝ)^3317
        have hw : |(81965061/156250000 : ℝ)|=(81965061/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130921151/625000000 : ℝ)|^4341 ≤ (6464336476161/50000000000000 : ℝ)^3317
        have hw : |(-130921151/625000000 : ℝ)|=(130921151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s7_1 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010765591/10000000000 : ℝ)*x 0 + (5246355889/10000000000 : ℝ)*x 1 + (5410063693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010765591/10000000000 : ℝ)^4341 ≤ (12254632191613/100000000000000 : ℝ)^3317 := by
    have hnat : (2010765591 : ℕ)^4341*100000000000000^3317 ≤ 12254632191613^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010765591 10000000000 12254632191613 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246355889/10000000000 : ℝ)^4341 ≤ (8598135294859/20000000000000 : ℝ)^3317 := by
    have hnat : (5246355889 : ℕ)^4341*20000000000000^3317 ≤ 8598135294859^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246355889 10000000000 8598135294859 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410063693/10000000000 : ℝ)^4341 ≤ (22377345655307/50000000000000 : ℝ)^3317 := by
    have hnat : (5410063693 : ℕ)^4341*50000000000000^3317 ≤ 22377345655307^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410063693 10000000000 22377345655307 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010765591/10000000000 : ℝ), (5246355889/10000000000 : ℝ), (5410063693/10000000000 : ℝ)] ![(12254632191613/100000000000000 : ℝ), (8598135294859/20000000000000 : ℝ), (22377345655307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010765591/10000000000 : ℝ)|^4341 ≤ (12254632191613/100000000000000 : ℝ)^3317
        have hw : |(-2010765591/10000000000 : ℝ)|=(2010765591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246355889/10000000000 : ℝ)|^4341 ≤ (8598135294859/20000000000000 : ℝ)^3317
        have hw : |(5246355889/10000000000 : ℝ)|=(5246355889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410063693/10000000000 : ℝ)|^4341 ≤ (22377345655307/50000000000000 : ℝ)^3317
        have hw : |(5410063693/10000000000 : ℝ)|=(5410063693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s7_2 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82900367/156250000 : ℝ)*x 0 + (-965219329/5000000000 : ℝ)*x 1 + (676257961/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82900367/156250000 : ℝ)^4341 ≤ (349018988479/800000000000 : ℝ)^3317 := by
    have hnat : (82900367 : ℕ)^4341*800000000000^3317 ≤ 349018988479^3317*156250000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82900367 156250000 349018988479 800000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965219329/5000000000 : ℝ)^4341 ≤ (5808967580809/50000000000000 : ℝ)^3317 := by
    have hnat : (965219329 : ℕ)^4341*50000000000000^3317 ≤ 5808967580809^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965219329 5000000000 5808967580809 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676257961/1250000000 : ℝ)^4341 ≤ (44754691256483/100000000000000 : ℝ)^3317 := by
    have hnat : (676257961 : ℕ)^4341*100000000000000^3317 ≤ 44754691256483^3317*1250000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676257961 1250000000 44754691256483 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82900367/156250000 : ℝ), (-965219329/5000000000 : ℝ), (676257961/1250000000 : ℝ)] ![(349018988479/800000000000 : ℝ), (5808967580809/50000000000000 : ℝ), (44754691256483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82900367/156250000 : ℝ)|^4341 ≤ (349018988479/800000000000 : ℝ)^3317
        have hw : |(82900367/156250000 : ℝ)|=(82900367/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-965219329/5000000000 : ℝ)|^4341 ≤ (5808967580809/50000000000000 : ℝ)^3317
        have hw : |(-965219329/5000000000 : ℝ)|=(965219329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676257961/1250000000 : ℝ)|^4341 ≤ (44754691256483/100000000000000 : ℝ)^3317
        have hw : |(676257961/1250000000 : ℝ)|=(676257961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s7_3 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061124697/2000000000 : ℝ)*x 0 + (2705031847/5000000000 : ℝ)*x 1 + (-386087731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061124697/2000000000 : ℝ)^4341 ≤ (43627373527591/100000000000000 : ℝ)^3317 := by
    have hnat : (1061124697 : ℕ)^4341*100000000000000^3317 ≤ 43627373527591^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061124697 2000000000 43627373527591 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705031847/5000000000 : ℝ)^4341 ≤ (279716820759/625000000000 : ℝ)^3317 := by
    have hnat : (2705031847 : ℕ)^4341*625000000000^3317 ≤ 279716820759^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705031847 5000000000 279716820759 625000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (386087731/2000000000 : ℝ)^4341 ≤ (1161793513799/10000000000000 : ℝ)^3317 := by
    have hnat : (386087731 : ℕ)^4341*10000000000000^3317 ≤ 1161793513799^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386087731 2000000000 1161793513799 10000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061124697/2000000000 : ℝ), (2705031847/5000000000 : ℝ), (-386087731/2000000000 : ℝ)] ![(43627373527591/100000000000000 : ℝ), (279716820759/625000000000 : ℝ), (1161793513799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061124697/2000000000 : ℝ)|^4341 ≤ (43627373527591/100000000000000 : ℝ)^3317
        have hw : |(1061124697/2000000000 : ℝ)|=(1061124697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705031847/5000000000 : ℝ)|^4341 ≤ (279716820759/625000000000 : ℝ)^3317
        have hw : |(2705031847/5000000000 : ℝ)|=(2705031847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-386087731/2000000000 : ℝ)|^4341 ≤ (1161793513799/10000000000000 : ℝ)^3317
        have hw : |(-386087731/2000000000 : ℝ)|=(386087731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s7_4 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863310257/2000000000 : ℝ)*x 0 + (4493764593/10000000000 : ℝ)*x 1 + (4145828561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863310257/2000000000 : ℝ)^4341 ≤ (4163025296259/12500000000000 : ℝ)^3317 := by
    have hnat : (863310257 : ℕ)^4341*12500000000000^3317 ≤ 4163025296259^3317*2000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863310257 2000000000 4163025296259 12500000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493764593/10000000000 : ℝ)^4341 ≤ (8776204263773/25000000000000 : ℝ)^3317 := by
    have hnat : (4493764593 : ℕ)^4341*25000000000000^3317 ≤ 8776204263773^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493764593 10000000000 8776204263773 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4145828561/10000000000 : ℝ)^4341 ≤ (31590980549767/100000000000000 : ℝ)^3317 := by
    have hnat : (4145828561 : ℕ)^4341*100000000000000^3317 ≤ 31590980549767^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145828561 10000000000 31590980549767 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863310257/2000000000 : ℝ), (4493764593/10000000000 : ℝ), (4145828561/10000000000 : ℝ)] ![(4163025296259/12500000000000 : ℝ), (8776204263773/25000000000000 : ℝ), (31590980549767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863310257/2000000000 : ℝ)|^4341 ≤ (4163025296259/12500000000000 : ℝ)^3317
        have hw : |(863310257/2000000000 : ℝ)|=(863310257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493764593/10000000000 : ℝ)|^4341 ≤ (8776204263773/25000000000000 : ℝ)^3317
        have hw : |(4493764593/10000000000 : ℝ)|=(4493764593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4145828561/10000000000 : ℝ)|^4341 ≤ (31590980549767/100000000000000 : ℝ)^3317
        have hw : |(4145828561/10000000000 : ℝ)|=(4145828561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1381_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5619/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1473/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5619/50000 : ℝ) ^ (1085/256 : ℝ) ≤ (4737215158159713/50000000000000000000 : ℝ) := by
    have hpowers : (5619/50000 : ℝ)^1085 ≤ (4737215158159713/50000000000000000000 : ℝ)^256 := by
      have hnat : (5619 : ℕ)^1085*50000000000000000000^256 ≤ 4737215158159713^256*50000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5619 50000 4737215158159713 50000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5619/50000 : ℝ)) (X := (4737215158159713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14731/100000 : ℝ) ^ (1085/256 : ℝ) ≤ (14917782068673213/50000000000000000000 : ℝ) := by
    have hpowers : (14731/100000 : ℝ)^1085 ≤ (14917782068673213/50000000000000000000 : ℝ)^256 := by
      have hnat : (14731 : ℕ)^1085*50000000000000000000^256 ≤ 14917782068673213^256*100000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14731 100000 14917782068673213 50000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14731/100000 : ℝ)) (X := (14917782068673213/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004737215158159713/25000000000000000000 : ℝ) ≤ (10000447055963537/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (25004737215158159713/25000000000000000000 : ℝ)^256 ≤ (10000447055963537/10000000000000000 : ℝ)^1085 := by
      have hnat : (25004737215158159713 : ℕ)^256*10000000000000000^1085 ≤ 10000447055963537^1085*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004737215158159713 25000000000000000000 10000447055963537 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000447055963537/10000000000000000 : ℝ)) (X := (25004737215158159713/25000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009827498613416463/25000000000000000000 : ℝ) ≤ (10000927359231707/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (25009827498613416463/25000000000000000000 : ℝ)^256 ≤ (10000927359231707/10000000000000000 : ℝ)^1085 := by
      have hnat : (25009827498613416463 : ℕ)^256*10000000000000000^1085 ≤ 10000927359231707^1085*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009827498613416463 25000000000000000000 10000927359231707 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000927359231707/10000000000000000 : ℝ)) (X := (25009827498613416463/25000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014917782068673213/25000000000000000000 : ℝ) ≤ (10001407662499877/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (25014917782068673213/25000000000000000000 : ℝ)^256 ≤ (10001407662499877/10000000000000000 : ℝ)^1085 := by
      have hnat : (25014917782068673213 : ℕ)^256*10000000000000000^1085 ≤ 10001407662499877^1085*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014917782068673213 25000000000000000000 10001407662499877 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001407662499877/10000000000000000 : ℝ)) (X := (25014917782068673213/25000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4737215158159713/50000000000000000000 : ℝ) ≤ ((34920766270225245821/34930000000000000000 : ℝ)+2*(48030326817/34930000000000 : ℝ)*(5619/50000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (34920766270225245821/34930000000000000000 : ℝ)+2*(48030326817/34930000000000 : ℝ)*(5619/50000 : ℝ)=(10000447055963537/10000000000000000 : ℝ) by norm_num, show 1+2*(4737215158159713/50000000000000000000 : ℝ)=(25004737215158159713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14917782068673213/50000000000000000000 : ℝ)+(4737215158159713/50000000000000000000 : ℝ) ≤ ((34920766270225245821/34930000000000000000 : ℝ)+(48030326817/34930000000000 : ℝ)*((14731/100000 : ℝ)+(5619/50000 : ℝ)))^(1085/256 : ℝ) := by
    rw [show (34920766270225245821/34930000000000000000 : ℝ)+(48030326817/34930000000000 : ℝ)*((14731/100000 : ℝ)+(5619/50000 : ℝ))=(10000927359231707/10000000000000000 : ℝ) by norm_num, show 1+(14917782068673213/50000000000000000000 : ℝ)+(4737215158159713/50000000000000000000 : ℝ)=(25009827498613416463/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14917782068673213/50000000000000000000 : ℝ) ≤ ((34920766270225245821/34930000000000000000 : ℝ)+2*(48030326817/34930000000000 : ℝ)*(14731/100000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (34920766270225245821/34930000000000000000 : ℝ)+2*(48030326817/34930000000000 : ℝ)*(14731/100000 : ℝ)=(10001407662499877/10000000000000000 : ℝ) by norm_num, show 1+2*(14917782068673213/50000000000000000000 : ℝ)=(25014917782068673213/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34920766270225245821/34930000000000000000 : ℝ)*(X 1 0+X 2 0)+(48030326817/34930000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (34920766270225245821/34930000000000000000 : ℝ)) (alpha := (48030326817/34930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34920766270225245821/34930000000000000000 : ℝ)*(X 0 1+X 2 1)+(48030326817/34930000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (34920766270225245821/34930000000000000000 : ℝ)) (alpha := (48030326817/34930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34920766270225245821/34930000000000000000 : ℝ)*(X 0 2+X 1 2)+(48030326817/34930000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (34920766270225245821/34930000000000000000 : ℝ)) (alpha := (48030326817/34930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5348281381/10000000000 : ℝ)*X 2 0+(81965061/156250000 : ℝ)*X 2 1+(-130921151/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2010765591/10000000000 : ℝ)*X 0 0+(5246355889/10000000000 : ℝ)*X 0 1+(5410063693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((82900367/156250000 : ℝ)*X 1 0+(-965219329/5000000000 : ℝ)*X 1 1+(676257961/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061124697/2000000000 : ℝ)*X 2 0+(2705031847/5000000000 : ℝ)*X 2 1+(-386087731/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((863310257/2000000000 : ℝ)*X 0 0+(4493764593/10000000000 : ℝ)*X 0 1+(4145828561/10000000000 : ℝ)*X 0 2+(863310257/2000000000 : ℝ)*X 1 0+(4493764593/10000000000 : ℝ)*X 1 1+(4145828561/10000000000 : ℝ)*X 1 2+(863310257/2000000000 : ℝ)*X 2 0+(4493764593/10000000000 : ℝ)*X 2 1+(4145828561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4811646045789068764438391211/873250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185992529/20000000000000 : ℝ)*(base19) + (257890159/25000000000000 : ℝ)*(base23) + (155791379/50000000000000 : ℝ)*(lower1) + (3506561/3125000000000 : ℝ)*(upper3) + (11803067/25000000000000 : ℝ)*(lower4) + (56558559/50000000000000 : ℝ)*(upper5) + (2245626659997197/50000000000000 : ℝ)*(major0) + (2245626659997197/50000000000000 : ℝ)*(major1) + (2245626659997197/50000000000000 : ℝ)*(major2) + (999149913/50000000000000 : ℝ)*(sp0) + (381776515135411/6250000000000 : ℝ)*(sp1) + (6108423312203931/100000000000000 : ℝ)*(sp2) + (3054210606153057/50000000000000 : ℝ)*(sp3) + (1437041107077027/50000000000000 : ℝ)*(sp4) + (1437041107077027/50000000000000 : ℝ)*(f.failure) + (381776515135411/6250000000000 : ℝ)*(f.sum) + (8192727835193/1746500000000000000000000000 : ℝ)*base66 + (103565574444245963737/1746500000000000000000000000000000 : ℝ)*base67 + (316886235061963737/1746500000000000000000000000000000 : ℝ)*base69 + (26799498510542036263/1746500000000000000000000000000000 : ℝ)*base72 + (217427815441/873250000000000000000000000 : ℝ)*base73 + (160148446581678036263/1746500000000000000000000000000000 : ℝ)*base76 + (7831278394704036263/1746500000000000000000000000000000 : ℝ)*base78 + (21919297439608036263/1746500000000000000000000000000000 : ℝ)*base80 + (715408596963/873250000000000000000000000 : ℝ)*base81 + (409403/39062500000000000000 : ℝ)*base89 + (409403/39062500000000000000 : ℝ)*base91 + (409403/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1381_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1381_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1381_s8_0 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010756623/10000000000 : ℝ)*x 0 + (5410653567/10000000000 : ℝ)*x 1 + (5245767043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010756623/10000000000 : ℝ)^4341 ≤ (12254560663223/100000000000000 : ℝ)^3317 := by
    have hnat : (2010756623 : ℕ)^4341*100000000000000^3317 ≤ 12254560663223^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010756623 10000000000 12254560663223 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410653567/10000000000 : ℝ)^4341 ≤ (44761077577517/100000000000000 : ℝ)^3317 := by
    have hnat : (5410653567 : ℕ)^4341*100000000000000^3317 ≤ 44761077577517^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410653567 10000000000 44761077577517 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245767043/10000000000 : ℝ)^4341 ≤ (10746090435113/25000000000000 : ℝ)^3317 := by
    have hnat : (5245767043 : ℕ)^4341*25000000000000^3317 ≤ 10746090435113^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245767043 10000000000 10746090435113 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010756623/10000000000 : ℝ), (5410653567/10000000000 : ℝ), (5245767043/10000000000 : ℝ)] ![(12254560663223/100000000000000 : ℝ), (44761077577517/100000000000000 : ℝ), (10746090435113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010756623/10000000000 : ℝ)|^4341 ≤ (12254560663223/100000000000000 : ℝ)^3317
        have hw : |(-2010756623/10000000000 : ℝ)|=(2010756623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410653567/10000000000 : ℝ)|^4341 ≤ (44761077577517/100000000000000 : ℝ)^3317
        have hw : |(5410653567/10000000000 : ℝ)|=(5410653567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245767043/10000000000 : ℝ)|^4341 ≤ (10746090435113/25000000000000 : ℝ)^3317
        have hw : |(5245767043/10000000000 : ℝ)|=(5245767043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s8_1 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348279193/10000000000 : ℝ)*x 0 + (-104736861/500000000 : ℝ)*x 1 + (5245767007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348279193/10000000000 : ℝ)^4341 ≤ (44086975341147/100000000000000 : ℝ)^3317 := by
    have hnat : (5348279193 : ℕ)^4341*100000000000000^3317 ≤ 44086975341147^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348279193 10000000000 44086975341147 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104736861/500000000 : ℝ)^4341 ≤ (6464331645911/50000000000000 : ℝ)^3317 := by
    have hnat : (104736861 : ℕ)^4341*50000000000000^3317 ≤ 6464331645911^3317*500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104736861 500000000 6464331645911 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245767007/10000000000 : ℝ)^4341 ≤ (21492180677199/50000000000000 : ℝ)^3317 := by
    have hnat : (5245767007 : ℕ)^4341*50000000000000^3317 ≤ 21492180677199^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245767007 10000000000 21492180677199 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348279193/10000000000 : ℝ), (-104736861/500000000 : ℝ), (5245767007/10000000000 : ℝ)] ![(44086975341147/100000000000000 : ℝ), (6464331645911/50000000000000 : ℝ), (21492180677199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348279193/10000000000 : ℝ)|^4341 ≤ (44086975341147/100000000000000 : ℝ)^3317
        have hw : |(5348279193/10000000000 : ℝ)|=(5348279193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104736861/500000000 : ℝ)|^4341 ≤ (6464331645911/50000000000000 : ℝ)^3317
        have hw : |(-104736861/500000000 : ℝ)|=(104736861/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245767007/10000000000 : ℝ)|^4341 ≤ (21492180677199/50000000000000 : ℝ)^3317
        have hw : |(5245767007/10000000000 : ℝ)|=(5245767007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s8_2 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668534931/1250000000 : ℝ)*x 0 + (1311441717/2500000000 : ℝ)*x 1 + (-2094737063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668534931/1250000000 : ℝ)^4341 ≤ (11021744523021/25000000000000 : ℝ)^3317 := by
    have hnat : (668534931 : ℕ)^4341*25000000000000^3317 ≤ 11021744523021^3317*1250000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668534931 1250000000 11021744523021 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311441717/2500000000 : ℝ)^4341 ≤ (42984359863799/100000000000000 : ℝ)^3317 := by
    have hnat : (1311441717 : ℕ)^4341*100000000000000^3317 ≤ 42984359863799^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311441717 2500000000 42984359863799 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2094737063/10000000000 : ℝ)^4341 ≤ (5050258603/39062500000 : ℝ)^3317 := by
    have hnat : (2094737063 : ℕ)^4341*39062500000^3317 ≤ 5050258603^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094737063 10000000000 5050258603 39062500000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668534931/1250000000 : ℝ), (1311441717/2500000000 : ℝ), (-2094737063/10000000000 : ℝ)] ![(11021744523021/25000000000000 : ℝ), (42984359863799/100000000000000 : ℝ), (5050258603/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668534931/1250000000 : ℝ)|^4341 ≤ (11021744523021/25000000000000 : ℝ)^3317
        have hw : |(668534931/1250000000 : ℝ)|=(668534931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311441717/2500000000 : ℝ)|^4341 ≤ (42984359863799/100000000000000 : ℝ)^3317
        have hw : |(1311441717/2500000000 : ℝ)|=(1311441717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2094737063/10000000000 : ℝ)|^4341 ≤ (5050258603/39062500000 : ℝ)^3317
        have hw : |(-2094737063/10000000000 : ℝ)|=(2094737063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s8_3 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158263269/5000000000 : ℝ)*x 0 + (4144572729/10000000000 : ℝ)*x 1 + (4495013899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158263269/5000000000 : ℝ)^4341 ≤ (33303952491727/100000000000000 : ℝ)^3317 := by
    have hnat : (2158263269 : ℕ)^4341*100000000000000^3317 ≤ 33303952491727^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158263269 5000000000 33303952491727 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4144572729/10000000000 : ℝ)^4341 ≤ (6315691516079/20000000000000 : ℝ)^3317 := by
    have hnat : (4144572729 : ℕ)^4341*20000000000000^3317 ≤ 6315691516079^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144572729 10000000000 6315691516079 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495013899/10000000000 : ℝ)^4341 ≤ (7023517983131/20000000000000 : ℝ)^3317 := by
    have hnat : (4495013899 : ℕ)^4341*20000000000000^3317 ≤ 7023517983131^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495013899 10000000000 7023517983131 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158263269/5000000000 : ℝ), (4144572729/10000000000 : ℝ), (4495013899/10000000000 : ℝ)] ![(33303952491727/100000000000000 : ℝ), (6315691516079/20000000000000 : ℝ), (7023517983131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158263269/5000000000 : ℝ)|^4341 ≤ (33303952491727/100000000000000 : ℝ)^3317
        have hw : |(2158263269/5000000000 : ℝ)|=(2158263269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4144572729/10000000000 : ℝ)|^4341 ≤ (6315691516079/20000000000000 : ℝ)^3317
        have hw : |(4144572729/10000000000 : ℝ)|=(4144572729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495013899/10000000000 : ℝ)|^4341 ≤ (7023517983131/20000000000000 : ℝ)^3317
        have hw : |(4495013899/10000000000 : ℝ)|=(4495013899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s8_4 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010768449/10000000000 : ℝ)*x 0 + (5246358797/10000000000 : ℝ)*x 1 + (5410058707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010768449/10000000000 : ℝ)^4341 ≤ (12254654986921/100000000000000 : ℝ)^3317 := by
    have hnat : (2010768449 : ℕ)^4341*100000000000000^3317 ≤ 12254654986921^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010768449 10000000000 12254654986921 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246358797/10000000000 : ℝ)^4341 ≤ (2149535382999/5000000000000 : ℝ)^3317 := by
    have hnat : (5246358797 : ℕ)^4341*5000000000000^3317 ≤ 2149535382999^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246358797 10000000000 2149535382999 5000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410058707/10000000000 : ℝ)^4341 ≤ (8950927466127/20000000000000 : ℝ)^3317 := by
    have hnat : (5410058707 : ℕ)^4341*20000000000000^3317 ≤ 8950927466127^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410058707 10000000000 8950927466127 20000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010768449/10000000000 : ℝ), (5246358797/10000000000 : ℝ), (5410058707/10000000000 : ℝ)] ![(12254654986921/100000000000000 : ℝ), (2149535382999/5000000000000 : ℝ), (8950927466127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010768449/10000000000 : ℝ)|^4341 ≤ (12254654986921/100000000000000 : ℝ)^3317
        have hw : |(-2010768449/10000000000 : ℝ)|=(2010768449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246358797/10000000000 : ℝ)|^4341 ≤ (2149535382999/5000000000000 : ℝ)^3317
        have hw : |(5246358797/10000000000 : ℝ)|=(5246358797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410058707/10000000000 : ℝ)|^4341 ≤ (8950927466127/20000000000000 : ℝ)^3317
        have hw : |(5410058707/10000000000 : ℝ)|=(5410058707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s8_5 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652811861/5000000000 : ℝ)*x 0 + (-965222733/5000000000 : ℝ)*x 1 + (676257313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652811861/5000000000 : ℝ)^4341 ≤ (2726711004877/6250000000000 : ℝ)^3317 := by
    have hnat : (2652811861 : ℕ)^4341*6250000000000^3317 ≤ 2726711004877^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652811861 5000000000 2726711004877 6250000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965222733/5000000000 : ℝ)^4341 ≤ (11617988782881/100000000000000 : ℝ)^3317 := by
    have hnat : (965222733 : ℕ)^4341*100000000000000^3317 ≤ 11617988782881^3317*5000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965222733 5000000000 11617988782881 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676257313/1250000000 : ℝ)^4341 ≤ (22377317566447/50000000000000 : ℝ)^3317 := by
    have hnat : (676257313 : ℕ)^4341*50000000000000^3317 ≤ 22377317566447^3317*1250000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676257313 1250000000 22377317566447 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652811861/5000000000 : ℝ), (-965222733/5000000000 : ℝ), (676257313/1250000000 : ℝ)] ![(2726711004877/6250000000000 : ℝ), (11617988782881/100000000000000 : ℝ), (22377317566447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652811861/5000000000 : ℝ)|^4341 ≤ (2726711004877/6250000000000 : ℝ)^3317
        have hw : |(2652811861/5000000000 : ℝ)|=(2652811861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-965222733/5000000000 : ℝ)|^4341 ≤ (11617988782881/100000000000000 : ℝ)^3317
        have hw : |(-965222733/5000000000 : ℝ)|=(965222733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676257313/1250000000 : ℝ)|^4341 ≤ (22377317566447/50000000000000 : ℝ)^3317
        have hw : |(676257313/1250000000 : ℝ)|=(676257313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1381_s8_6 (p : ℝ) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4316551361/10000000000 : ℝ)*x 0 + (4493756143/10000000000 : ℝ)*x 1 + (1036459287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316551361/10000000000 : ℝ)^4341 ≤ (8326050784367/25000000000000 : ℝ)^3317 := by
    have hnat : (4316551361 : ℕ)^4341*25000000000000^3317 ≤ 8326050784367^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316551361 10000000000 8326050784367 25000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493756143/10000000000 : ℝ)^4341 ≤ (35104730666321/100000000000000 : ℝ)^3317 := by
    have hnat : (4493756143 : ℕ)^4341*100000000000000^3317 ≤ 35104730666321^3317*10000000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493756143 10000000000 35104730666321 100000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036459287/2500000000 : ℝ)^4341 ≤ (15795533091041/50000000000000 : ℝ)^3317 := by
    have hnat : (1036459287 : ℕ)^4341*50000000000000^3317 ≤ 15795533091041^3317*2500000000^4341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036459287 2500000000 15795533091041 50000000000000 4341 3317 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4341/1024 : ℝ)) 4341 3317 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316551361/10000000000 : ℝ), (4493756143/10000000000 : ℝ), (1036459287/2500000000 : ℝ)] ![(8326050784367/25000000000000 : ℝ), (35104730666321/100000000000000 : ℝ), (15795533091041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316551361/10000000000 : ℝ)|^4341 ≤ (8326050784367/25000000000000 : ℝ)^3317
        have hw : |(4316551361/10000000000 : ℝ)|=(4316551361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493756143/10000000000 : ℝ)|^4341 ≤ (35104730666321/100000000000000 : ℝ)^3317
        have hw : |(4493756143/10000000000 : ℝ)|=(4493756143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036459287/2500000000 : ℝ)|^4341 ≤ (15795533091041/50000000000000 : ℝ)^3317
        have hw : |(1036459287/2500000000 : ℝ)|=(1036459287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1381_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11239/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1473/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5619/50000 : ℝ) ^ (1085/256 : ℝ) ≤ (4737215158159713/50000000000000000000 : ℝ) := by
    have hpowers : (5619/50000 : ℝ)^1085 ≤ (4737215158159713/50000000000000000000 : ℝ)^256 := by
      have hnat : (5619 : ℕ)^1085*50000000000000000000^256 ≤ 4737215158159713^256*50000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5619 50000 4737215158159713 50000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5619/50000 : ℝ)) (X := (4737215158159713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1473/10000 : ℝ) ^ (1085/256 : ℝ) ≤ (29826981039525473/100000000000000000000 : ℝ) := by
    have hpowers : (1473/10000 : ℝ)^1085 ≤ (29826981039525473/100000000000000000000 : ℝ)^256 := by
      have hnat : (1473 : ℕ)^1085*100000000000000000000^256 ≤ 29826981039525473^256*10000^1085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1473 10000 29826981039525473 100000000000000000000 1085 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1473/10000 : ℝ)) (X := (29826981039525473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004737215158159713/25000000000000000000 : ℝ) ≤ (10000447055963537/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (25004737215158159713/25000000000000000000 : ℝ)^256 ≤ (10000447055963537/10000000000000000 : ℝ)^1085 := by
      have hnat : (25004737215158159713 : ℕ)^256*10000000000000000^1085 ≤ 10000447055963537^1085*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004737215158159713 25000000000000000000 10000447055963537 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000447055963537/10000000000000000 : ℝ)) (X := (25004737215158159713/25000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039301411355844899/100000000000000000000 : ℝ) ≤ (500046357838943/500000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (100039301411355844899/100000000000000000000 : ℝ)^256 ≤ (500046357838943/500000000000000 : ℝ)^1085 := by
      have hnat : (100039301411355844899 : ℕ)^256*500000000000000^1085 ≤ 500046357838943^1085*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039301411355844899 100000000000000000000 500046357838943 500000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500046357838943/500000000000000 : ℝ)) (X := (100039301411355844899/100000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029826981039525473/50000000000000000000 : ℝ) ≤ (10001407257594183/10000000000000000 : ℝ) ^ (1085/256 : ℝ) := by
    have hpowers : (50029826981039525473/50000000000000000000 : ℝ)^256 ≤ (10001407257594183/10000000000000000 : ℝ)^1085 := by
      have hnat : (50029826981039525473 : ℕ)^256*10000000000000000^1085 ≤ 10001407257594183^1085*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029826981039525473 50000000000000000000 10001407257594183 10000000000000000 256 1085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001407257594183/10000000000000000 : ℝ)) (X := (50029826981039525473/50000000000000000000 : ℝ)) (by norm_num) 1085 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4737215158159713/50000000000000000000 : ℝ) ≤ ((363653858057286161/363750000000000000 : ℝ)+2*(480100815323/349200000000000 : ℝ)*(5619/50000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (363653858057286161/363750000000000000 : ℝ)+2*(480100815323/349200000000000 : ℝ)*(5619/50000 : ℝ)=(10000447055963537/10000000000000000 : ℝ) by norm_num, show 1+2*(4737215158159713/50000000000000000000 : ℝ)=(25004737215158159713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29826981039525473/100000000000000000000 : ℝ)+(4737215158159713/50000000000000000000 : ℝ) ≤ ((363653858057286161/363750000000000000 : ℝ)+(480100815323/349200000000000 : ℝ)*((1473/10000 : ℝ)+(5619/50000 : ℝ)))^(1085/256 : ℝ) := by
    rw [show (363653858057286161/363750000000000000 : ℝ)+(480100815323/349200000000000 : ℝ)*((1473/10000 : ℝ)+(5619/50000 : ℝ))=(500046357838943/500000000000000 : ℝ) by norm_num, show 1+(29826981039525473/100000000000000000000 : ℝ)+(4737215158159713/50000000000000000000 : ℝ)=(100039301411355844899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29826981039525473/100000000000000000000 : ℝ) ≤ ((363653858057286161/363750000000000000 : ℝ)+2*(480100815323/349200000000000 : ℝ)*(1473/10000 : ℝ))^(1085/256 : ℝ) := by
    rw [show (363653858057286161/363750000000000000 : ℝ)+2*(480100815323/349200000000000 : ℝ)*(1473/10000 : ℝ)=(10001407257594183/10000000000000000 : ℝ) by norm_num, show 1+2*(29826981039525473/100000000000000000000 : ℝ)=(50029826981039525473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (363653858057286161/363750000000000000 : ℝ)*(X 1 0+X 2 0)+(480100815323/349200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (363653858057286161/363750000000000000 : ℝ)) (alpha := (480100815323/349200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (363653858057286161/363750000000000000 : ℝ)*(X 0 1+X 2 1)+(480100815323/349200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (363653858057286161/363750000000000000 : ℝ)) (alpha := (480100815323/349200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (363653858057286161/363750000000000000 : ℝ)*(X 0 2+X 1 2)+(480100815323/349200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1085/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (363653858057286161/363750000000000000 : ℝ)) (alpha := (480100815323/349200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2010756623/10000000000 : ℝ)*X 0 0+(5410653567/10000000000 : ℝ)*X 0 1+(5245767043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348279193/10000000000 : ℝ)*X 1 0+(-104736861/500000000 : ℝ)*X 1 1+(5245767007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668534931/1250000000 : ℝ)*X 2 0+(1311441717/2500000000 : ℝ)*X 2 1+(-2094737063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158263269/5000000000 : ℝ)*X 0 0+(4144572729/10000000000 : ℝ)*X 0 1+(4495013899/10000000000 : ℝ)*X 0 2+(2158263269/5000000000 : ℝ)*X 1 0+(4144572729/10000000000 : ℝ)*X 1 1+(4495013899/10000000000 : ℝ)*X 1 2+(2158263269/5000000000 : ℝ)*X 2 0+(4144572729/10000000000 : ℝ)*X 2 1+(4495013899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2010768449/10000000000 : ℝ)*X 0 0+(5246358797/10000000000 : ℝ)*X 0 1+(5410058707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652811861/5000000000 : ℝ)*X 1 0+(-965222733/5000000000 : ℝ)*X 1 1+(676257313/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4316551361/10000000000 : ℝ)*X 0 0+(4493756143/10000000000 : ℝ)*X 0 1+(1036459287/2500000000 : ℝ)*X 0 2+(4316551361/10000000000 : ℝ)*X 1 0+(4493756143/10000000000 : ℝ)*X 1 1+(1036459287/2500000000 : ℝ)*X 1 2+(4316551361/10000000000 : ℝ)*X 2 0+(4493756143/10000000000 : ℝ)*X 2 1+(1036459287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1381_s8_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9718662326869075773622091/3031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (211835741/100000000000000 : ℝ)*(base19) + (394623093/100000000000000 : ℝ)*(base23) + (67650607/100000000000000 : ℝ)*(lower2) + (35672481/50000000000000 : ℝ)*(upper5) + (2229583604134627/50000000000000 : ℝ)*(major0) + (2229583604134627/50000000000000 : ℝ)*(major1) + (2229583604134627/50000000000000 : ℝ)*(major2) + (3032388799128387/50000000000000 : ℝ)*(sp0) + (6064782187539787/100000000000000 : ℝ)*(sp1) + (6064784526909327/100000000000000 : ℝ)*(sp2) + (178346712048921/6250000000000 : ℝ)*(sp3) + (1464655129/20000000000000 : ℝ)*(sp4) + (630539223/25000000000000 : ℝ)*(sp5) + (997675727/50000000000000 : ℝ)*(sp6) + (285354938813419/10000000000000 : ℝ)*(f.failure) + (303239246076621/5000000000000 : ℝ)*(f.sum) + (18717715730629/8730000000000000000000000000 : ℝ)*base66 + (240632407960534267/27281250000000000000000000000000 : ℝ)*base68 + (74406408490909267/27281250000000000000000000000000 : ℝ)*base70 + (574683686045659267/27281250000000000000000000000000 : ℝ)*base72 + (35865413939899/8730000000000000000000000000 : ℝ)*base74 + (260934501582784267/27281250000000000000000000000000 : ℝ)*base76 + (113108604739815517/27281250000000000000000000000000 : ℝ)*base78 + (289470371774565517/27281250000000000000000000000000 : ℝ)*base80 + (32955788756629/8730000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (169791/7812500000000000000 : ℝ)*base89 + (169791/7812500000000000000 : ℝ)*base91 + (169791/7812500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1381_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1381_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1381_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1381_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1381_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1381_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1085/256 : ℝ) ≤ p) (hpb : p ≤ (4341/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1220839/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1381_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

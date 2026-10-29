-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1449_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:56.768995+00:00
-- url     : https://prove2.me/submissions/0f055e01-6e20-4f3c-bcaf-c980eedf6424

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
theorem support_rectangle_w1449_s3_0 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1954077131/10000000000 : ℝ)*x 0 + (5415309827/10000000000 : ℝ)*x 1 + (523983451/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1954077131/10000000000 : ℝ)^4409 ≤ (1192459703243/10000000000000 : ℝ)^3385 := by
    have hnat : (1954077131 : ℕ)^4409*10000000000000^3385 ≤ 1192459703243^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954077131 10000000000 1192459703243 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415309827/10000000000 : ℝ)^4409 ≤ (44982274245189/100000000000000 : ℝ)^3385 := by
    have hnat : (5415309827 : ℕ)^4409*100000000000000^3385 ≤ 44982274245189^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415309827 10000000000 44982274245189 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523983451/1000000000 : ℝ)^4409 ≤ (43093128714177/100000000000000 : ℝ)^3385 := by
    have hnat : (523983451 : ℕ)^4409*100000000000000^3385 ≤ 43093128714177^3385*1000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523983451 1000000000 43093128714177 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1954077131/10000000000 : ℝ), (5415309827/10000000000 : ℝ), (523983451/1000000000 : ℝ)] ![(1192459703243/10000000000000 : ℝ), (44982274245189/100000000000000 : ℝ), (43093128714177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1954077131/10000000000 : ℝ)|^4409 ≤ (1192459703243/10000000000000 : ℝ)^3385
        have hw : |(-1954077131/10000000000 : ℝ)|=(1954077131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415309827/10000000000 : ℝ)|^4409 ≤ (44982274245189/100000000000000 : ℝ)^3385
        have hw : |(5415309827/10000000000 : ℝ)|=(5415309827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523983451/1000000000 : ℝ)|^4409 ≤ (43093128714177/100000000000000 : ℝ)^3385
        have hw : |(523983451/1000000000 : ℝ)|=(523983451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s3_1 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349001691/10000000000 : ℝ)*x 0 + (-510888607/2500000000 : ℝ)*x 1 + (5239833941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349001691/10000000000 : ℝ)^4409 ≤ (11066549628737/25000000000000 : ℝ)^3385 := by
    have hnat : (5349001691 : ℕ)^4409*25000000000000^3385 ≤ 11066549628737^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349001691 10000000000 11066549628737 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (510888607/2500000000 : ℝ)^4409 ≤ (1264067884959/10000000000000 : ℝ)^3385 := by
    have hnat : (510888607 : ℕ)^4409*10000000000000^3385 ≤ 1264067884959^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510888607 2500000000 1264067884959 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239833941/10000000000 : ℝ)^4409 ≤ (43093122619031/100000000000000 : ℝ)^3385 := by
    have hnat : (5239833941 : ℕ)^4409*100000000000000^3385 ≤ 43093122619031^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239833941 10000000000 43093122619031 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349001691/10000000000 : ℝ), (-510888607/2500000000 : ℝ), (5239833941/10000000000 : ℝ)] ![(11066549628737/25000000000000 : ℝ), (1264067884959/10000000000000 : ℝ), (43093122619031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349001691/10000000000 : ℝ)|^4409 ≤ (11066549628737/25000000000000 : ℝ)^3385
        have hw : |(5349001691/10000000000 : ℝ)|=(5349001691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-510888607/2500000000 : ℝ)|^4409 ≤ (1264067884959/10000000000000 : ℝ)^3385
        have hw : |(-510888607/2500000000 : ℝ)|=(510888607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239833941/10000000000 : ℝ)|^4409 ≤ (43093122619031/100000000000000 : ℝ)^3385
        have hw : |(5239833941/10000000000 : ℝ)|=(5239833941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s3_2 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337250159/2500000000 : ℝ)*x 0 + (2619917543/5000000000 : ℝ)*x 1 + (-1021777159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337250159/2500000000 : ℝ)^4409 ≤ (44266187143039/100000000000000 : ℝ)^3385 := by
    have hnat : (1337250159 : ℕ)^4409*100000000000000^3385 ≤ 44266187143039^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337250159 2500000000 44266187143039 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619917543/5000000000 : ℝ)^4409 ≤ (10773283721077/25000000000000 : ℝ)^3385 := by
    have hnat : (2619917543 : ℕ)^4409*25000000000000^3385 ≤ 10773283721077^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619917543 5000000000 10773283721077 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021777159/5000000000 : ℝ)^4409 ≤ (1580084745417/12500000000000 : ℝ)^3385 := by
    have hnat : (1021777159 : ℕ)^4409*12500000000000^3385 ≤ 1580084745417^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021777159 5000000000 1580084745417 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337250159/2500000000 : ℝ), (2619917543/5000000000 : ℝ), (-1021777159/5000000000 : ℝ)] ![(44266187143039/100000000000000 : ℝ), (10773283721077/25000000000000 : ℝ), (1580084745417/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337250159/2500000000 : ℝ)|^4409 ≤ (44266187143039/100000000000000 : ℝ)^3385
        have hw : |(1337250159/2500000000 : ℝ)|=(1337250159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619917543/5000000000 : ℝ)|^4409 ≤ (10773283721077/25000000000000 : ℝ)^3385
        have hw : |(2619917543/5000000000 : ℝ)|=(2619917543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021777159/5000000000 : ℝ)|^4409 ≤ (1580084745417/12500000000000 : ℝ)^3385
        have hw : |(-1021777159/5000000000 : ℝ)|=(1021777159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s3_3 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298821949/10000000000 : ℝ)*x 0 + (4111414909/10000000000 : ℝ)*x 1 + (4493810211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298821949/10000000000 : ℝ)^4409 ≤ (33299185189227/100000000000000 : ℝ)^3385 := by
    have hnat : (4298821949 : ℕ)^4409*100000000000000^3385 ≤ 33299185189227^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298821949 10000000000 33299185189227 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4111414909/10000000000 : ℝ)^4409 ≤ (3142095641423/10000000000000 : ℝ)^3385 := by
    have hnat : (4111414909 : ℕ)^4409*10000000000000^3385 ≤ 3142095641423^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111414909 10000000000 3142095641423 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493810211/10000000000 : ℝ)^4409 ≤ (8819964595091/25000000000000 : ℝ)^3385 := by
    have hnat : (4493810211 : ℕ)^4409*25000000000000^3385 ≤ 8819964595091^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493810211 10000000000 8819964595091 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298821949/10000000000 : ℝ), (4111414909/10000000000 : ℝ), (4493810211/10000000000 : ℝ)] ![(33299185189227/100000000000000 : ℝ), (3142095641423/10000000000000 : ℝ), (8819964595091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298821949/10000000000 : ℝ)|^4409 ≤ (33299185189227/100000000000000 : ℝ)^3385
        have hw : |(4298821949/10000000000 : ℝ)|=(4298821949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4111414909/10000000000 : ℝ)|^4409 ≤ (3142095641423/10000000000000 : ℝ)^3385
        have hw : |(4111414909/10000000000 : ℝ)|=(4111414909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493810211/10000000000 : ℝ)|^4409 ≤ (8819964595091/25000000000000 : ℝ)^3385
        have hw : |(4493810211/10000000000 : ℝ)|=(4493810211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s3_4 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-977046033/5000000000 : ℝ)*x 0 + (5240530141/10000000000 : ℝ)*x 1 + (5414610093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977046033/5000000000 : ℝ)^4409 ≤ (5962357871469/50000000000000 : ℝ)^3385 := by
    have hnat : (977046033 : ℕ)^4409*50000000000000^3385 ≤ 5962357871469^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977046033 5000000000 5962357871469 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240530141/10000000000 : ℝ)^4409 ≤ (21550290242841/50000000000000 : ℝ)^3385 := by
    have hnat : (5240530141 : ℕ)^4409*50000000000000^3385 ≤ 21550290242841^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240530141 10000000000 21550290242841 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414610093/10000000000 : ℝ)^4409 ≤ (44974703754769/100000000000000 : ℝ)^3385 := by
    have hnat : (5414610093 : ℕ)^4409*100000000000000^3385 ≤ 44974703754769^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414610093 10000000000 44974703754769 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977046033/5000000000 : ℝ), (5240530141/10000000000 : ℝ), (5414610093/10000000000 : ℝ)] ![(5962357871469/50000000000000 : ℝ), (21550290242841/50000000000000 : ℝ), (44974703754769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977046033/5000000000 : ℝ)|^4409 ≤ (5962357871469/50000000000000 : ℝ)^3385
        have hw : |(-977046033/5000000000 : ℝ)|=(977046033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240530141/10000000000 : ℝ)|^4409 ≤ (21550290242841/50000000000000 : ℝ)^3385
        have hw : |(5240530141/10000000000 : ℝ)|=(5240530141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414610093/10000000000 : ℝ)|^4409 ≤ (44974703754769/100000000000000 : ℝ)^3385
        have hw : |(5414610093/10000000000 : ℝ)|=(5414610093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s3_5 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060659049/2000000000 : ℝ)*x 0 + (-1868779301/10000000000 : ℝ)*x 1 + (676826257/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060659049/2000000000 : ℝ)^4409 ≤ (43774163986299/100000000000000 : ℝ)^3385 := by
    have hnat : (1060659049 : ℕ)^4409*100000000000000^3385 ≤ 43774163986299^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060659049 2000000000 43774163986299 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1868779301/10000000000 : ℝ)^4409 ≤ (2812783161141/25000000000000 : ℝ)^3385 := by
    have hnat : (1868779301 : ℕ)^4409*25000000000000^3385 ≤ 2812783161141^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868779301 10000000000 2812783161141 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676826257/1250000000 : ℝ)^4409 ≤ (4497470335447/10000000000000 : ℝ)^3385 := by
    have hnat : (676826257 : ℕ)^4409*10000000000000^3385 ≤ 4497470335447^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676826257 1250000000 4497470335447 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060659049/2000000000 : ℝ), (-1868779301/10000000000 : ℝ), (676826257/1250000000 : ℝ)] ![(43774163986299/100000000000000 : ℝ), (2812783161141/25000000000000 : ℝ), (4497470335447/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060659049/2000000000 : ℝ)|^4409 ≤ (43774163986299/100000000000000 : ℝ)^3385
        have hw : |(1060659049/2000000000 : ℝ)|=(1060659049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1868779301/10000000000 : ℝ)|^4409 ≤ (2812783161141/25000000000000 : ℝ)^3385
        have hw : |(-1868779301/10000000000 : ℝ)|=(1868779301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676826257/1250000000 : ℝ)|^4409 ≤ (4497470335447/10000000000000 : ℝ)^3385
        have hw : |(676826257/1250000000 : ℝ)|=(676826257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s3_6 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651647039/5000000000 : ℝ)*x 0 + (2707305491/5000000000 : ℝ)*x 1 + (-1868779623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651647039/5000000000 : ℝ)^4409 ≤ (43774151439749/100000000000000 : ℝ)^3385 := by
    have hnat : (2651647039 : ℕ)^4409*100000000000000^3385 ≤ 43774151439749^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651647039 5000000000 43774151439749 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707305491/5000000000 : ℝ)^4409 ≤ (44974713372759/100000000000000 : ℝ)^3385 := by
    have hnat : (2707305491 : ℕ)^4409*100000000000000^3385 ≤ 44974713372759^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707305491 5000000000 44974713372759 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1868779623/10000000000 : ℝ)^4409 ≤ (5625567584823/50000000000000 : ℝ)^3385 := by
    have hnat : (1868779623 : ℕ)^4409*50000000000000^3385 ≤ 5625567584823^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868779623 10000000000 5625567584823 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651647039/5000000000 : ℝ), (2707305491/5000000000 : ℝ), (-1868779623/10000000000 : ℝ)] ![(43774151439749/100000000000000 : ℝ), (44974713372759/100000000000000 : ℝ), (5625567584823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651647039/5000000000 : ℝ)|^4409 ≤ (43774151439749/100000000000000 : ℝ)^3385
        have hw : |(2651647039/5000000000 : ℝ)|=(2651647039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707305491/5000000000 : ℝ)|^4409 ≤ (44974713372759/100000000000000 : ℝ)^3385
        have hw : |(2707305491/5000000000 : ℝ)|=(2707305491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1868779623/10000000000 : ℝ)|^4409 ≤ (5625567584823/50000000000000 : ℝ)^3385
        have hw : |(-1868779623/10000000000 : ℝ)|=(1868779623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s3_7 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298853237/10000000000 : ℝ)*x 0 + (4492294519/10000000000 : ℝ)*x 1 + (822588011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298853237/10000000000 : ℝ)^4409 ≤ (8324875216723/25000000000000 : ℝ)^3385 := by
    have hnat : (4298853237 : ℕ)^4409*25000000000000^3385 ≤ 8324875216723^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298853237 10000000000 8324875216723 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492294519/10000000000 : ℝ)^4409 ≤ (35264360142137/100000000000000 : ℝ)^3385 := by
    have hnat : (4492294519 : ℕ)^4409*100000000000000^3385 ≤ 35264360142137^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492294519 10000000000 35264360142137 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (822588011/2000000000 : ℝ)^4409 ≤ (3143613898467/10000000000000 : ℝ)^3385 := by
    have hnat : (822588011 : ℕ)^4409*10000000000000^3385 ≤ 3143613898467^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822588011 2000000000 3143613898467 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298853237/10000000000 : ℝ), (4492294519/10000000000 : ℝ), (822588011/2000000000 : ℝ)] ![(8324875216723/25000000000000 : ℝ), (35264360142137/100000000000000 : ℝ), (3143613898467/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298853237/10000000000 : ℝ)|^4409 ≤ (8324875216723/25000000000000 : ℝ)^3385
        have hw : |(4298853237/10000000000 : ℝ)|=(4298853237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492294519/10000000000 : ℝ)|^4409 ≤ (35264360142137/100000000000000 : ℝ)^3385
        have hw : |(4492294519/10000000000 : ℝ)|=(4492294519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(822588011/2000000000 : ℝ)|^4409 ≤ (3143613898467/10000000000000 : ℝ)^3385
        have hw : |(822588011/2000000000 : ℝ)|=(822588011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1449_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (787/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (561/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14937/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (787/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1309/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (787/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1309/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (787/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1309/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (787/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1309/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (787/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1309/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (787/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1309/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (1309/12500 : ℝ) ^ (551/128 : ℝ) ≤ (30234571467803/500000000000000000 : ℝ) := by
    have hpowers : (1309/12500 : ℝ)^551 ≤ (30234571467803/500000000000000000 : ℝ)^128 := by
      have hnat : (1309 : ℕ)^551*500000000000000000^128 ≤ 30234571467803^128*12500^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1309 12500 30234571467803 500000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1309/12500 : ℝ)) (X := (30234571467803/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hpowhi : (787/5000 : ℝ) ^ (551/128 : ℝ) ≤ (17471343183649741/50000000000000000000 : ℝ) := by
    have hpowers : (787/5000 : ℝ)^551 ≤ (17471343183649741/50000000000000000000 : ℝ)^128 := by
      have hnat : (787 : ℕ)^551*50000000000000000000^128 ≤ 17471343183649741^128*5000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        787 5000 17471343183649741 50000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (787/5000 : ℝ)) (X := (17471343183649741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (250030234571467803/250000000000000000 : ℝ) ≤ (10000280932523187/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (250030234571467803/250000000000000000 : ℝ)^128 ≤ (10000280932523187/10000000000000000 : ℝ)^551 := by
      have hnat : (250030234571467803 : ℕ)^128*10000000000000000^551 ≤ 10000280932523187^551*250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250030234571467803 250000000000000000 10000280932523187 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280932523187/10000000000000000 : ℝ)) (X := (250030234571467803/250000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020494800330430041/50000000000000000000 : ℝ) ≤ (5000476029363497/5000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (50020494800330430041/50000000000000000000 : ℝ)^128 ≤ (5000476029363497/5000000000000000 : ℝ)^551 := by
      have hnat : (50020494800330430041 : ℕ)^128*5000000000000000^551 ≤ 5000476029363497^551*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020494800330430041 50000000000000000000 5000476029363497 5000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000476029363497/5000000000000000 : ℝ)) (X := (50020494800330430041/50000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017471343183649741/25000000000000000000 : ℝ) ≤ (10001623184930801/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (25017471343183649741/25000000000000000000 : ℝ)^128 ≤ (10001623184930801/10000000000000000 : ℝ)^551 := by
      have hnat : (25017471343183649741 : ℕ)^128*10000000000000000^551 ≤ 10001623184930801^551*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017471343183649741 25000000000000000000 10001623184930801 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001623184930801/10000000000000000 : ℝ)) (X := (25017471343183649741/25000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(30234571467803/500000000000000000 : ℝ) ≤ ((13166855971329903827/13170000000000000000 : ℝ)+2*(671126203807/526800000000000 : ℝ)*(1309/12500 : ℝ))^(551/128 : ℝ) := by
    rw [show (13166855971329903827/13170000000000000000 : ℝ)+2*(671126203807/526800000000000 : ℝ)*(1309/12500 : ℝ)=(10000280932523187/10000000000000000 : ℝ) by norm_num, show 1+2*(30234571467803/500000000000000000 : ℝ)=(250030234571467803/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17471343183649741/50000000000000000000 : ℝ)+(30234571467803/500000000000000000 : ℝ) ≤ ((13166855971329903827/13170000000000000000 : ℝ)+(671126203807/526800000000000 : ℝ)*((787/5000 : ℝ)+(1309/12500 : ℝ)))^(551/128 : ℝ) := by
    rw [show (13166855971329903827/13170000000000000000 : ℝ)+(671126203807/526800000000000 : ℝ)*((787/5000 : ℝ)+(1309/12500 : ℝ))=(5000476029363497/5000000000000000 : ℝ) by norm_num, show 1+(17471343183649741/50000000000000000000 : ℝ)+(30234571467803/500000000000000000 : ℝ)=(50020494800330430041/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17471343183649741/50000000000000000000 : ℝ) ≤ ((13166855971329903827/13170000000000000000 : ℝ)+2*(671126203807/526800000000000 : ℝ)*(787/5000 : ℝ))^(551/128 : ℝ) := by
    rw [show (13166855971329903827/13170000000000000000 : ℝ)+2*(671126203807/526800000000000 : ℝ)*(787/5000 : ℝ)=(10001623184930801/10000000000000000 : ℝ) by norm_num, show 1+2*(17471343183649741/50000000000000000000 : ℝ)=(25017471343183649741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13166855971329903827/13170000000000000000 : ℝ)*(X 1 0+X 2 0)+(671126203807/526800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (1309/12500 : ℝ)) (hi := (787/5000 : ℝ)) (c := (13166855971329903827/13170000000000000000 : ℝ)) (alpha := (671126203807/526800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13166855971329903827/13170000000000000000 : ℝ)*(X 0 1+X 2 1)+(671126203807/526800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (1309/12500 : ℝ)) (hi := (787/5000 : ℝ)) (c := (13166855971329903827/13170000000000000000 : ℝ)) (alpha := (671126203807/526800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13166855971329903827/13170000000000000000 : ℝ)*(X 0 2+X 1 2)+(671126203807/526800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (1309/12500 : ℝ)) (hi := (787/5000 : ℝ)) (c := (13166855971329903827/13170000000000000000 : ℝ)) (alpha := (671126203807/526800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1954077131/10000000000 : ℝ)*X 0 0+(5415309827/10000000000 : ℝ)*X 0 1+(523983451/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349001691/10000000000 : ℝ)*X 1 0+(-510888607/2500000000 : ℝ)*X 1 1+(5239833941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337250159/2500000000 : ℝ)*X 2 0+(2619917543/5000000000 : ℝ)*X 2 1+(-1021777159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298821949/10000000000 : ℝ)*X 0 0+(4111414909/10000000000 : ℝ)*X 0 1+(4493810211/10000000000 : ℝ)*X 0 2+(4298821949/10000000000 : ℝ)*X 1 0+(4111414909/10000000000 : ℝ)*X 1 1+(4493810211/10000000000 : ℝ)*X 1 2+(4298821949/10000000000 : ℝ)*X 2 0+(4111414909/10000000000 : ℝ)*X 2 1+(4493810211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-977046033/5000000000 : ℝ)*X 0 0+(5240530141/10000000000 : ℝ)*X 0 1+(5414610093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060659049/2000000000 : ℝ)*X 1 0+(-1868779301/10000000000 : ℝ)*X 1 1+(676826257/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651647039/5000000000 : ℝ)*X 2 0+(2707305491/5000000000 : ℝ)*X 2 1+(-1868779623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298853237/10000000000 : ℝ)*X 0 0+(4492294519/10000000000 : ℝ)*X 0 1+(822588011/2000000000 : ℝ)*X 0 2+(4298853237/10000000000 : ℝ)*X 1 0+(4492294519/10000000000 : ℝ)*X 1 1+(822588011/2000000000 : ℝ)*X 1 2+(4298853237/10000000000 : ℝ)*X 2 0+(4492294519/10000000000 : ℝ)*X 2 1+(822588011/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42688567238109466873857/4390000000000000000000000000 : ℝ) := by norm_num
    linear_combination (415023849/25000000000000 : ℝ)*(base19) + (146057889/25000000000000 : ℝ)*(base23) + (94256021/50000000000000 : ℝ)*(lower2) + (214262969/100000000000000 : ℝ)*(lower4) + (10877193/50000000000000 : ℝ)*(lower5) + (2078498459204623/50000000000000 : ℝ)*(major0) + (2078498459204623/50000000000000 : ℝ)*(major1) + (2078498459204623/50000000000000 : ℝ)*(major2) + (2849421444798203/50000000000000 : ℝ)*(sp0) + (5698867890393223/100000000000000 : ℝ)*(sp1) + (2849434483128531/50000000000000 : ℝ)*(sp2) + (653777786371809/25000000000000 : ℝ)*(sp3) + (26660892213/100000000000000 : ℝ)*(sp4) + (6408353861/50000000000000 : ℝ)*(sp7) + (2615123962194959/100000000000000 : ℝ)*(f.failure) + (2849434775244309/50000000000000 : ℝ)*(f.sum) + (93280281565981/13170000000000000000000000000 : ℝ)*base65 + (62626582877772407/219500000000000000000000000000000 : ℝ)*base67 + (940114682813227593/219500000000000000000000000000000 : ℝ)*base70 + (2271075757464772407/219500000000000000000000000000000 : ℝ)*base71 + (71253852140101/13170000000000000000000000000 : ℝ)*base73 + (1968714724606227593/219500000000000000000000000000000 : ℝ)*base76 + (1240402238554272407/219500000000000000000000000000000 : ℝ)*base77 + (356289943493727593/219500000000000000000000000000000 : ℝ)*base80 + (23866322105461/13170000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (27918239/5000000000000000000000 : ℝ)*base89 + (27918239/5000000000000000000000 : ℝ)*base91 + (27918239/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23193208545424866543777/2195000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37180601/50000000000000 : ℝ)*(base8) + (731985187/100000000000000 : ℝ)*(base21) + (150565839/100000000000000 : ℝ)*(upper2) + (42504939/25000000000000 : ℝ)*(lower4) + (1047567275500003/25000000000000 : ℝ)*(major0) + (1047567275500003/25000000000000 : ℝ)*(major1) + (1047567275500003/25000000000000 : ℝ)*(major2) + (1105393901/100000000000000 : ℝ)*(sp0) + (2193016577/100000000000000 : ℝ)*(sp1) + (3506524959/100000000000000 : ℝ)*(sp2) + (5744481521700559/100000000000000 : ℝ)*(sp4) + (1436120127109771/25000000000000 : ℝ)*(sp5) + (1436119615736379/25000000000000 : ℝ)*(sp6) + (329506893791453/12500000000000 : ℝ)*(sp7) + (329506893791453/12500000000000 : ℝ)*(f.failure) + (2872241350727831/50000000000000 : ℝ)*(f.sum) + (9263328657533/3292500000000000000000000000 : ℝ)*base65 + (5320410814921173/109750000000000000000000000000000 : ℝ)*base68 + (170569011961171173/109750000000000000000000000000000 : ℝ)*base70 + (650932855998328827/109750000000000000000000000000000 : ℝ)*base71 + (9781832280061/6585000000000000000000000000 : ℝ)*base73 + (318740040789828827/109750000000000000000000000000000 : ℝ)*base75 + (874061093869578827/109750000000000000000000000000000 : ℝ)*base77 + (147661138654921173/109750000000000000000000000000000 : ℝ)*base80 + (23212991575771/6585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (84787/625000000000000000000 : ℝ)*base90 + (84787/625000000000000000000 : ℝ)*base92 + (84787/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1449_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (787/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1449_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1449_s4_0 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1954883833/10000000000 : ℝ)*x 0 + (2704189527/5000000000 : ℝ)*x 1 + (5246233533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1954883833/10000000000 : ℝ)^4409 ≤ (1193100947789/10000000000000 : ℝ)^3385 := by
    have hnat : (1954883833 : ℕ)^4409*10000000000000^3385 ≤ 1193100947789^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954883833 10000000000 1193100947789 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704189527/5000000000 : ℝ)^4409 ≤ (5613412823839/12500000000000 : ℝ)^3385 := by
    have hnat : (2704189527 : ℕ)^4409*12500000000000^3385 ≤ 5613412823839^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704189527 5000000000 5613412823839 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246233533/10000000000 : ℝ)^4409 ≤ (21580843957317/50000000000000 : ℝ)^3385 := by
    have hnat : (5246233533 : ℕ)^4409*50000000000000^3385 ≤ 21580843957317^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246233533 10000000000 21580843957317 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1954883833/10000000000 : ℝ), (2704189527/5000000000 : ℝ), (5246233533/10000000000 : ℝ)] ![(1193100947789/10000000000000 : ℝ), (5613412823839/12500000000000 : ℝ), (21580843957317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1954883833/10000000000 : ℝ)|^4409 ≤ (1193100947789/10000000000000 : ℝ)^3385
        have hw : |(-1954883833/10000000000 : ℝ)|=(1954883833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704189527/5000000000 : ℝ)|^4409 ≤ (5613412823839/12500000000000 : ℝ)^3385
        have hw : |(2704189527/5000000000 : ℝ)|=(2704189527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246233533/10000000000 : ℝ)|^4409 ≤ (21580843957317/50000000000000 : ℝ)^3385
        have hw : |(5246233533/10000000000 : ℝ)|=(5246233533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s4_1 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673603593/5000000000 : ℝ)*x 0 + (-7958759/39062500 : ℝ)*x 1 + (5246233441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673603593/5000000000 : ℝ)^4409 ≤ (44246856418229/100000000000000 : ℝ)^3385 := by
    have hnat : (2673603593 : ℕ)^4409*100000000000000^3385 ≤ 44246856418229^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673603593 5000000000 44246856418229 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7958759/39062500 : ℝ)^4409 ≤ (1259145663867/10000000000000 : ℝ)^3385 := by
    have hnat : (7958759 : ℕ)^4409*10000000000000^3385 ≤ 1259145663867^3385*39062500^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7958759 39062500 1259145663867 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246233441/10000000000 : ℝ)^4409 ≤ (43161686928763/100000000000000 : ℝ)^3385 := by
    have hnat : (5246233441 : ℕ)^4409*100000000000000^3385 ≤ 43161686928763^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246233441 10000000000 43161686928763 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673603593/5000000000 : ℝ), (-7958759/39062500 : ℝ), (5246233441/10000000000 : ℝ)] ![(44246856418229/100000000000000 : ℝ), (1259145663867/10000000000000 : ℝ), (43161686928763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673603593/5000000000 : ℝ)|^4409 ≤ (44246856418229/100000000000000 : ℝ)^3385
        have hw : |(2673603593/5000000000 : ℝ)|=(2673603593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7958759/39062500 : ℝ)|^4409 ≤ (1259145663867/10000000000000 : ℝ)^3385
        have hw : |(-7958759/39062500 : ℝ)|=(7958759/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246233441/10000000000 : ℝ)|^4409 ≤ (43161686928763/100000000000000 : ℝ)^3385
        have hw : |(5246233441/10000000000 : ℝ)|=(5246233441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s4_2 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668400901/1250000000 : ℝ)*x 0 + (5246233711/10000000000 : ℝ)*x 1 + (-407488383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668400901/1250000000 : ℝ)^4409 ≤ (2765428540959/6250000000000 : ℝ)^3385 := by
    have hnat : (668400901 : ℕ)^4409*6250000000000^3385 ≤ 2765428540959^3385*1250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668400901 1250000000 2765428540959 6250000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246233711/10000000000 : ℝ)^4409 ≤ (67440140347/156250000000 : ℝ)^3385 := by
    have hnat : (5246233711 : ℕ)^4409*156250000000^3385 ≤ 67440140347^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246233711 10000000000 67440140347 156250000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407488383/2000000000 : ℝ)^4409 ≤ (196741461053/1562500000000 : ℝ)^3385 := by
    have hnat : (407488383 : ℕ)^4409*1562500000000^3385 ≤ 196741461053^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407488383 2000000000 196741461053 1562500000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668400901/1250000000 : ℝ), (5246233711/10000000000 : ℝ), (-407488383/2000000000 : ℝ)] ![(2765428540959/6250000000000 : ℝ), (67440140347/156250000000 : ℝ), (196741461053/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668400901/1250000000 : ℝ)|^4409 ≤ (2765428540959/6250000000000 : ℝ)^3385
        have hw : |(668400901/1250000000 : ℝ)|=(668400901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246233711/10000000000 : ℝ)|^4409 ≤ (67440140347/156250000000 : ℝ)^3385
        have hw : |(5246233711/10000000000 : ℝ)|=(5246233711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407488383/2000000000 : ℝ)|^4409 ≤ (196741461053/1562500000000 : ℝ)^3385
        have hw : |(-407488383/2000000000 : ℝ)|=(407488383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s4_3 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149657779/5000000000 : ℝ)*x 0 + (4125881419/10000000000 : ℝ)*x 1 + (223961301/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149657779/5000000000 : ℝ)^4409 ≤ (6660833099411/20000000000000 : ℝ)^3385 := by
    have hnat : (2149657779 : ℕ)^4409*20000000000000^3385 ≤ 6660833099411^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149657779 5000000000 6660833099411 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4125881419/10000000000 : ℝ)^4409 ≤ (31565036572647/100000000000000 : ℝ)^3385 := by
    have hnat : (4125881419 : ℕ)^4409*100000000000000^3385 ≤ 31565036572647^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125881419 10000000000 31565036572647 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223961301/500000000 : ℝ)^4409 ≤ (17565398957313/50000000000000 : ℝ)^3385 := by
    have hnat : (223961301 : ℕ)^4409*50000000000000^3385 ≤ 17565398957313^3385*500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223961301 500000000 17565398957313 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149657779/5000000000 : ℝ), (4125881419/10000000000 : ℝ), (223961301/500000000 : ℝ)] ![(6660833099411/20000000000000 : ℝ), (31565036572647/100000000000000 : ℝ), (17565398957313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149657779/5000000000 : ℝ)|^4409 ≤ (6660833099411/20000000000000 : ℝ)^3385
        have hw : |(2149657779/5000000000 : ℝ)|=(2149657779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4125881419/10000000000 : ℝ)|^4409 ≤ (31565036572647/100000000000000 : ℝ)^3385
        have hw : |(4125881419/10000000000 : ℝ)|=(4125881419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(223961301/500000000 : ℝ)|^4409 ≤ (17565398957313/50000000000000 : ℝ)^3385
        have hw : |(223961301/500000000 : ℝ)|=(223961301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s4_4 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390979081/2000000000 : ℝ)*x 0 + (1311706989/2500000000 : ℝ)*x 1 + (2703890777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390979081/2000000000 : ℝ)^4409 ≤ (1193110146913/10000000000000 : ℝ)^3385 := by
    have hnat : (390979081 : ℕ)^4409*10000000000000^3385 ≤ 1193110146913^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390979081 2000000000 1193110146913 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311706989/2500000000 : ℝ)^4409 ≤ (21584028926827/50000000000000 : ℝ)^3385 := by
    have hnat : (1311706989 : ℕ)^4409*50000000000000^3385 ≤ 21584028926827^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311706989 2500000000 21584028926827 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703890777/5000000000 : ℝ)^4409 ≤ (44900840665531/100000000000000 : ℝ)^3385 := by
    have hnat : (2703890777 : ℕ)^4409*100000000000000^3385 ≤ 44900840665531^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703890777 5000000000 44900840665531 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390979081/2000000000 : ℝ), (1311706989/2500000000 : ℝ), (2703890777/5000000000 : ℝ)] ![(1193110146913/10000000000000 : ℝ), (21584028926827/50000000000000 : ℝ), (44900840665531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390979081/2000000000 : ℝ)|^4409 ≤ (1193110146913/10000000000000 : ℝ)^3385
        have hw : |(-390979081/2000000000 : ℝ)|=(390979081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311706989/2500000000 : ℝ)|^4409 ≤ (21584028926827/50000000000000 : ℝ)^3385
        have hw : |(1311706989/2500000000 : ℝ)|=(1311706989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703890777/5000000000 : ℝ)|^4409 ≤ (44900840665531/100000000000000 : ℝ)^3385
        have hw : |(2703890777/5000000000 : ℝ)|=(2703890777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s4_5 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060994597/2000000000 : ℝ)*x 0 + (-117243373/625000000 : ℝ)*x 1 + (5407781541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060994597/2000000000 : ℝ)^4409 ≤ (8758440484783/20000000000000 : ℝ)^3385 := by
    have hnat : (1060994597 : ℕ)^4409*20000000000000^3385 ≤ 8758440484783^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060994597 2000000000 8758440484783 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117243373/625000000 : ℝ)^4409 ≤ (706684814997/6250000000000 : ℝ)^3385 := by
    have hnat : (117243373 : ℕ)^4409*6250000000000^3385 ≤ 706684814997^3385*625000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117243373 625000000 706684814997 6250000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407781541/10000000000 : ℝ)^4409 ≤ (44900840524939/100000000000000 : ℝ)^3385 := by
    have hnat : (5407781541 : ℕ)^4409*100000000000000^3385 ≤ 44900840524939^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407781541 10000000000 44900840524939 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060994597/2000000000 : ℝ), (-117243373/625000000 : ℝ), (5407781541/10000000000 : ℝ)] ![(8758440484783/20000000000000 : ℝ), (706684814997/6250000000000 : ℝ), (44900840524939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060994597/2000000000 : ℝ)|^4409 ≤ (8758440484783/20000000000000 : ℝ)^3385
        have hw : |(1060994597/2000000000 : ℝ)|=(1060994597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117243373/625000000 : ℝ)|^4409 ≤ (706684814997/6250000000000 : ℝ)^3385
        have hw : |(-117243373/625000000 : ℝ)|=(117243373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407781541/10000000000 : ℝ)|^4409 ≤ (44900840524939/100000000000000 : ℝ)^3385
        have hw : |(5407781541/10000000000 : ℝ)|=(5407781541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s4_6 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331560813/625000000 : ℝ)*x 0 + (5407781533/10000000000 : ℝ)*x 1 + (-1875893947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331560813/625000000 : ℝ)^4409 ≤ (8758440534243/20000000000000 : ℝ)^3385 := by
    have hnat : (331560813 : ℕ)^4409*20000000000000^3385 ≤ 8758440534243^3385*625000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331560813 625000000 8758440534243 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407781533/10000000000 : ℝ)^4409 ≤ (44900840438421/100000000000000 : ℝ)^3385 := by
    have hnat : (5407781533 : ℕ)^4409*100000000000000^3385 ≤ 44900840438421^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407781533 10000000000 44900840438421 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875893947/10000000000 : ℝ)^4409 ≤ (11306956875083/100000000000000 : ℝ)^3385 := by
    have hnat : (1875893947 : ℕ)^4409*100000000000000^3385 ≤ 11306956875083^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875893947 10000000000 11306956875083 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331560813/625000000 : ℝ), (5407781533/10000000000 : ℝ), (-1875893947/10000000000 : ℝ)] ![(8758440534243/20000000000000 : ℝ), (44900840438421/100000000000000 : ℝ), (11306956875083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331560813/625000000 : ℝ)|^4409 ≤ (8758440534243/20000000000000 : ℝ)^3385
        have hw : |(331560813/625000000 : ℝ)|=(331560813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407781533/10000000000 : ℝ)|^4409 ≤ (44900840438421/100000000000000 : ℝ)^3385
        have hw : |(5407781533/10000000000 : ℝ)|=(5407781533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1875893947/10000000000 : ℝ)|^4409 ≤ (11306956875083/100000000000000 : ℝ)^3385
        have hw : |(-1875893947/10000000000 : ℝ)|=(1875893947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s4_7 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859868347/2000000000 : ℝ)*x 0 + (4477931427/10000000000 : ℝ)*x 1 + (4127181971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859868347/2000000000 : ℝ)^4409 ≤ (33304429616839/100000000000000 : ℝ)^3385 := by
    have hnat : (859868347 : ℕ)^4409*100000000000000^3385 ≤ 33304429616839^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859868347 2000000000 33304429616839 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477931427/10000000000 : ℝ)^4409 ≤ (3511757336991/10000000000000 : ℝ)^3385 := by
    have hnat : (4477931427 : ℕ)^4409*10000000000000^3385 ≤ 3511757336991^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477931427 10000000000 3511757336991 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127181971/10000000000 : ℝ)^4409 ≤ (15788998501261/50000000000000 : ℝ)^3385 := by
    have hnat : (4127181971 : ℕ)^4409*50000000000000^3385 ≤ 15788998501261^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127181971 10000000000 15788998501261 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859868347/2000000000 : ℝ), (4477931427/10000000000 : ℝ), (4127181971/10000000000 : ℝ)] ![(33304429616839/100000000000000 : ℝ), (3511757336991/10000000000000 : ℝ), (15788998501261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859868347/2000000000 : ℝ)|^4409 ≤ (33304429616839/100000000000000 : ℝ)^3385
        have hw : |(859868347/2000000000 : ℝ)|=(859868347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477931427/10000000000 : ℝ)|^4409 ≤ (3511757336991/10000000000000 : ℝ)^3385
        have hw : |(4477931427/10000000000 : ℝ)|=(4477931427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127181971/10000000000 : ℝ)|^4409 ≤ (15788998501261/50000000000000 : ℝ)^3385
        have hw : |(4127181971/10000000000 : ℝ)|=(4127181971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1449_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11357/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1849/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (561/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (561/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (561/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (561/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (561/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (561/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (561/5000 : ℝ) ^ (551/128 : ℝ) ≤ (4068985391129613/50000000000000000000 : ℝ) := by
    have hpowers : (561/5000 : ℝ)^551 ≤ (4068985391129613/50000000000000000000 : ℝ)^128 := by
      have hnat : (561 : ℕ)^551*50000000000000000000^128 ≤ 4068985391129613^128*5000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 5000 4068985391129613 50000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/5000 : ℝ)) (X := (4068985391129613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14937/100000 : ℝ) ^ (551/128 : ℝ) ≤ (278908594966981/1000000000000000000 : ℝ) := by
    have hpowers : (14937/100000 : ℝ)^551 ≤ (278908594966981/1000000000000000000 : ℝ)^128 := by
      have hnat : (14937 : ℕ)^551*1000000000000000000^128 ≤ 278908594966981^128*100000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14937 100000 278908594966981 1000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14937/100000 : ℝ)) (X := (278908594966981/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004068985391129613/25000000000000000000 : ℝ) ≤ (1250047259309839/1250000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (25004068985391129613/25000000000000000000 : ℝ)^128 ≤ (1250047259309839/1250000000000000 : ℝ)^551 := by
      have hnat : (25004068985391129613 : ℕ)^128*1250000000000000^551 ≤ 1250047259309839^551*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004068985391129613 25000000000000000000 1250047259309839 1250000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250047259309839/1250000000000000 : ℝ)) (X := (25004068985391129613/25000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018014415139478663/50000000000000000000 : ℝ) ≤ (10000836851657669/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (50018014415139478663/50000000000000000000 : ℝ)^128 ≤ (10000836851657669/10000000000000000 : ℝ)^551 := by
      have hnat : (50018014415139478663 : ℕ)^128*10000000000000000^551 ≤ 10000836851657669^551*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018014415139478663 50000000000000000000 10000836851657669 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000836851657669/10000000000000000 : ℝ)) (X := (50018014415139478663/50000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (500278908594966981/500000000000000000 : ℝ) ≤ (5000647814418313/5000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (500278908594966981/500000000000000000 : ℝ)^128 ≤ (5000647814418313/5000000000000000 : ℝ)^551 := by
      have hnat : (500278908594966981 : ℕ)^128*5000000000000000^551 ≤ 5000647814418313^551*500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500278908594966981 500000000000000000 5000647814418313 5000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000647814418313/5000000000000000 : ℝ)) (X := (500278908594966981/500000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4068985391129613/50000000000000000000 : ℝ) ≤ ((258063266270427621/258125000000000000 : ℝ)+2*(152925726319/123900000000000 : ℝ)*(561/5000 : ℝ))^(551/128 : ℝ) := by
    rw [show (258063266270427621/258125000000000000 : ℝ)+2*(152925726319/123900000000000 : ℝ)*(561/5000 : ℝ)=(1250047259309839/1250000000000000 : ℝ) by norm_num, show 1+2*(4068985391129613/50000000000000000000 : ℝ)=(25004068985391129613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(278908594966981/1000000000000000000 : ℝ)+(4068985391129613/50000000000000000000 : ℝ) ≤ ((258063266270427621/258125000000000000 : ℝ)+(152925726319/123900000000000 : ℝ)*((14937/100000 : ℝ)+(561/5000 : ℝ)))^(551/128 : ℝ) := by
    rw [show (258063266270427621/258125000000000000 : ℝ)+(152925726319/123900000000000 : ℝ)*((14937/100000 : ℝ)+(561/5000 : ℝ))=(10000836851657669/10000000000000000 : ℝ) by norm_num, show 1+(278908594966981/1000000000000000000 : ℝ)+(4068985391129613/50000000000000000000 : ℝ)=(50018014415139478663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(278908594966981/1000000000000000000 : ℝ) ≤ ((258063266270427621/258125000000000000 : ℝ)+2*(152925726319/123900000000000 : ℝ)*(14937/100000 : ℝ))^(551/128 : ℝ) := by
    rw [show (258063266270427621/258125000000000000 : ℝ)+2*(152925726319/123900000000000 : ℝ)*(14937/100000 : ℝ)=(5000647814418313/5000000000000000 : ℝ) by norm_num, show 1+2*(278908594966981/1000000000000000000 : ℝ)=(500278908594966981/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (258063266270427621/258125000000000000 : ℝ)*(X 1 0+X 2 0)+(152925726319/123900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (258063266270427621/258125000000000000 : ℝ)) (alpha := (152925726319/123900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (258063266270427621/258125000000000000 : ℝ)*(X 0 1+X 2 1)+(152925726319/123900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (258063266270427621/258125000000000000 : ℝ)) (alpha := (152925726319/123900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (258063266270427621/258125000000000000 : ℝ)*(X 0 2+X 1 2)+(152925726319/123900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (258063266270427621/258125000000000000 : ℝ)) (alpha := (152925726319/123900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1954883833/10000000000 : ℝ)*X 0 0+(2704189527/5000000000 : ℝ)*X 0 1+(5246233533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673603593/5000000000 : ℝ)*X 1 0+(-7958759/39062500 : ℝ)*X 1 1+(5246233441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668400901/1250000000 : ℝ)*X 2 0+(5246233711/10000000000 : ℝ)*X 2 1+(-407488383/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149657779/5000000000 : ℝ)*X 0 0+(4125881419/10000000000 : ℝ)*X 0 1+(223961301/500000000 : ℝ)*X 0 2+(2149657779/5000000000 : ℝ)*X 1 0+(4125881419/10000000000 : ℝ)*X 1 1+(223961301/500000000 : ℝ)*X 1 2+(2149657779/5000000000 : ℝ)*X 2 0+(4125881419/10000000000 : ℝ)*X 2 1+(223961301/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-390979081/2000000000 : ℝ)*X 0 0+(1311706989/2500000000 : ℝ)*X 0 1+(2703890777/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060994597/2000000000 : ℝ)*X 1 0+(-117243373/625000000 : ℝ)*X 1 1+(5407781541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331560813/625000000 : ℝ)*X 2 0+(5407781533/10000000000 : ℝ)*X 2 1+(-1875893947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859868347/2000000000 : ℝ)*X 0 0+(4477931427/10000000000 : ℝ)*X 0 1+(4127181971/10000000000 : ℝ)*X 0 2+(859868347/2000000000 : ℝ)*X 1 0+(4477931427/10000000000 : ℝ)*X 1 1+(4127181971/10000000000 : ℝ)*X 1 2+(859868347/2000000000 : ℝ)*X 2 0+(4477931427/10000000000 : ℝ)*X 2 1+(4127181971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8793988521319874314932783/1290625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97646423/20000000000000 : ℝ)*(base19) + (38082921/20000000000000 : ℝ)*(base23) + (13308183/20000000000000 : ℝ)*(upper3) + (211025337/100000000000000 : ℝ)*(upper4) + (224935775428017/5000000000000 : ℝ)*(major0) + (224935775428017/5000000000000 : ℝ)*(major1) + (224935775428017/5000000000000 : ℝ)*(major2) + (6167315611917337/100000000000000 : ℝ)*(sp0) + (1233464371876463/20000000000000 : ℝ)*(sp1) + (1541832800974489/25000000000000 : ℝ)*(sp2) + (2830095609028311/100000000000000 : ℝ)*(sp3) + (19569050223/100000000000000 : ℝ)*(sp4) + (12833353129/100000000000000 : ℝ)*(sp5) + (1893327499/50000000000000 : ℝ)*(sp6) + (2830095609028311/100000000000000 : ℝ)*(f.failure) + (6167335180967559/100000000000000 : ℝ)*(f.sum) + (836742123381/206500000000000000000000000 : ℝ)*base66 + (36287140243507/5761718750000000000000000000 : ℝ)*base68 + (187194212377153/23046875000000000000000000000 : ℝ)*base70 + (114015383632013/92187500000000000000000000000 : ℝ)*base71 + (785637156037/413000000000000000000000000 : ℝ)*base74 + (776649323110901/184375000000000000000000000000 : ℝ)*base75 + (150883625254651/184375000000000000000000000000 : ℝ)*base77 + (33636629166111/11523437500000000000000000000 : ℝ)*base79 + (1483294629449/206500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (45043431/5000000000000000000000 : ℝ)*base89 + (45043431/5000000000000000000000 : ℝ)*base91 + (45043431/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12546737529803088796366071/1613281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (606568267/50000000000000 : ℝ)*(base19) + (1387448467/100000000000000 : ℝ)*(base23) + (27744603/20000000000000 : ℝ)*(upper3) + (33447659/50000000000000 : ℝ)*(lower4) + (170433787/100000000000000 : ℝ)*(upper5) + (2266002027454009/50000000000000 : ℝ)*(major0) + (2266002027454009/50000000000000 : ℝ)*(major1) + (2266002027454009/50000000000000 : ℝ)*(major2) + (3174742697/12500000000000 : ℝ)*(sp1) + (3508798549/12500000000000 : ℝ)*(sp2) + (776621344971333/12500000000000 : ℝ)*(sp4) + (3106472074346277/50000000000000 : ℝ)*(sp5) + (1242588260386761/20000000000000 : ℝ)*(sp6) + (712759272701721/25000000000000 : ℝ)*(sp7) + (712759272701721/25000000000000 : ℝ)*(f.failure) + (776621344971333/12500000000000 : ℝ)*(f.sum) + (7094283817079/3097500000000000000000000000 : ℝ)*base66 + (52088839075619069/5531250000000000000000000000000 : ℝ)*base68 + (5190443211119069/5531250000000000000000000000000 : ℝ)*base70 + (20522112562568431/5531250000000000000000000000000 : ℝ)*base71 + (3236326727099/3097500000000000000000000000 : ℝ)*base74 + (56803957795431569/5531250000000000000000000000000 : ℝ)*base76 + (23471492704619069/5531250000000000000000000000000 : ℝ)*base78 + (1295497505650319/5531250000000000000000000000000 : ℝ)*base80 + (11805934058687/6195000000000000000000000000 : ℝ)*base81 + (16644041/1250000000000000000000 : ℝ)*base89 + (16644041/1250000000000000000000 : ℝ)*base91 + (16644041/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1449_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1449_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1449_s5_0 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-977499969/5000000000 : ℝ)*x 0 + (216293589/400000000 : ℝ)*x 1 + (5247196289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977499969/5000000000 : ℝ)^4409 ≤ (2386386491661/20000000000000 : ℝ)^3385 := by
    have hnat : (977499969 : ℕ)^4409*20000000000000^3385 ≤ 2386386491661^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977499969 5000000000 2386386491661 20000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216293589/400000000 : ℝ)^4409 ≤ (22448031225697/50000000000000 : ℝ)^3385 := by
    have hnat : (216293589 : ℕ)^4409*50000000000000^3385 ≤ 22448031225697^3385*400000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216293589 400000000 22448031225697 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247196289/10000000000 : ℝ)^4409 ≤ (21586002541467/50000000000000 : ℝ)^3385 := by
    have hnat : (5247196289 : ℕ)^4409*50000000000000^3385 ≤ 21586002541467^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247196289 10000000000 21586002541467 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977499969/5000000000 : ℝ), (216293589/400000000 : ℝ), (5247196289/10000000000 : ℝ)] ![(2386386491661/20000000000000 : ℝ), (22448031225697/50000000000000 : ℝ), (21586002541467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977499969/5000000000 : ℝ)|^4409 ≤ (2386386491661/20000000000000 : ℝ)^3385
        have hw : |(-977499969/5000000000 : ℝ)|=(977499969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216293589/400000000 : ℝ)|^4409 ≤ (22448031225697/50000000000000 : ℝ)^3385
        have hw : |(216293589/400000000 : ℝ)|=(216293589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247196289/10000000000 : ℝ)|^4409 ≤ (21586002541467/50000000000000 : ℝ)^3385
        have hw : |(5247196289/10000000000 : ℝ)|=(5247196289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s5_1 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334183633/625000000 : ℝ)*x 0 + (-2036520669/10000000000 : ℝ)*x 1 + (5247196287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334183633/625000000 : ℝ)^4409 ≤ (5530494567769/12500000000000 : ℝ)^3385 := by
    have hnat : (334183633 : ℕ)^4409*12500000000000^3385 ≤ 5530494567769^3385*625000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334183633 625000000 5530494567769 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036520669/10000000000 : ℝ)^4409 ≤ (1258403839113/10000000000000 : ℝ)^3385 := by
    have hnat : (2036520669 : ℕ)^4409*10000000000000^3385 ≤ 1258403839113^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036520669 10000000000 1258403839113 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247196287/10000000000 : ℝ)^4409 ≤ (43172005061501/100000000000000 : ℝ)^3385 := by
    have hnat : (5247196287 : ℕ)^4409*100000000000000^3385 ≤ 43172005061501^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247196287 10000000000 43172005061501 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334183633/625000000 : ℝ), (-2036520669/10000000000 : ℝ), (5247196287/10000000000 : ℝ)] ![(5530494567769/12500000000000 : ℝ), (1258403839113/10000000000000 : ℝ), (43172005061501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334183633/625000000 : ℝ)|^4409 ≤ (5530494567769/12500000000000 : ℝ)^3385
        have hw : |(334183633/625000000 : ℝ)|=(334183633/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2036520669/10000000000 : ℝ)|^4409 ≤ (1258403839113/10000000000000 : ℝ)^3385
        have hw : |(-2036520669/10000000000 : ℝ)|=(2036520669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247196287/10000000000 : ℝ)|^4409 ≤ (43172005061501/100000000000000 : ℝ)^3385
        have hw : |(5247196287/10000000000 : ℝ)|=(5247196287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s5_2 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346938183/10000000000 : ℝ)*x 0 + (5247196227/10000000000 : ℝ)*x 1 + (-81460827/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346938183/10000000000 : ℝ)^4409 ≤ (44243957134931/100000000000000 : ℝ)^3385 := by
    have hnat : (5346938183 : ℕ)^4409*100000000000000^3385 ≤ 44243957134931^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346938183 10000000000 44243957134931 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247196227/10000000000 : ℝ)^4409 ≤ (21586002209253/50000000000000 : ℝ)^3385 := by
    have hnat : (5247196227 : ℕ)^4409*50000000000000^3385 ≤ 21586002209253^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247196227 10000000000 21586002209253 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81460827/400000000 : ℝ)^4409 ≤ (12584038439421/100000000000000 : ℝ)^3385 := by
    have hnat : (81460827 : ℕ)^4409*100000000000000^3385 ≤ 12584038439421^3385*400000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81460827 400000000 12584038439421 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346938183/10000000000 : ℝ), (5247196227/10000000000 : ℝ), (-81460827/400000000 : ℝ)] ![(44243957134931/100000000000000 : ℝ), (21586002209253/50000000000000 : ℝ), (12584038439421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346938183/10000000000 : ℝ)|^4409 ≤ (44243957134931/100000000000000 : ℝ)^3385
        have hw : |(5346938183/10000000000 : ℝ)|=(5346938183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247196227/10000000000 : ℝ)|^4409 ≤ (21586002209253/50000000000000 : ℝ)^3385
        have hw : |(5247196227/10000000000 : ℝ)|=(5247196227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81460827/400000000 : ℝ)|^4409 ≤ (12584038439421/100000000000000 : ℝ)^3385
        have hw : |(-81460827/400000000 : ℝ)|=(81460827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s5_3 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299387231/10000000000 : ℝ)*x 0 + (2064026353/5000000000 : ℝ)*x 1 + (111925923/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299387231/10000000000 : ℝ)^4409 ≤ (16652444330977/50000000000000 : ℝ)^3385 := by
    have hnat : (4299387231 : ℕ)^4409*50000000000000^3385 ≤ 16652444330977^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299387231 10000000000 16652444330977 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064026353/5000000000 : ℝ)^4409 ≤ (789666871367/2500000000000 : ℝ)^3385 := by
    have hnat : (2064026353 : ℕ)^4409*2500000000000^3385 ≤ 789666871367^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064026353 5000000000 789666871367 2500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111925923/250000000 : ℝ)^4409 ≤ (17554218232489/50000000000000 : ℝ)^3385 := by
    have hnat : (111925923 : ℕ)^4409*50000000000000^3385 ≤ 17554218232489^3385*250000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111925923 250000000 17554218232489 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299387231/10000000000 : ℝ), (2064026353/5000000000 : ℝ), (111925923/250000000 : ℝ)] ![(16652444330977/50000000000000 : ℝ), (789666871367/2500000000000 : ℝ), (17554218232489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299387231/10000000000 : ℝ)|^4409 ≤ (16652444330977/50000000000000 : ℝ)^3385
        have hw : |(4299387231/10000000000 : ℝ)|=(4299387231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064026353/5000000000 : ℝ)|^4409 ≤ (789666871367/2500000000000 : ℝ)^3385
        have hw : |(2064026353/5000000000 : ℝ)|=(2064026353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(111925923/250000000 : ℝ)|^4409 ≤ (17554218232489/50000000000000 : ℝ)^3385
        have hw : |(111925923/250000000 : ℝ)|=(111925923/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s5_4 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61094099/312500000 : ℝ)*x 0 + (1311943983/2500000000 : ℝ)*x 1 + (1081351411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61094099/312500000 : ℝ)^4409 ≤ (11932021732429/100000000000000 : ℝ)^3385 := by
    have hnat : (61094099 : ℕ)^4409*100000000000000^3385 ≤ 11932021732429^3385*312500000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61094099 312500000 11932021732429 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311943983/2500000000 : ℝ)^4409 ≤ (1079455424477/2500000000000 : ℝ)^3385 := by
    have hnat : (1311943983 : ℕ)^4409*2500000000000^3385 ≤ 1079455424477^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311943983 2500000000 1079455424477 2500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081351411/2000000000 : ℝ)^4409 ≤ (22444880637749/50000000000000 : ℝ)^3385 := by
    have hnat : (1081351411 : ℕ)^4409*50000000000000^3385 ≤ 22444880637749^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081351411 2000000000 22444880637749 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61094099/312500000 : ℝ), (1311943983/2500000000 : ℝ), (1081351411/2000000000 : ℝ)] ![(11932021732429/100000000000000 : ℝ), (1079455424477/2500000000000 : ℝ), (22444880637749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61094099/312500000 : ℝ)|^4409 ≤ (11932021732429/100000000000000 : ℝ)^3385
        have hw : |(-61094099/312500000 : ℝ)|=(61094099/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311943983/2500000000 : ℝ)|^4409 ≤ (1079455424477/2500000000000 : ℝ)^3385
        have hw : |(1311943983/2500000000 : ℝ)|=(1311943983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081351411/2000000000 : ℝ)|^4409 ≤ (22444880637749/50000000000000 : ℝ)^3385
        have hw : |(1081351411/2000000000 : ℝ)|=(1081351411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s5_5 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305224977/10000000000 : ℝ)*x 0 + (-375391979/2000000000 : ℝ)*x 1 + (1351689277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305224977/10000000000 : ℝ)^4409 ≤ (5474363987179/12500000000000 : ℝ)^3385 := by
    have hnat : (5305224977 : ℕ)^4409*12500000000000^3385 ≤ 5474363987179^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305224977 10000000000 5474363987179 12500000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375391979/2000000000 : ℝ)^4409 ≤ (11315326234507/100000000000000 : ℝ)^3385 := by
    have hnat : (375391979 : ℕ)^4409*100000000000000^3385 ≤ 11315326234507^3385*2000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375391979 2000000000 11315326234507 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351689277/2500000000 : ℝ)^4409 ≤ (44889761848647/100000000000000 : ℝ)^3385 := by
    have hnat : (1351689277 : ℕ)^4409*100000000000000^3385 ≤ 44889761848647^3385*2500000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351689277 2500000000 44889761848647 100000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305224977/10000000000 : ℝ), (-375391979/2000000000 : ℝ), (1351689277/2500000000 : ℝ)] ![(5474363987179/12500000000000 : ℝ), (11315326234507/100000000000000 : ℝ), (44889761848647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305224977/10000000000 : ℝ)|^4409 ≤ (5474363987179/12500000000000 : ℝ)^3385
        have hw : |(5305224977/10000000000 : ℝ)|=(5305224977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375391979/2000000000 : ℝ)|^4409 ≤ (11315326234507/100000000000000 : ℝ)^3385
        have hw : |(-375391979/2000000000 : ℝ)|=(375391979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351689277/2500000000 : ℝ)|^4409 ≤ (44889761848647/100000000000000 : ℝ)^3385
        have hw : |(1351689277/2500000000 : ℝ)|=(1351689277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s5_6 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652612499/5000000000 : ℝ)*x 0 + (2703378557/5000000000 : ℝ)*x 1 + (-938479929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652612499/5000000000 : ℝ)^4409 ≤ (4379491212323/10000000000000 : ℝ)^3385 := by
    have hnat : (2652612499 : ℕ)^4409*10000000000000^3385 ≤ 4379491212323^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652612499 5000000000 4379491212323 10000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703378557/5000000000 : ℝ)^4409 ≤ (11222440478383/25000000000000 : ℝ)^3385 := by
    have hnat : (2703378557 : ℕ)^4409*25000000000000^3385 ≤ 11222440478383^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703378557 5000000000 11222440478383 25000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (938479929/5000000000 : ℝ)^4409 ≤ (5657662971987/50000000000000 : ℝ)^3385 := by
    have hnat : (938479929 : ℕ)^4409*50000000000000^3385 ≤ 5657662971987^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938479929 5000000000 5657662971987 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652612499/5000000000 : ℝ), (2703378557/5000000000 : ℝ), (-938479929/5000000000 : ℝ)] ![(4379491212323/10000000000000 : ℝ), (11222440478383/25000000000000 : ℝ), (5657662971987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652612499/5000000000 : ℝ)|^4409 ≤ (4379491212323/10000000000000 : ℝ)^3385
        have hw : |(2652612499/5000000000 : ℝ)|=(2652612499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703378557/5000000000 : ℝ)|^4409 ≤ (11222440478383/25000000000000 : ℝ)^3385
        have hw : |(2703378557/5000000000 : ℝ)|=(2703378557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-938479929/5000000000 : ℝ)|^4409 ≤ (5657662971987/50000000000000 : ℝ)^3385
        have hw : |(-938479929/5000000000 : ℝ)|=(938479929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1449_s5_7 (p : ℝ) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299411643/10000000000 : ℝ)*x 0 + (4475773677/10000000000 : ℝ)*x 1 + (2064661259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299411643/10000000000 : ℝ)^4409 ≤ (520392733977/1562500000000 : ℝ)^3385 := by
    have hnat : (4299411643 : ℕ)^4409*1562500000000^3385 ≤ 520392733977^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299411643 10000000000 520392733977 1562500000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475773677/10000000000 : ℝ)^4409 ≤ (17547767030991/50000000000000 : ℝ)^3385 := by
    have hnat : (4475773677 : ℕ)^4409*50000000000000^3385 ≤ 17547767030991^3385*10000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475773677 10000000000 17547767030991 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064661259/5000000000 : ℝ)^4409 ≤ (15799665474949/50000000000000 : ℝ)^3385 := by
    have hnat : (2064661259 : ℕ)^4409*50000000000000^3385 ≤ 15799665474949^3385*5000000000^4409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064661259 5000000000 15799665474949 50000000000000 4409 3385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4409/1024 : ℝ)) 4409 3385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299411643/10000000000 : ℝ), (4475773677/10000000000 : ℝ), (2064661259/5000000000 : ℝ)] ![(520392733977/1562500000000 : ℝ), (17547767030991/50000000000000 : ℝ), (15799665474949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299411643/10000000000 : ℝ)|^4409 ≤ (520392733977/1562500000000 : ℝ)^3385
        have hw : |(4299411643/10000000000 : ℝ)|=(4299411643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475773677/10000000000 : ℝ)|^4409 ≤ (17547767030991/50000000000000 : ℝ)^3385
        have hw : |(4475773677/10000000000 : ℝ)|=(4475773677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064661259/5000000000 : ℝ)|^4409 ≤ (15799665474949/50000000000000 : ℝ)^3385
        have hw : |(2064661259/5000000000 : ℝ)|=(2064661259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1449_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11377/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11357/100000 : ℝ) ^ (551/128 : ℝ) ≤ (4287213814580037/50000000000000000000 : ℝ) := by
    have hpowers : (11357/100000 : ℝ)^551 ≤ (4287213814580037/50000000000000000000 : ℝ)^128 := by
      have hnat : (11357 : ℕ)^551*50000000000000000000^128 ≤ 4287213814580037^128*100000^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11357 100000 4287213814580037 50000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11357/100000 : ℝ)) (X := (4287213814580037/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hpowhi : (1849/12500 : ℝ) ^ (551/128 : ℝ) ≤ (13371963038005551/50000000000000000000 : ℝ) := by
    have hpowers : (1849/12500 : ℝ)^551 ≤ (13371963038005551/50000000000000000000 : ℝ)^128 := by
      have hnat : (1849 : ℕ)^551*50000000000000000000^128 ≤ 13371963038005551^128*12500^551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1849 12500 13371963038005551 50000000000000000000 551 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1849/12500 : ℝ)) (X := (13371963038005551/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004287213814580037/25000000000000000000 : ℝ) ≤ (10000398350090247/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (25004287213814580037/25000000000000000000 : ℝ)^128 ≤ (10000398350090247/10000000000000000 : ℝ)^551 := by
      have hnat : (25004287213814580037 : ℕ)^128*10000000000000000^551 ≤ 10000398350090247^551*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004287213814580037 25000000000000000000 10000398350090247 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000398350090247/10000000000000000 : ℝ)) (X := (25004287213814580037/25000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504414794213146397/12500000000000000000 : ℝ) ≤ (156262817991521/156250000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (12504414794213146397/12500000000000000000 : ℝ)^128 ≤ (156262817991521/156250000000000 : ℝ)^551 := by
      have hnat : (12504414794213146397 : ℕ)^128*156250000000000^551 ≤ 156262817991521^551*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504414794213146397 12500000000000000000 156262817991521 156250000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156262817991521/156250000000000 : ℝ)) (X := (12504414794213146397/12500000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013371963038005551/25000000000000000000 : ℝ) ≤ (10001242352824441/10000000000000000 : ℝ) ^ (551/128 : ℝ) := by
    have hpowers : (25013371963038005551/25000000000000000000 : ℝ)^128 ≤ (10001242352824441/10000000000000000 : ℝ)^551 := by
      have hnat : (25013371963038005551 : ℕ)^128*10000000000000000^551 ≤ 10001242352824441^551*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013371963038005551 25000000000000000000 10001242352824441 10000000000000000 128 551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001242352824441/10000000000000000 : ℝ)) (X := (25013371963038005551/25000000000000000000 : ℝ)) (by norm_num) 551 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4287213814580037/50000000000000000000 : ℝ) ≤ ((34341782993507757187/34350000000000000000 : ℝ)+2*(422001367097/343500000000000 : ℝ)*(11357/100000 : ℝ))^(551/128 : ℝ) := by
    rw [show (34341782993507757187/34350000000000000000 : ℝ)+2*(422001367097/343500000000000 : ℝ)*(11357/100000 : ℝ)=(10000398350090247/10000000000000000 : ℝ) by norm_num, show 1+2*(4287213814580037/50000000000000000000 : ℝ)=(25004287213814580037/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13371963038005551/50000000000000000000 : ℝ)+(4287213814580037/50000000000000000000 : ℝ) ≤ ((34341782993507757187/34350000000000000000 : ℝ)+(422001367097/343500000000000 : ℝ)*((1849/12500 : ℝ)+(11357/100000 : ℝ)))^(551/128 : ℝ) := by
    rw [show (34341782993507757187/34350000000000000000 : ℝ)+(422001367097/343500000000000 : ℝ)*((1849/12500 : ℝ)+(11357/100000 : ℝ))=(156262817991521/156250000000000 : ℝ) by norm_num, show 1+(13371963038005551/50000000000000000000 : ℝ)+(4287213814580037/50000000000000000000 : ℝ)=(12504414794213146397/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13371963038005551/50000000000000000000 : ℝ) ≤ ((34341782993507757187/34350000000000000000 : ℝ)+2*(422001367097/343500000000000 : ℝ)*(1849/12500 : ℝ))^(551/128 : ℝ) := by
    rw [show (34341782993507757187/34350000000000000000 : ℝ)+2*(422001367097/343500000000000 : ℝ)*(1849/12500 : ℝ)=(10001242352824441/10000000000000000 : ℝ) by norm_num, show 1+2*(13371963038005551/50000000000000000000 : ℝ)=(25013371963038005551/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34341782993507757187/34350000000000000000 : ℝ)*(X 1 0+X 2 0)+(422001367097/343500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (34341782993507757187/34350000000000000000 : ℝ)) (alpha := (422001367097/343500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34341782993507757187/34350000000000000000 : ℝ)*(X 0 1+X 2 1)+(422001367097/343500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (34341782993507757187/34350000000000000000 : ℝ)) (alpha := (422001367097/343500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34341782993507757187/34350000000000000000 : ℝ)*(X 0 2+X 1 2)+(422001367097/343500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (551/128 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (34341782993507757187/34350000000000000000 : ℝ)) (alpha := (422001367097/343500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-977499969/5000000000 : ℝ)*X 0 0+(216293589/400000000 : ℝ)*X 0 1+(5247196289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334183633/625000000 : ℝ)*X 1 0+(-2036520669/10000000000 : ℝ)*X 1 1+(5247196287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346938183/10000000000 : ℝ)*X 2 0+(5247196227/10000000000 : ℝ)*X 2 1+(-81460827/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4299387231/10000000000 : ℝ)*X 0 0+(2064026353/5000000000 : ℝ)*X 0 1+(111925923/250000000 : ℝ)*X 0 2+(4299387231/10000000000 : ℝ)*X 1 0+(2064026353/5000000000 : ℝ)*X 1 1+(111925923/250000000 : ℝ)*X 1 2+(4299387231/10000000000 : ℝ)*X 2 0+(2064026353/5000000000 : ℝ)*X 2 1+(111925923/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-61094099/312500000 : ℝ)*X 0 0+(1311943983/2500000000 : ℝ)*X 0 1+(1081351411/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305224977/10000000000 : ℝ)*X 1 0+(-375391979/2000000000 : ℝ)*X 1 1+(1351689277/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652612499/5000000000 : ℝ)*X 2 0+(2703378557/5000000000 : ℝ)*X 2 1+(-938479929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4299411643/10000000000 : ℝ)*X 0 0+(4475773677/10000000000 : ℝ)*X 0 1+(2064661259/5000000000 : ℝ)*X 0 2+(4299411643/10000000000 : ℝ)*X 1 0+(4475773677/10000000000 : ℝ)*X 1 1+(2064661259/5000000000 : ℝ)*X 1 2+(4299411643/10000000000 : ℝ)*X 2 0+(4475773677/10000000000 : ℝ)*X 2 1+(2064661259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1449_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2999144477141344832397/286250000000000000000000000 : ℝ) := by norm_num
    linear_combination (458275099/25000000000000 : ℝ)*(base19) + (1750585387/100000000000000 : ℝ)*(base23) + (39232447/50000000000000 : ℝ)*(lower2) + (32696171/12500000000000 : ℝ)*(upper3) + (157911949/100000000000000 : ℝ)*(upper5) + (910997617818103/20000000000000 : ℝ)*(major0) + (910997617818103/20000000000000 : ℝ)*(major1) + (910997617818103/20000000000000 : ℝ)*(major2) + (6244441588035663/100000000000000 : ℝ)*(sp0) + (6244477885760807/100000000000000 : ℝ)*(sp1) + (780559746034477/12500000000000 : ℝ)*(sp2) + (2865476354452693/100000000000000 : ℝ)*(sp3) + (1906541277/5000000000000 : ℝ)*(sp4) + (4938905443/25000000000000 : ℝ)*(sp7) + (89546753439827/3125000000000 : ℝ)*(f.failure) + (6244479718861203/100000000000000 : ℝ)*(f.sum) + (3430709651071/858750000000000000000000000 : ℝ)*base66 + (214980750332352087/229000000000000000000000000000000 : ℝ)*base67 + (85898509858352087/229000000000000000000000000000000 : ℝ)*base69 + (2086962725889647913/229000000000000000000000000000000 : ℝ)*base72 + (5273209531637/1717500000000000000000000000 : ℝ)*base74 + (635937204700352087/229000000000000000000000000000000 : ℝ)*base75 + (1173145790217647913/229000000000000000000000000000000 : ℝ)*base78 + (1170705183100647913/229000000000000000000000000000000 : ℝ)*base80 + (9347187181369/3435000000000000000000000000 : ℝ)*base82 + (1473833/156250000000000000000 : ℝ)*base90 + (1473833/156250000000000000000 : ℝ)*base92 + (1473833/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (777569117684651091552515249/143125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (755399633/100000000000000 : ℝ)*(base19) + (427563773/50000000000000 : ℝ)*(base23) + (112203691/100000000000000 : ℝ)*(upper3) + (28231977/100000000000000 : ℝ)*(lower4) + (14119599/12500000000000 : ℝ)*(upper5) + (1147058060707627/25000000000000 : ℝ)*(major0) + (1147058060707627/25000000000000 : ℝ)*(major1) + (1147058060707627/25000000000000 : ℝ)*(major2) + (4200702207/25000000000000 : ℝ)*(sp1) + (3910352149/20000000000000 : ℝ)*(sp2) + (6290054639647169/100000000000000 : ℝ)*(sp4) + (6290037081438707/100000000000000 : ℝ)*(sp5) + (6290034232758877/100000000000000 : ℝ)*(sp6) + (721602416230149/25000000000000 : ℝ)*(sp7) + (721602416230149/25000000000000 : ℝ)*(f.failure) + (6290054639647169/100000000000000 : ℝ)*(f.sum) + (11084089436003/2146875000000000000000000000 : ℝ)*base66 + (1337106801401044917/286250000000000000000000000000000 : ℝ)*base68 + (3127271092015205083/286250000000000000000000000000000 : ℝ)*base69 + (1313402424874794917/286250000000000000000000000000000 : ℝ)*base72 + (59755407733849/17175000000000000000000000000 : ℝ)*base74 + (2071159246248955083/286250000000000000000000000000000 : ℝ)*base75 + (79279877977294917/286250000000000000000000000000000 : ℝ)*base78 + (188377990107294917/286250000000000000000000000000000 : ℝ)*base80 + (30892720698551/17175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10338229/1250000000000000000000 : ℝ)*base89 + (10338229/1250000000000000000000 : ℝ)*base91 + (10338229/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1449_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1449_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1449_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (787/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1449_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1449_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1449_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (551/128 : ℝ) ≤ p) (hpb : p ≤ (4409/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79479921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (787/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1309/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1449_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

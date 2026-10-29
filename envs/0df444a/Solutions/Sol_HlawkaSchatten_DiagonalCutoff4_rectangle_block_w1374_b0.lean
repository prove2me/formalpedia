-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1374_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:25.052602+00:00
-- url     : https://prove2.me/submissions/a3f9b051-c6f8-45d1-a3f6-83dc93ebbb3c

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
theorem support_rectangle_w1374_s0_0 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-447594743/2500000000 : ℝ)*x 0 + (2991605203/5000000000 : ℝ)*x 1 + (4818486251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447594743/2500000000 : ℝ)^2167 ≤ (2628886763379/25000000000000 : ℝ)^1655 := by
    have hnat : (447594743 : ℕ)^2167*25000000000000^1655 ≤ 2628886763379^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447594743 2500000000 2628886763379 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2991605203/5000000000 : ℝ)^2167 ≤ (10208346873263/20000000000000 : ℝ)^1655 := by
    have hnat : (2991605203 : ℕ)^2167*20000000000000^1655 ≤ 10208346873263^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991605203 5000000000 10208346873263 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4818486251/10000000000 : ℝ)^2167 ≤ (38442718556371/100000000000000 : ℝ)^1655 := by
    have hnat : (4818486251 : ℕ)^2167*100000000000000^1655 ≤ 38442718556371^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4818486251 10000000000 38442718556371 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-447594743/2500000000 : ℝ), (2991605203/5000000000 : ℝ), (4818486251/10000000000 : ℝ)] ![(2628886763379/25000000000000 : ℝ), (10208346873263/20000000000000 : ℝ), (38442718556371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-447594743/2500000000 : ℝ)|^2167 ≤ (2628886763379/25000000000000 : ℝ)^1655
        have hw : |(-447594743/2500000000 : ℝ)|=(447594743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2991605203/5000000000 : ℝ)|^2167 ≤ (10208346873263/20000000000000 : ℝ)^1655
        have hw : |(2991605203/5000000000 : ℝ)|=(2991605203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4818486251/10000000000 : ℝ)|^2167 ≤ (38442718556371/100000000000000 : ℝ)^1655
        have hw : |(4818486251/10000000000 : ℝ)|=(4818486251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s0_1 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1374558161/2500000000 : ℝ)*x 0 + (-612719511/2500000000 : ℝ)*x 1 + (240924343/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374558161/2500000000 : ℝ)^2167 ≤ (22846890181397/50000000000000 : ℝ)^1655 := by
    have hnat : (1374558161 : ℕ)^2167*50000000000000^1655 ≤ 22846890181397^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374558161 2500000000 22846890181397 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (612719511/2500000000 : ℝ)^2167 ≤ (15863494707233/100000000000000 : ℝ)^1655 := by
    have hnat : (612719511 : ℕ)^2167*100000000000000^1655 ≤ 15863494707233^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612719511 2500000000 15863494707233 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240924343/500000000 : ℝ)^2167 ≤ (7688544983639/20000000000000 : ℝ)^1655 := by
    have hnat : (240924343 : ℕ)^2167*20000000000000^1655 ≤ 7688544983639^1655*500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240924343 500000000 7688544983639 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374558161/2500000000 : ℝ), (-612719511/2500000000 : ℝ), (240924343/500000000 : ℝ)] ![(22846890181397/50000000000000 : ℝ), (15863494707233/100000000000000 : ℝ), (7688544983639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374558161/2500000000 : ℝ)|^2167 ≤ (22846890181397/50000000000000 : ℝ)^1655
        have hw : |(1374558161/2500000000 : ℝ)|=(1374558161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-612719511/2500000000 : ℝ)|^2167 ≤ (15863494707233/100000000000000 : ℝ)^1655
        have hw : |(-612719511/2500000000 : ℝ)|=(612719511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240924343/500000000 : ℝ)|^2167 ≤ (7688544983639/20000000000000 : ℝ)^1655
        have hw : |(240924343/500000000 : ℝ)|=(240924343/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s0_2 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5498232531/10000000000 : ℝ)*x 0 + (963697233/2000000000 : ℝ)*x 1 + (-490175809/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5498232531/10000000000 : ℝ)^2167 ≤ (45693779133167/100000000000000 : ℝ)^1655 := by
    have hnat : (5498232531 : ℕ)^2167*100000000000000^1655 ≤ 45693779133167^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498232531 10000000000 45693779133167 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963697233/2000000000 : ℝ)^2167 ≤ (7688543531597/20000000000000 : ℝ)^1655 := by
    have hnat : (963697233 : ℕ)^2167*20000000000000^1655 ≤ 7688543531597^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963697233 2000000000 7688543531597 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490175809/2000000000 : ℝ)^2167 ≤ (3965875797669/25000000000000 : ℝ)^1655 := by
    have hnat : (490175809 : ℕ)^2167*25000000000000^1655 ≤ 3965875797669^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490175809 2000000000 3965875797669 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5498232531/10000000000 : ℝ), (963697233/2000000000 : ℝ), (-490175809/2000000000 : ℝ)] ![(45693779133167/100000000000000 : ℝ), (7688543531597/20000000000000 : ℝ), (3965875797669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5498232531/10000000000 : ℝ)|^2167 ≤ (45693779133167/100000000000000 : ℝ)^1655
        have hw : |(5498232531/10000000000 : ℝ)|=(5498232531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(963697233/2000000000 : ℝ)|^2167 ≤ (7688543531597/20000000000000 : ℝ)^1655
        have hw : |(963697233/2000000000 : ℝ)|=(963697233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490175809/2000000000 : ℝ)|^2167 ≤ (3965875797669/25000000000000 : ℝ)^1655
        have hw : |(-490175809/2000000000 : ℝ)|=(490175809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s0_3 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1043498893/2500000000 : ℝ)*x 0 + (776282743/2500000000 : ℝ)*x 1 + (5574133651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043498893/2500000000 : ℝ)^2167 ≤ (31853989785457/100000000000000 : ℝ)^1655 := by
    have hnat : (1043498893 : ℕ)^2167*100000000000000^1655 ≤ 31853989785457^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043498893 2500000000 31853989785457 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776282743/2500000000 : ℝ)^2167 ≤ (5406135831053/25000000000000 : ℝ)^1655 := by
    have hnat : (776282743 : ℕ)^2167*25000000000000^1655 ≤ 5406135831053^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776282743 2500000000 5406135831053 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5574133651/10000000000 : ℝ)^2167 ≤ (46521466881201/100000000000000 : ℝ)^1655 := by
    have hnat : (5574133651 : ℕ)^2167*100000000000000^1655 ≤ 46521466881201^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5574133651 10000000000 46521466881201 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1043498893/2500000000 : ℝ), (776282743/2500000000 : ℝ), (5574133651/10000000000 : ℝ)] ![(31853989785457/100000000000000 : ℝ), (5406135831053/25000000000000 : ℝ), (46521466881201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1043498893/2500000000 : ℝ)|^2167 ≤ (31853989785457/100000000000000 : ℝ)^1655
        have hw : |(1043498893/2500000000 : ℝ)|=(1043498893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776282743/2500000000 : ℝ)|^2167 ≤ (5406135831053/25000000000000 : ℝ)^1655
        have hw : |(776282743/2500000000 : ℝ)|=(776282743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5574133651/10000000000 : ℝ)|^2167 ≤ (46521466881201/100000000000000 : ℝ)^1655
        have hw : |(5574133651/10000000000 : ℝ)|=(5574133651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s0_4 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-897335261/5000000000 : ℝ)*x 0 + (4848403409/10000000000 : ℝ)*x 1 + (74402799/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897335261/5000000000 : ℝ)^2167 ≤ (10548562935223/100000000000000 : ℝ)^1655 := by
    have hnat : (897335261 : ℕ)^2167*100000000000000^1655 ≤ 10548562935223^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897335261 5000000000 10548562935223 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4848403409/10000000000 : ℝ)^2167 ≤ (9688885810723/25000000000000 : ℝ)^1655 := by
    have hnat : (4848403409 : ℕ)^2167*25000000000000^1655 ≤ 9688885810723^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4848403409 10000000000 9688885810723 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74402799/125000000 : ℝ)^2167 ≤ (2534794690327/5000000000000 : ℝ)^1655 := by
    have hnat : (74402799 : ℕ)^2167*5000000000000^1655 ≤ 2534794690327^1655*125000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74402799 125000000 2534794690327 5000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-897335261/5000000000 : ℝ), (4848403409/10000000000 : ℝ), (74402799/125000000 : ℝ)] ![(10548562935223/100000000000000 : ℝ), (9688885810723/25000000000000 : ℝ), (2534794690327/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-897335261/5000000000 : ℝ)|^2167 ≤ (10548562935223/100000000000000 : ℝ)^1655
        have hw : |(-897335261/5000000000 : ℝ)|=(897335261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4848403409/10000000000 : ℝ)|^2167 ≤ (9688885810723/25000000000000 : ℝ)^1655
        have hw : |(4848403409/10000000000 : ℝ)|=(4848403409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74402799/125000000 : ℝ)|^2167 ≤ (2534794690327/5000000000000 : ℝ)^1655
        have hw : |(74402799/125000000 : ℝ)|=(74402799/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s0_5 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5180616603/10000000000 : ℝ)*x 0 + (-32928591/250000000 : ℝ)*x 1 + (1488055647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180616603/10000000000 : ℝ)^2167 ≤ (42268896660369/100000000000000 : ℝ)^1655 := by
    have hnat : (5180616603 : ℕ)^2167*100000000000000^1655 ≤ 42268896660369^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180616603 10000000000 42268896660369 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32928591/250000000 : ℝ)^2167 ≤ (879403047351/12500000000000 : ℝ)^1655 := by
    have hnat : (32928591 : ℕ)^2167*12500000000000^1655 ≤ 879403047351^1655*250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32928591 250000000 879403047351 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1488055647/2500000000 : ℝ)^2167 ≤ (50695878952019/100000000000000 : ℝ)^1655 := by
    have hnat : (1488055647 : ℕ)^2167*100000000000000^1655 ≤ 50695878952019^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488055647 2500000000 50695878952019 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180616603/10000000000 : ℝ), (-32928591/250000000 : ℝ), (1488055647/2500000000 : ℝ)] ![(42268896660369/100000000000000 : ℝ), (879403047351/12500000000000 : ℝ), (50695878952019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180616603/10000000000 : ℝ)|^2167 ≤ (42268896660369/100000000000000 : ℝ)^1655
        have hw : |(5180616603/10000000000 : ℝ)|=(5180616603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32928591/250000000 : ℝ)|^2167 ≤ (879403047351/12500000000000 : ℝ)^1655
        have hw : |(-32928591/250000000 : ℝ)|=(32928591/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1488055647/2500000000 : ℝ)|^2167 ≤ (50695878952019/100000000000000 : ℝ)^1655
        have hw : |(1488055647/2500000000 : ℝ)|=(1488055647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s0_6 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2590307687/5000000000 : ℝ)*x 0 + (1488056309/2500000000 : ℝ)*x 1 + (-263428259/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2590307687/5000000000 : ℝ)^2167 ≤ (42268883530747/100000000000000 : ℝ)^1655 := by
    have hnat : (2590307687 : ℕ)^2167*100000000000000^1655 ≤ 42268883530747^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590307687 5000000000 42268883530747 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1488056309/2500000000 : ℝ)^2167 ≤ (50695908482629/100000000000000 : ℝ)^1655 := by
    have hnat : (1488056309 : ℕ)^2167*100000000000000^1655 ≤ 50695908482629^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488056309 2500000000 50695908482629 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263428259/2000000000 : ℝ)^2167 ≤ (3517603989317/50000000000000 : ℝ)^1655 := by
    have hnat : (263428259 : ℕ)^2167*50000000000000^1655 ≤ 3517603989317^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263428259 2000000000 3517603989317 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2590307687/5000000000 : ℝ), (1488056309/2500000000 : ℝ), (-263428259/2000000000 : ℝ)] ![(42268883530747/100000000000000 : ℝ), (50695908482629/100000000000000 : ℝ), (3517603989317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2590307687/5000000000 : ℝ)|^2167 ≤ (42268883530747/100000000000000 : ℝ)^1655
        have hw : |(2590307687/5000000000 : ℝ)|=(2590307687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1488056309/2500000000 : ℝ)|^2167 ≤ (50695908482629/100000000000000 : ℝ)^1655
        have hw : |(1488056309/2500000000 : ℝ)|=(1488056309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263428259/2000000000 : ℝ)|^2167 ≤ (3517603989317/50000000000000 : ℝ)^1655
        have hw : |(-263428259/2000000000 : ℝ)|=(263428259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s0_7 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (418308461/1000000000 : ℝ)*x 0 + (5510717777/10000000000 : ℝ)*x 1 + (3170818383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418308461/1000000000 : ℝ)^2167 ≤ (31944842282747/100000000000000 : ℝ)^1655 := by
    have hnat : (418308461 : ℕ)^2167*100000000000000^1655 ≤ 31944842282747^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418308461 1000000000 31944842282747 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510717777/10000000000 : ℝ)^2167 ≤ (22914843474259/50000000000000 : ℝ)^1655 := by
    have hnat : (5510717777 : ℕ)^2167*50000000000000^1655 ≤ 22914843474259^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510717777 10000000000 22914843474259 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3170818383/10000000000 : ℝ)^2167 ≤ (22225470763387/100000000000000 : ℝ)^1655 := by
    have hnat : (3170818383 : ℕ)^2167*100000000000000^1655 ≤ 22225470763387^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170818383 10000000000 22225470763387 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418308461/1000000000 : ℝ), (5510717777/10000000000 : ℝ), (3170818383/10000000000 : ℝ)] ![(31944842282747/100000000000000 : ℝ), (22914843474259/50000000000000 : ℝ), (22225470763387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418308461/1000000000 : ℝ)|^2167 ≤ (31944842282747/100000000000000 : ℝ)^1655
        have hw : |(418308461/1000000000 : ℝ)|=(418308461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510717777/10000000000 : ℝ)|^2167 ≤ (22914843474259/50000000000000 : ℝ)^1655
        have hw : |(5510717777/10000000000 : ℝ)|=(5510717777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3170818383/10000000000 : ℝ)|^2167 ≤ (22225470763387/100000000000000 : ℝ)^1655
        have hw : |(3170818383/10000000000 : ℝ)|=(3170818383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1374_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (413/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26643/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (4333/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4333 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4333*1^1024 ≤ 0^1024*1^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4333/1024 : ℝ) ≤ (1035401095108363831/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4333 ≤ (1035401095108363831/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4333*50000000000000000000^1024 ≤ 1035401095108363831^1024*5^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1035401095108363831 50000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1035401095108363831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4333 := by
      have hnat : (1 : ℕ)^1024*1^4333 ≤ 1^4333*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51035401095108363831/50000000000000000000 : ℝ) ≤ (502427804861813/500000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (51035401095108363831/50000000000000000000 : ℝ)^1024 ≤ (502427804861813/500000000000000 : ℝ)^4333 := by
      have hnat : (51035401095108363831 : ℕ)^1024*500000000000000^4333 ≤ 502427804861813^4333*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51035401095108363831 50000000000000000000 502427804861813 500000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502427804861813/500000000000000 : ℝ)) (X := (51035401095108363831/50000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26035401095108363831/25000000000000000000 : ℝ) ≤ (252427804861813/250000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (26035401095108363831/25000000000000000000 : ℝ)^1024 ≤ (252427804861813/250000000000000 : ℝ)^4333 := by
      have hnat : (26035401095108363831 : ℕ)^1024*250000000000000^4333 ≤ 252427804861813^4333*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26035401095108363831 25000000000000000000 252427804861813 250000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252427804861813/250000000000000 : ℝ)) (X := (26035401095108363831/25000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2427804861813/200000000000000 : ℝ)*(0 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2427804861813/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1035401095108363831/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2427804861813/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4333/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2427804861813/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(502427804861813/500000000000000 : ℝ) by norm_num, show 1+(1035401095108363831/50000000000000000000 : ℝ)+(0 : ℝ)=(51035401095108363831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1035401095108363831/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2427804861813/200000000000000 : ℝ)*(2/5 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2427804861813/200000000000000 : ℝ)*(2/5 : ℝ)=(252427804861813/250000000000000 : ℝ) by norm_num, show 1+2*(1035401095108363831/50000000000000000000 : ℝ)=(26035401095108363831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2427804861813/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2427804861813/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2427804861813/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2427804861813/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2427804861813/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2427804861813/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-447594743/2500000000 : ℝ)*X 0 0+(2991605203/5000000000 : ℝ)*X 0 1+(4818486251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1374558161/2500000000 : ℝ)*X 1 0+(-612719511/2500000000 : ℝ)*X 1 1+(240924343/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5498232531/10000000000 : ℝ)*X 2 0+(963697233/2000000000 : ℝ)*X 2 1+(-490175809/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1043498893/2500000000 : ℝ)*X 0 0+(776282743/2500000000 : ℝ)*X 0 1+(5574133651/10000000000 : ℝ)*X 0 2+(1043498893/2500000000 : ℝ)*X 1 0+(776282743/2500000000 : ℝ)*X 1 1+(5574133651/10000000000 : ℝ)*X 1 2+(1043498893/2500000000 : ℝ)*X 2 0+(776282743/2500000000 : ℝ)*X 2 1+(5574133651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-897335261/5000000000 : ℝ)*X 0 0+(4848403409/10000000000 : ℝ)*X 0 1+(74402799/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5180616603/10000000000 : ℝ)*X 1 0+(-32928591/250000000 : ℝ)*X 1 1+(1488055647/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2590307687/5000000000 : ℝ)*X 2 0+(1488056309/2500000000 : ℝ)*X 2 1+(-263428259/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((418308461/1000000000 : ℝ)*X 0 0+(5510717777/10000000000 : ℝ)*X 0 1+(3170818383/10000000000 : ℝ)*X 0 2+(418308461/1000000000 : ℝ)*X 1 0+(5510717777/10000000000 : ℝ)*X 1 1+(3170818383/10000000000 : ℝ)*X 1 2+(418308461/1000000000 : ℝ)*X 2 0+(5510717777/10000000000 : ℝ)*X 2 1+(3170818383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2982220545532750206363/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94578457/50000000000000 : ℝ)*(base1) + (25294683/50000000000000 : ℝ)*(base16) + (639041101/100000000000000 : ℝ)*(base19) + (671984981/100000000000000 : ℝ)*(base23) + (24126391/25000000000000 : ℝ)*(upper3) + (63179965321117/10000000000000 : ℝ)*(major0) + (63179965321117/10000000000000 : ℝ)*(major1) + (63179965321117/10000000000000 : ℝ)*(major2) + (429287246724957/50000000000000 : ℝ)*(sp0) + (85857512630209/10000000000000 : ℝ)*(sp1) + (107321892993447/12500000000000 : ℝ)*(sp2) + (202511191422301/50000000000000 : ℝ)*(sp3) + (1511639557/100000000000000 : ℝ)*(sp4) + (819080913/100000000000000 : ℝ)*(sp7) + (405023391082429/100000000000000 : ℝ)*(f.failure) + (858575815932557/100000000000000 : ℝ)*(f.sum) + (3838948306879/1000000000000000000000000000 : ℝ)*base66 + (1062361078879/2000000000000000000000000000 : ℝ)*base68 + (10637432935121/2000000000000000000000000000 : ℝ)*base69 + (1950798662879/2000000000000000000000000000 : ℝ)*base72 + (678964220121/1000000000000000000000000000 : ℝ)*base73 + (8045829843121/2000000000000000000000000000 : ℝ)*base75 + (6292463545121/2000000000000000000000000000 : ℝ)*base77 + (6699623364879/2000000000000000000000000000 : ℝ)*base80 + (29424855879/1000000000000000000000000000 : ℝ)*base82 + (5861649/2000000000000000000000 : ℝ)*base89 + (5861649/2000000000000000000000 : ℝ)*base91 + (5861649/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10092921202457017839/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (129838527/12500000000000 : ℝ)*(base19) + (1626175559/100000000000000 : ℝ)*(base23) + (316833049/50000000000000 : ℝ)*(base39) + (713643/1000000000000 : ℝ)*(upper2) + (369792453/100000000000000 : ℝ)*(upper5) + (666654755775729/100000000000000 : ℝ)*(major0) + (666654755775729/100000000000000 : ℝ)*(major1) + (666654122109631/100000000000000 : ℝ)*(major2) + (2644131599/100000000000000 : ℝ)*(sp1) + (3391373843/100000000000000 : ℝ)*(sp2) + (452970416602711/50000000000000 : ℝ)*(sp4) + (113242143795701/12500000000000 : ℝ)*(sp5) + (452968224661059/50000000000000 : ℝ)*(sp6) + (427367708249227/100000000000000 : ℝ)*(sp7) + (427367708249227/100000000000000 : ℝ)*(f.failure) + (5662134167947/625000000000 : ℝ)*(f.sum) + (938049150471/250000000000000000000000000 : ℝ)*base65 + (24431848118997/20000000000000000000000000000 : ℝ)*base68 + (56623780716677/20000000000000000000000000000 : ℝ)*base69 + (29781914421003/20000000000000000000000000000 : ℝ)*base71 + (865360028779/250000000000000000000000000 : ℝ)*base74 + (87099187363323/20000000000000000000000000000 : ℝ)*base76 + (147763959636677/20000000000000000000000000000 : ℝ)*base77 + (3681257896677/20000000000000000000000000000 : ℝ)*base79 + (4718107623323/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2943913/2000000000000000000000 : ℝ)*base90 + (2943913/2000000000000000000000 : ℝ)*base92 + (2943913/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1374_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26643/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1374_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1374_s1_0 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1970583993/10000000000 : ℝ)*x 0 + (5628076769/10000000000 : ℝ)*x 1 + (1011635729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1970583993/10000000000 : ℝ)^2167 ≤ (11922488806643/100000000000000 : ℝ)^1655 := by
    have hnat : (1970583993 : ℕ)^2167*100000000000000^1655 ≤ 11922488806643^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970583993 10000000000 11922488806643 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5628076769/10000000000 : ℝ)^2167 ≤ (23555916321237/50000000000000 : ℝ)^1655 := by
    have hnat : (5628076769 : ℕ)^2167*50000000000000^1655 ≤ 23555916321237^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5628076769 10000000000 23555916321237 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011635729/2000000000 : ℝ)^2167 ≤ (40965678538509/100000000000000 : ℝ)^1655 := by
    have hnat : (1011635729 : ℕ)^2167*100000000000000^1655 ≤ 40965678538509^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011635729 2000000000 40965678538509 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1970583993/10000000000 : ℝ), (5628076769/10000000000 : ℝ), (1011635729/2000000000 : ℝ)] ![(11922488806643/100000000000000 : ℝ), (23555916321237/50000000000000 : ℝ), (40965678538509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1970583993/10000000000 : ℝ)|^2167 ≤ (11922488806643/100000000000000 : ℝ)^1655
        have hw : |(-1970583993/10000000000 : ℝ)|=(1970583993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5628076769/10000000000 : ℝ)|^2167 ≤ (23555916321237/50000000000000 : ℝ)^1655
        have hw : |(5628076769/10000000000 : ℝ)|=(5628076769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1011635729/2000000000 : ℝ)|^2167 ≤ (40965678538509/100000000000000 : ℝ)^1655
        have hw : |(1011635729/2000000000 : ℝ)|=(1011635729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s1_1 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2701201433/5000000000 : ℝ)*x 0 + (-1136940257/5000000000 : ℝ)*x 1 + (5058179989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701201433/5000000000 : ℝ)^2167 ≤ (697715885007/1562500000000 : ℝ)^1655 := by
    have hnat : (2701201433 : ℕ)^2167*1562500000000^1655 ≤ 697715885007^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701201433 5000000000 697715885007 1562500000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136940257/5000000000 : ℝ)^2167 ≤ (898780660217/6250000000000 : ℝ)^1655 := by
    have hnat : (1136940257 : ℕ)^2167*6250000000000^1655 ≤ 898780660217^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136940257 5000000000 898780660217 6250000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5058179989/10000000000 : ℝ)^2167 ≤ (819313855817/2000000000000 : ℝ)^1655 := by
    have hnat : (5058179989 : ℕ)^2167*2000000000000^1655 ≤ 819313855817^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5058179989 10000000000 819313855817 2000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701201433/5000000000 : ℝ), (-1136940257/5000000000 : ℝ), (5058179989/10000000000 : ℝ)] ![(697715885007/1562500000000 : ℝ), (898780660217/6250000000000 : ℝ), (819313855817/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701201433/5000000000 : ℝ)|^2167 ≤ (697715885007/1562500000000 : ℝ)^1655
        have hw : |(2701201433/5000000000 : ℝ)|=(2701201433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1136940257/5000000000 : ℝ)|^2167 ≤ (898780660217/6250000000000 : ℝ)^1655
        have hw : |(-1136940257/5000000000 : ℝ)|=(1136940257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5058179989/10000000000 : ℝ)|^2167 ≤ (819313855817/2000000000000 : ℝ)^1655
        have hw : |(5058179989/10000000000 : ℝ)|=(5058179989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s1_2 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (84412553/156250000 : ℝ)*x 0 + (5058178839/10000000000 : ℝ)*x 1 + (-1136940649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84412553/156250000 : ℝ)^2167 ≤ (11163455583287/25000000000000 : ℝ)^1655 := by
    have hnat : (84412553 : ℕ)^2167*25000000000000^1655 ≤ 11163455583287^1655*156250000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84412553 156250000 11163455583287 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5058178839/10000000000 : ℝ)^2167 ≤ (40965680595767/100000000000000 : ℝ)^1655 := by
    have hnat : (5058178839 : ℕ)^2167*100000000000000^1655 ≤ 40965680595767^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5058178839 10000000000 40965680595767 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136940649/5000000000 : ℝ)^2167 ≤ (719024852777/5000000000000 : ℝ)^1655 := by
    have hnat : (1136940649 : ℕ)^2167*5000000000000^1655 ≤ 719024852777^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136940649 5000000000 719024852777 5000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84412553/156250000 : ℝ), (5058178839/10000000000 : ℝ), (-1136940649/5000000000 : ℝ)] ![(11163455583287/25000000000000 : ℝ), (40965680595767/100000000000000 : ℝ), (719024852777/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84412553/156250000 : ℝ)|^2167 ≤ (11163455583287/25000000000000 : ℝ)^1655
        have hw : |(84412553/156250000 : ℝ)|=(84412553/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5058178839/10000000000 : ℝ)|^2167 ≤ (40965680595767/100000000000000 : ℝ)^1655
        have hw : |(5058178839/10000000000 : ℝ)|=(5058178839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1136940649/5000000000 : ℝ)|^2167 ≤ (719024852777/5000000000000 : ℝ)^1655
        have hw : |(-1136940649/5000000000 : ℝ)|=(1136940649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s1_3 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (535822527/1250000000 : ℝ)*x 0 + (3721439927/10000000000 : ℝ)*x 1 + (4929515257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535822527/1250000000 : ℝ)^2167 ≤ (8245913295117/25000000000000 : ℝ)^1655 := by
    have hnat : (535822527 : ℕ)^2167*25000000000000^1655 ≤ 8245913295117^1655*1250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535822527 1250000000 8245913295117 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3721439927/10000000000 : ℝ)^2167 ≤ (27409668643801/100000000000000 : ℝ)^1655 := by
    have hnat : (3721439927 : ℕ)^2167*100000000000000^1655 ≤ 27409668643801^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3721439927 10000000000 27409668643801 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4929515257/10000000000 : ℝ)^2167 ≤ (39606678166401/100000000000000 : ℝ)^1655 := by
    have hnat : (4929515257 : ℕ)^2167*100000000000000^1655 ≤ 39606678166401^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4929515257 10000000000 39606678166401 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535822527/1250000000 : ℝ), (3721439927/10000000000 : ℝ), (4929515257/10000000000 : ℝ)] ![(8245913295117/25000000000000 : ℝ), (27409668643801/100000000000000 : ℝ), (39606678166401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535822527/1250000000 : ℝ)|^2167 ≤ (8245913295117/25000000000000 : ℝ)^1655
        have hw : |(535822527/1250000000 : ℝ)|=(535822527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3721439927/10000000000 : ℝ)|^2167 ≤ (27409668643801/100000000000000 : ℝ)^1655
        have hw : |(3721439927/10000000000 : ℝ)|=(3721439927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4929515257/10000000000 : ℝ)|^2167 ≤ (39606678166401/100000000000000 : ℝ)^1655
        have hw : |(4929515257/10000000000 : ℝ)|=(4929515257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s1_4 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-197106491/1000000000 : ℝ)*x 0 + (5065155513/10000000000 : ℝ)*x 1 + (5620976137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197106491/1000000000 : ℝ)^2167 ≤ (11926298757803/100000000000000 : ℝ)^1655 := by
    have hnat : (197106491 : ℕ)^2167*100000000000000^1655 ≤ 11926298757803^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197106491 1000000000 11926298757803 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5065155513/10000000000 : ℝ)^2167 ≤ (10259919988603/25000000000000 : ℝ)^1655 := by
    have hnat : (5065155513 : ℕ)^2167*25000000000000^1655 ≤ 10259919988603^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5065155513 10000000000 10259919988603 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5620976137/10000000000 : ℝ)^2167 ≤ (376272170101/800000000000 : ℝ)^1655 := by
    have hnat : (5620976137 : ℕ)^2167*800000000000^1655 ≤ 376272170101^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620976137 10000000000 376272170101 800000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197106491/1000000000 : ℝ), (5065155513/10000000000 : ℝ), (5620976137/10000000000 : ℝ)] ![(11926298757803/100000000000000 : ℝ), (10259919988603/25000000000000 : ℝ), (376272170101/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197106491/1000000000 : ℝ)|^2167 ≤ (11926298757803/100000000000000 : ℝ)^1655
        have hw : |(-197106491/1000000000 : ℝ)|=(197106491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5065155513/10000000000 : ℝ)|^2167 ≤ (10259919988603/25000000000000 : ℝ)^1655
        have hw : |(5065155513/10000000000 : ℝ)|=(5065155513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5620976137/10000000000 : ℝ)|^2167 ≤ (376272170101/800000000000 : ℝ)^1655
        have hw : |(5620976137/10000000000 : ℝ)|=(5620976137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s1_5 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5254134229/10000000000 : ℝ)*x 0 + (-855542079/5000000000 : ℝ)*x 1 + (5620976233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254134229/10000000000 : ℝ)^2167 ≤ (43056016804723/100000000000000 : ℝ)^1655 := by
    have hnat : (5254134229 : ℕ)^2167*100000000000000^1655 ≤ 43056016804723^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254134229 10000000000 43056016804723 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (855542079/5000000000 : ℝ)^2167 ≤ (4954980431987/50000000000000 : ℝ)^1655 := by
    have hnat : (855542079 : ℕ)^2167*50000000000000^1655 ≤ 4954980431987^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855542079 5000000000 4954980431987 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5620976233/10000000000 : ℝ)^2167 ≤ (47034022314423/100000000000000 : ℝ)^1655 := by
    have hnat : (5620976233 : ℕ)^2167*100000000000000^1655 ≤ 47034022314423^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620976233 10000000000 47034022314423 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254134229/10000000000 : ℝ), (-855542079/5000000000 : ℝ), (5620976233/10000000000 : ℝ)] ![(43056016804723/100000000000000 : ℝ), (4954980431987/50000000000000 : ℝ), (47034022314423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254134229/10000000000 : ℝ)|^2167 ≤ (43056016804723/100000000000000 : ℝ)^1655
        have hw : |(5254134229/10000000000 : ℝ)|=(5254134229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-855542079/5000000000 : ℝ)|^2167 ≤ (4954980431987/50000000000000 : ℝ)^1655
        have hw : |(-855542079/5000000000 : ℝ)|=(855542079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5620976233/10000000000 : ℝ)|^2167 ≤ (47034022314423/100000000000000 : ℝ)^1655
        have hw : |(5620976233/10000000000 : ℝ)|=(5620976233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s1_6 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1313533531/2500000000 : ℝ)*x 0 + (5620976339/10000000000 : ℝ)*x 1 + (-855542077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313533531/2500000000 : ℝ)^2167 ≤ (43056015678089/100000000000000 : ℝ)^1655 := by
    have hnat : (1313533531 : ℕ)^2167*100000000000000^1655 ≤ 43056015678089^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313533531 2500000000 43056015678089 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5620976339/10000000000 : ℝ)^2167 ≤ (5879252934473/12500000000000 : ℝ)^1655 := by
    have hnat : (5620976339 : ℕ)^2167*12500000000000^1655 ≤ 5879252934473^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620976339 10000000000 5879252934473 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (855542077/5000000000 : ℝ)^2167 ≤ (247749020841/2500000000000 : ℝ)^1655 := by
    have hnat : (855542077 : ℕ)^2167*2500000000000^1655 ≤ 247749020841^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855542077 5000000000 247749020841 2500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313533531/2500000000 : ℝ), (5620976339/10000000000 : ℝ), (-855542077/5000000000 : ℝ)] ![(43056015678089/100000000000000 : ℝ), (5879252934473/12500000000000 : ℝ), (247749020841/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313533531/2500000000 : ℝ)|^2167 ≤ (43056015678089/100000000000000 : ℝ)^1655
        have hw : |(1313533531/2500000000 : ℝ)|=(1313533531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5620976339/10000000000 : ℝ)|^2167 ≤ (5879252934473/12500000000000 : ℝ)^1655
        have hw : |(5620976339/10000000000 : ℝ)|=(5620976339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-855542077/5000000000 : ℝ)|^2167 ≤ (247749020841/2500000000000 : ℝ)^1655
        have hw : |(-855542077/5000000000 : ℝ)|=(855542077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s1_7 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2143800207/5000000000 : ℝ)*x 0 + (196589099/400000000 : ℝ)*x 1 + (116765271/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143800207/5000000000 : ℝ)^2167 ≤ (824848303507/2500000000000 : ℝ)^1655 := by
    have hnat : (2143800207 : ℕ)^2167*2500000000000^1655 ≤ 824848303507^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143800207 5000000000 824848303507 2500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196589099/400000000 : ℝ)^2167 ≤ (7890235915827/20000000000000 : ℝ)^1655 := by
    have hnat : (196589099 : ℕ)^2167*20000000000000^1655 ≤ 7890235915827^1655*400000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196589099 400000000 7890235915827 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116765271/312500000 : ℝ)^2167 ≤ (13777444130121/50000000000000 : ℝ)^1655 := by
    have hnat : (116765271 : ℕ)^2167*50000000000000^1655 ≤ 13777444130121^1655*312500000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116765271 312500000 13777444130121 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143800207/5000000000 : ℝ), (196589099/400000000 : ℝ), (116765271/312500000 : ℝ)] ![(824848303507/2500000000000 : ℝ), (7890235915827/20000000000000 : ℝ), (13777444130121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143800207/5000000000 : ℝ)|^2167 ≤ (824848303507/2500000000000 : ℝ)^1655
        have hw : |(2143800207/5000000000 : ℝ)|=(2143800207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(196589099/400000000 : ℝ)|^2167 ≤ (7890235915827/20000000000000 : ℝ)^1655
        have hw : |(196589099/400000000 : ℝ)|=(196589099/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116765271/312500000 : ℝ)|^2167 ≤ (13777444130121/50000000000000 : ℝ)^1655
        have hw : |(116765271/312500000 : ℝ)|=(116765271/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1374_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26643/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (7181/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19227/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26643/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (413/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26643/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (413/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26643/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (413/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26643/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (413/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26643/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (413/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26643/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (413/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (413/25000 : ℝ) ^ (4333/1024 : ℝ) ≤ (180088908889/6250000000000000000 : ℝ) := by
    have hpowers : (413/25000 : ℝ)^4333 ≤ (180088908889/6250000000000000000 : ℝ)^1024 := by
      have hnat : (413 : ℕ)^4333*6250000000000000000^1024 ≤ 180088908889^1024*25000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413 25000 180088908889 6250000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (413/25000 : ℝ)) (X := (180088908889/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26643/100000 : ℝ) ^ (4333/1024 : ℝ) ≤ (185505337623451849/50000000000000000000 : ℝ) := by
    have hpowers : (26643/100000 : ℝ)^4333 ≤ (185505337623451849/50000000000000000000 : ℝ)^1024 := by
      have hnat : (26643 : ℕ)^4333*50000000000000000000^1024 ≤ 185505337623451849^1024*100000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26643 100000 185505337623451849 50000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26643/100000 : ℝ)) (X := (185505337623451849/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000180088908889/3125000000000000000 : ℝ) ≤ (1250000017023867/1250000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (3125000180088908889/3125000000000000000 : ℝ)^1024 ≤ (1250000017023867/1250000000000000 : ℝ)^4333 := by
      have hnat : (3125000180088908889 : ℕ)^1024*1250000000000000^4333 ≤ 1250000017023867^4333*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000180088908889 3125000000000000000 1250000017023867 1250000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000017023867/1250000000000000 : ℝ)) (X := (3125000180088908889/3125000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50185506778334722961/50000000000000000000 : ℝ) ≤ (10008755615872023/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (50185506778334722961/50000000000000000000 : ℝ)^1024 ≤ (10008755615872023/10000000000000000 : ℝ)^4333 := by
      have hnat : (50185506778334722961 : ℕ)^1024*10000000000000000^4333 ≤ 10008755615872023^4333*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50185506778334722961 50000000000000000000 10008755615872023 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008755615872023/10000000000000000 : ℝ)) (X := (50185506778334722961/50000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25185505337623451849/25000000000000000000 : ℝ) ≤ (1001751109555311/1000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (25185505337623451849/25000000000000000000 : ℝ)^1024 ≤ (1001751109555311/1000000000000000 : ℝ)^4333 := by
      have hnat : (25185505337623451849 : ℕ)^1024*1000000000000000^4333 ≤ 1001751109555311^4333*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25185505337623451849 25000000000000000000 1001751109555311 1000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001751109555311/1000000000000000 : ℝ)) (X := (25185505337623451849/25000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(180088908889/6250000000000000000 : ℝ) ≤ ((15617567206167585633/15619375000000000000 : ℝ)+2*(8755479681087/2499100000000000 : ℝ)*(413/25000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (15617567206167585633/15619375000000000000 : ℝ)+2*(8755479681087/2499100000000000 : ℝ)*(413/25000 : ℝ)=(1250000017023867/1250000000000000 : ℝ) by norm_num, show 1+2*(180088908889/6250000000000000000 : ℝ)=(3125000180088908889/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(185505337623451849/50000000000000000000 : ℝ)+(180088908889/6250000000000000000 : ℝ) ≤ ((15617567206167585633/15619375000000000000 : ℝ)+(8755479681087/2499100000000000 : ℝ)*((26643/100000 : ℝ)+(413/25000 : ℝ)))^(4333/1024 : ℝ) := by
    rw [show (15617567206167585633/15619375000000000000 : ℝ)+(8755479681087/2499100000000000 : ℝ)*((26643/100000 : ℝ)+(413/25000 : ℝ))=(10008755615872023/10000000000000000 : ℝ) by norm_num, show 1+(185505337623451849/50000000000000000000 : ℝ)+(180088908889/6250000000000000000 : ℝ)=(50185506778334722961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(185505337623451849/50000000000000000000 : ℝ) ≤ ((15617567206167585633/15619375000000000000 : ℝ)+2*(8755479681087/2499100000000000 : ℝ)*(26643/100000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (15617567206167585633/15619375000000000000 : ℝ)+2*(8755479681087/2499100000000000 : ℝ)*(26643/100000 : ℝ)=(1001751109555311/1000000000000000 : ℝ) by norm_num, show 1+2*(185505337623451849/50000000000000000000 : ℝ)=(25185505337623451849/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15617567206167585633/15619375000000000000 : ℝ)*(X 1 0+X 2 0)+(8755479681087/2499100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (413/25000 : ℝ)) (hi := (26643/100000 : ℝ)) (c := (15617567206167585633/15619375000000000000 : ℝ)) (alpha := (8755479681087/2499100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15617567206167585633/15619375000000000000 : ℝ)*(X 0 1+X 2 1)+(8755479681087/2499100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (413/25000 : ℝ)) (hi := (26643/100000 : ℝ)) (c := (15617567206167585633/15619375000000000000 : ℝ)) (alpha := (8755479681087/2499100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15617567206167585633/15619375000000000000 : ℝ)*(X 0 2+X 1 2)+(8755479681087/2499100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (413/25000 : ℝ)) (hi := (26643/100000 : ℝ)) (c := (15617567206167585633/15619375000000000000 : ℝ)) (alpha := (8755479681087/2499100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1970583993/10000000000 : ℝ)*X 0 0+(5628076769/10000000000 : ℝ)*X 0 1+(1011635729/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2701201433/5000000000 : ℝ)*X 1 0+(-1136940257/5000000000 : ℝ)*X 1 1+(5058179989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((84412553/156250000 : ℝ)*X 2 0+(5058178839/10000000000 : ℝ)*X 2 1+(-1136940649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((535822527/1250000000 : ℝ)*X 0 0+(3721439927/10000000000 : ℝ)*X 0 1+(4929515257/10000000000 : ℝ)*X 0 2+(535822527/1250000000 : ℝ)*X 1 0+(3721439927/10000000000 : ℝ)*X 1 1+(4929515257/10000000000 : ℝ)*X 1 2+(535822527/1250000000 : ℝ)*X 2 0+(3721439927/10000000000 : ℝ)*X 2 1+(4929515257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-197106491/1000000000 : ℝ)*X 0 0+(5065155513/10000000000 : ℝ)*X 0 1+(5620976137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254134229/10000000000 : ℝ)*X 1 0+(-855542079/5000000000 : ℝ)*X 1 1+(5620976233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313533531/2500000000 : ℝ)*X 2 0+(5620976339/10000000000 : ℝ)*X 2 1+(-855542077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2143800207/5000000000 : ℝ)*X 0 0+(196589099/400000000 : ℝ)*X 0 1+(116765271/312500000 : ℝ)*X 0 2+(2143800207/5000000000 : ℝ)*X 1 0+(196589099/400000000 : ℝ)*X 1 1+(116765271/312500000 : ℝ)*X 1 2+(2143800207/5000000000 : ℝ)*X 2 0+(196589099/400000000 : ℝ)*X 2 1+(116765271/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (418227919869240232728923409/97621093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (531736803/100000000000000 : ℝ)*(base19) + (364860523/50000000000000 : ℝ)*(base23) + (440791/1250000000000 : ℝ)*(upper2) + (67470943/100000000000000 : ℝ)*(upper3) + (322810330678881/25000000000000 : ℝ)*(major0) + (322810330678881/25000000000000 : ℝ)*(major1) + (322810330678881/25000000000000 : ℝ)*(major2) + (1754707785514927/100000000000000 : ℝ)*(sp0) + (877357457197273/50000000000000 : ℝ)*(sp1) + (109669582931069/6250000000000 : ℝ)*(sp2) + (827764755389671/100000000000000 : ℝ)*(sp3) + (3830308211/50000000000000 : ℝ)*(sp4) + (3473783/250000000000 : ℝ)*(sp6) + (2301103477/100000000000000 : ℝ)*(sp7) + (206941764123287/25000000000000 : ℝ)*(f.failure) + (1754715446131349/100000000000000 : ℝ)*(f.sum) + (557168473999323/124955000000000000000000000000 : ℝ)*base65 + (866506256296184637/97621093750000000000000000000000 : ℝ)*base67 + (60771366184910423/390484375000000000000000000000000 : ℝ)*base69 + (1720689779571941673/390484375000000000000000000000000 : ℝ)*base71 + (36270968219031/15619375000000000000000000000 : ℝ)*base73 + (311418437830506381/48810546875000000000000000000000 : ℝ)*base75 + (1959726846799879173/390484375000000000000000000000000 : ℝ)*base77 + (2416289118159160423/390484375000000000000000000000000 : ℝ)*base79 + (29689720466457/124955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5859053/500000000000000000000 : ℝ)*base90 + (5859053/500000000000000000000 : ℝ)*base92 + (5859053/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1599603614003715126643068093/156193750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10440173/10000000000000 : ℝ)*(base1) + (2055851179/100000000000000 : ℝ)*(base19) + (1011049249/50000000000000 : ℝ)*(base23) + (121334343/50000000000000 : ℝ)*(upper3) + (57414409/25000000000000 : ℝ)*(upper5) + (264786610921043/20000000000000 : ℝ)*(major0) + (264786610921043/20000000000000 : ℝ)*(major1) + (264786610921043/20000000000000 : ℝ)*(major2) + (10948566747/100000000000000 : ℝ)*(sp1) + (2756635967/25000000000000 : ℝ)*(sp2) + (899570677754857/50000000000000 : ℝ)*(sp4) + (899564123345029/50000000000000 : ℝ)*(sp5) + (899564101232809/50000000000000 : ℝ)*(sp6) + (424362206164523/50000000000000 : ℝ)*(sp7) + (848724516730777/100000000000000 : ℝ)*(f.failure) + (112446328194249/6250000000000 : ℝ)*(f.sum) + (73536883417477/24991000000000000000000000000 : ℝ)*base65 + (559009201154906469/312387500000000000000000000000000 : ℝ)*base67 + (61820219140318531/312387500000000000000000000000000 : ℝ)*base70 + (2179792666478206469/312387500000000000000000000000000 : ℝ)*base71 + (3540080741293/24991000000000000000000000000 : ℝ)*base73 + (258088797451068969/312387500000000000000000000000000 : ℝ)*base75 + (3041344767142593531/312387500000000000000000000000000 : ℝ)*base78 + (599723141358006469/312387500000000000000000000000000 : ℝ)*base79 + (3041559521417/999640000000000000000000000 : ℝ)*base81 + (9116637/2000000000000000000000 : ℝ)*base89 + (9116637/2000000000000000000000 : ℝ)*base91 + (9116637/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1374_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26643/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7181/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19227/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1374_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1374_s2_0 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1004014449/5000000000 : ℝ)*x 0 + (547131191/1000000000 : ℝ)*x 1 + (1297728643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004014449/5000000000 : ℝ)^2167 ≤ (12219994124249/100000000000000 : ℝ)^1655 := by
    have hnat : (1004014449 : ℕ)^2167*100000000000000^1655 ≤ 12219994124249^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004014449 5000000000 12219994124249 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547131191/1000000000 : ℝ)^2167 ≤ (45401060379527/100000000000000 : ℝ)^1655 := by
    have hnat : (547131191 : ℕ)^2167*100000000000000^1655 ≤ 45401060379527^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547131191 1000000000 45401060379527 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297728643/2500000000 : ℝ)^2167 ≤ (21189472742159/50000000000000 : ℝ)^1655 := by
    have hnat : (1297728643 : ℕ)^2167*50000000000000^1655 ≤ 21189472742159^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297728643 2500000000 21189472742159 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1004014449/5000000000 : ℝ), (547131191/1000000000 : ℝ), (1297728643/2500000000 : ℝ)] ![(12219994124249/100000000000000 : ℝ), (45401060379527/100000000000000 : ℝ), (21189472742159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1004014449/5000000000 : ℝ)|^2167 ≤ (12219994124249/100000000000000 : ℝ)^1655
        have hw : |(-1004014449/5000000000 : ℝ)|=(1004014449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547131191/1000000000 : ℝ)|^2167 ≤ (45401060379527/100000000000000 : ℝ)^1655
        have hw : |(547131191/1000000000 : ℝ)|=(547131191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297728643/2500000000 : ℝ)|^2167 ≤ (21189472742159/50000000000000 : ℝ)^1655
        have hw : |(1297728643/2500000000 : ℝ)|=(1297728643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s2_1 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (670468199/1250000000 : ℝ)*x 0 + (-269083487/1250000000 : ℝ)*x 1 + (519091471/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670468199/1250000000 : ℝ)^2167 ≤ (5529488421991/12500000000000 : ℝ)^1655 := by
    have hnat : (670468199 : ℕ)^2167*12500000000000^1655 ≤ 5529488421991^1655*1250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670468199 1250000000 5529488421991 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269083487/1250000000 : ℝ)^2167 ≤ (2677029129849/20000000000000 : ℝ)^1655 := by
    have hnat : (269083487 : ℕ)^2167*20000000000000^1655 ≤ 2677029129849^1655*1250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269083487 1250000000 2677029129849 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519091471/1000000000 : ℝ)^2167 ≤ (21189473479751/50000000000000 : ℝ)^1655 := by
    have hnat : (519091471 : ℕ)^2167*50000000000000^1655 ≤ 21189473479751^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519091471 1000000000 21189473479751 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670468199/1250000000 : ℝ), (-269083487/1250000000 : ℝ), (519091471/1000000000 : ℝ)] ![(5529488421991/12500000000000 : ℝ), (2677029129849/20000000000000 : ℝ), (21189473479751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670468199/1250000000 : ℝ)|^2167 ≤ (5529488421991/12500000000000 : ℝ)^1655
        have hw : |(670468199/1250000000 : ℝ)|=(670468199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-269083487/1250000000 : ℝ)|^2167 ≤ (2677029129849/20000000000000 : ℝ)^1655
        have hw : |(-269083487/1250000000 : ℝ)|=(269083487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519091471/1000000000 : ℝ)|^2167 ≤ (21189473479751/50000000000000 : ℝ)^1655
        have hw : |(519091471/1000000000 : ℝ)|=(519091471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s2_2 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2681872777/5000000000 : ℝ)*x 0 + (1038182947/2000000000 : ℝ)*x 1 + (-1076333957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681872777/5000000000 : ℝ)^2167 ≤ (44235906965581/100000000000000 : ℝ)^1655 := by
    have hnat : (2681872777 : ℕ)^2167*100000000000000^1655 ≤ 44235906965581^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681872777 5000000000 44235906965581 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038182947/2000000000 : ℝ)^2167 ≤ (8475789445349/20000000000000 : ℝ)^1655 := by
    have hnat : (1038182947 : ℕ)^2167*20000000000000^1655 ≤ 8475789445349^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038182947 2000000000 8475789445349 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076333957/5000000000 : ℝ)^2167 ≤ (13385145795793/100000000000000 : ℝ)^1655 := by
    have hnat : (1076333957 : ℕ)^2167*100000000000000^1655 ≤ 13385145795793^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076333957 5000000000 13385145795793 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681872777/5000000000 : ℝ), (1038182947/2000000000 : ℝ), (-1076333957/5000000000 : ℝ)] ![(44235906965581/100000000000000 : ℝ), (8475789445349/20000000000000 : ℝ), (13385145795793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681872777/5000000000 : ℝ)|^2167 ≤ (44235906965581/100000000000000 : ℝ)^1655
        have hw : |(2681872777/5000000000 : ℝ)|=(2681872777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038182947/2000000000 : ℝ)|^2167 ≤ (8475789445349/20000000000000 : ℝ)^1655
        have hw : |(1038182947/2000000000 : ℝ)|=(1038182947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076333957/5000000000 : ℝ)|^2167 ≤ (13385145795793/100000000000000 : ℝ)^1655
        have hw : |(-1076333957/5000000000 : ℝ)|=(1076333957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s2_3 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4312859809/10000000000 : ℝ)*x 0 + (805015449/2000000000 : ℝ)*x 1 + (4619468177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312859809/10000000000 : ℝ)^2167 ≤ (33248673039681/100000000000000 : ℝ)^1655 := by
    have hnat : (4312859809 : ℕ)^2167*100000000000000^1655 ≤ 33248673039681^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312859809 10000000000 33248673039681 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805015449/2000000000 : ℝ)^2167 ≤ (1898388053009/6250000000000 : ℝ)^1655 := by
    have hnat : (805015449 : ℕ)^2167*6250000000000^1655 ≤ 1898388053009^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805015449 2000000000 1898388053009 6250000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4619468177/10000000000 : ℝ)^2167 ≤ (4547139761857/12500000000000 : ℝ)^1655 := by
    have hnat : (4619468177 : ℕ)^2167*12500000000000^1655 ≤ 4547139761857^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619468177 10000000000 4547139761857 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312859809/10000000000 : ℝ), (805015449/2000000000 : ℝ), (4619468177/10000000000 : ℝ)] ![(33248673039681/100000000000000 : ℝ), (1898388053009/6250000000000 : ℝ), (4547139761857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312859809/10000000000 : ℝ)|^2167 ≤ (33248673039681/100000000000000 : ℝ)^1655
        have hw : |(4312859809/10000000000 : ℝ)|=(4312859809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805015449/2000000000 : ℝ)|^2167 ≤ (1898388053009/6250000000000 : ℝ)^1655
        have hw : |(805015449/2000000000 : ℝ)|=(805015449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4619468177/10000000000 : ℝ)|^2167 ≤ (4547139761857/12500000000000 : ℝ)^1655
        have hw : |(4619468177/10000000000 : ℝ)|=(4619468177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s2_4 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-502021511/2500000000 : ℝ)*x 0 + (207704537/400000000 : ℝ)*x 1 + (1093919681/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502021511/2500000000 : ℝ)^2167 ≤ (611022473941/5000000000000 : ℝ)^1655 := by
    have hnat : (502021511 : ℕ)^2167*5000000000000^1655 ≤ 611022473941^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502021511 2500000000 611022473941 5000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207704537/400000000 : ℝ)^2167 ≤ (10599276675483/25000000000000 : ℝ)^1655 := by
    have hnat : (207704537 : ℕ)^2167*25000000000000^1655 ≤ 10599276675483^1655*400000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207704537 400000000 10599276675483 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093919681/2000000000 : ℝ)^2167 ≤ (22691221902551/50000000000000 : ℝ)^1655 := by
    have hnat : (1093919681 : ℕ)^2167*50000000000000^1655 ≤ 22691221902551^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093919681 2000000000 22691221902551 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502021511/2500000000 : ℝ), (207704537/400000000 : ℝ), (1093919681/2000000000 : ℝ)] ![(611022473941/5000000000000 : ℝ), (10599276675483/25000000000000 : ℝ), (22691221902551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502021511/2500000000 : ℝ)|^2167 ≤ (611022473941/5000000000000 : ℝ)^1655
        have hw : |(-502021511/2500000000 : ℝ)|=(502021511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207704537/400000000 : ℝ)|^2167 ≤ (10599276675483/25000000000000 : ℝ)^1655
        have hw : |(207704537/400000000 : ℝ)|=(207704537/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093919681/2000000000 : ℝ)|^2167 ≤ (22691221902551/50000000000000 : ℝ)^1655
        have hw : |(1093919681/2000000000 : ℝ)|=(1093919681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s2_5 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5291227579/10000000000 : ℝ)*x 0 + (-468496187/2500000000 : ℝ)*x 1 + (2734799057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291227579/10000000000 : ℝ)^2167 ≤ (43454456771807/100000000000000 : ℝ)^1655 := by
    have hnat : (5291227579 : ℕ)^2167*100000000000000^1655 ≤ 43454456771807^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291227579 10000000000 43454456771807 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468496187/2500000000 : ℝ)^2167 ≤ (5581551284121/50000000000000 : ℝ)^1655 := by
    have hnat : (468496187 : ℕ)^2167*50000000000000^1655 ≤ 5581551284121^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468496187 2500000000 5581551284121 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734799057/5000000000 : ℝ)^2167 ≤ (11345610160913/25000000000000 : ℝ)^1655 := by
    have hnat : (2734799057 : ℕ)^2167*25000000000000^1655 ≤ 11345610160913^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734799057 5000000000 11345610160913 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291227579/10000000000 : ℝ), (-468496187/2500000000 : ℝ), (2734799057/5000000000 : ℝ)] ![(43454456771807/100000000000000 : ℝ), (5581551284121/50000000000000 : ℝ), (11345610160913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291227579/10000000000 : ℝ)|^2167 ≤ (43454456771807/100000000000000 : ℝ)^1655
        have hw : |(5291227579/10000000000 : ℝ)|=(5291227579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-468496187/2500000000 : ℝ)|^2167 ≤ (5581551284121/50000000000000 : ℝ)^1655
        have hw : |(-468496187/2500000000 : ℝ)|=(468496187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734799057/5000000000 : ℝ)|^2167 ≤ (11345610160913/25000000000000 : ℝ)^1655
        have hw : |(2734799057/5000000000 : ℝ)|=(2734799057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s2_6 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5291229059/10000000000 : ℝ)*x 0 + (5469598251/10000000000 : ℝ)*x 1 + (-1873982517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291229059/10000000000 : ℝ)^2167 ≤ (43454472686583/100000000000000 : ℝ)^1655 := by
    have hnat : (5291229059 : ℕ)^2167*100000000000000^1655 ≤ 43454472686583^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291229059 10000000000 43454472686583 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469598251/10000000000 : ℝ)^2167 ≤ (45382442132033/100000000000000 : ℝ)^1655 := by
    have hnat : (5469598251 : ℕ)^2167*100000000000000^1655 ≤ 45382442132033^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469598251 10000000000 45382442132033 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873982517/10000000000 : ℝ)^2167 ≤ (11163085167039/100000000000000 : ℝ)^1655 := by
    have hnat : (1873982517 : ℕ)^2167*100000000000000^1655 ≤ 11163085167039^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873982517 10000000000 11163085167039 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291229059/10000000000 : ℝ), (5469598251/10000000000 : ℝ), (-1873982517/10000000000 : ℝ)] ![(43454472686583/100000000000000 : ℝ), (45382442132033/100000000000000 : ℝ), (11163085167039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291229059/10000000000 : ℝ)|^2167 ≤ (43454472686583/100000000000000 : ℝ)^1655
        have hw : |(5291229059/10000000000 : ℝ)|=(5291229059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469598251/10000000000 : ℝ)|^2167 ≤ (45382442132033/100000000000000 : ℝ)^1655
        have hw : |(5469598251/10000000000 : ℝ)|=(5469598251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873982517/10000000000 : ℝ)|^2167 ≤ (11163085167039/100000000000000 : ℝ)^1655
        have hw : |(-1873982517/10000000000 : ℝ)|=(1873982517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s2_7 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (269561419/625000000 : ℝ)*x 0 + (2307933847/5000000000 : ℝ)*x 1 + (4028707953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269561419/625000000 : ℝ)^2167 ≤ (16624956783049/50000000000000 : ℝ)^1655 := by
    have hnat : (269561419 : ℕ)^2167*50000000000000^1655 ≤ 16624956783049^1655*625000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269561419 625000000 16624956783049 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2307933847/5000000000 : ℝ)^2167 ≤ (36339998295827/100000000000000 : ℝ)^1655 := by
    have hnat : (2307933847 : ℕ)^2167*100000000000000^1655 ≤ 36339998295827^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307933847 5000000000 36339998295827 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028707953/10000000000 : ℝ)^2167 ≤ (152050440579/500000000000 : ℝ)^1655 := by
    have hnat : (4028707953 : ℕ)^2167*500000000000^1655 ≤ 152050440579^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028707953 10000000000 152050440579 500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269561419/625000000 : ℝ), (2307933847/5000000000 : ℝ), (4028707953/10000000000 : ℝ)] ![(16624956783049/50000000000000 : ℝ), (36339998295827/100000000000000 : ℝ), (152050440579/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269561419/625000000 : ℝ)|^2167 ≤ (16624956783049/50000000000000 : ℝ)^1655
        have hw : |(269561419/625000000 : ℝ)|=(269561419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2307933847/5000000000 : ℝ)|^2167 ≤ (36339998295827/100000000000000 : ℝ)^1655
        have hw : |(2307933847/5000000000 : ℝ)|=(2307933847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028707953/10000000000 : ℝ)|^2167 ≤ (152050440579/500000000000 : ℝ)^1655
        have hw : |(4028707953/10000000000 : ℝ)|=(4028707953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1374_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5027/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15983/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19227/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19227/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7181/100000 : ℝ) ^ (4333/1024 : ℝ) ≤ (1445469957714771/100000000000000000000 : ℝ) := by
    have hpowers : (7181/100000 : ℝ)^4333 ≤ (1445469957714771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7181 : ℕ)^4333*100000000000000000000^1024 ≤ 1445469957714771^1024*100000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7181 100000 1445469957714771 100000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7181/100000 : ℝ)) (X := (1445469957714771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19227/100000 : ℝ) ^ (4333/1024 : ℝ) ≤ (5831641286463049/6250000000000000000 : ℝ) := by
    have hpowers : (19227/100000 : ℝ)^4333 ≤ (5831641286463049/6250000000000000000 : ℝ)^1024 := by
      have hnat : (19227 : ℕ)^4333*6250000000000000000^1024 ≤ 5831641286463049^1024*100000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19227 100000 5831641286463049 6250000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19227/100000 : ℝ)) (X := (5831641286463049/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001445469957714771/50000000000000000000 : ℝ) ≤ (5000034159817631/5000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (50001445469957714771/50000000000000000000 : ℝ)^1024 ≤ (5000034159817631/5000000000000000 : ℝ)^4333 := by
      have hnat : (50001445469957714771 : ℕ)^1024*5000000000000000^4333 ≤ 5000034159817631^4333*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001445469957714771 50000000000000000000 5000034159817631 5000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000034159817631/5000000000000000 : ℝ)) (X := (50001445469957714771/50000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20018950346108224711/20000000000000000000 : ℝ) ≤ (5001119209415649/5000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (20018950346108224711/20000000000000000000 : ℝ)^1024 ≤ (5001119209415649/5000000000000000 : ℝ)^4333 := by
      have hnat : (20018950346108224711 : ℕ)^1024*5000000000000000^4333 ≤ 5001119209415649^4333*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20018950346108224711 20000000000000000000 5001119209415649 5000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001119209415649/5000000000000000 : ℝ)) (X := (20018950346108224711/20000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3130831641286463049/3125000000000000000 : ℝ) ≤ (5002204259013667/5000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (3130831641286463049/3125000000000000000 : ℝ)^1024 ≤ (5002204259013667/5000000000000000 : ℝ)^4333 := by
      have hnat : (3130831641286463049 : ℕ)^1024*5000000000000000^4333 ≤ 5002204259013667^4333*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3130831641286463049 3125000000000000000 5002204259013667 5000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002204259013667/5000000000000000 : ℝ)) (X := (3130831641286463049/3125000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1445469957714771/100000000000000000000 : ℝ) ≤ ((6021482800683644851/6023000000000000000 : ℝ)+2*(542524799009/301150000000000 : ℝ)*(7181/100000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (6021482800683644851/6023000000000000000 : ℝ)+2*(542524799009/301150000000000 : ℝ)*(7181/100000 : ℝ)=(5000034159817631/5000000000000000 : ℝ) by norm_num, show 1+2*(1445469957714771/100000000000000000000 : ℝ)=(50001445469957714771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5831641286463049/6250000000000000000 : ℝ)+(1445469957714771/100000000000000000000 : ℝ) ≤ ((6021482800683644851/6023000000000000000 : ℝ)+(542524799009/301150000000000 : ℝ)*((19227/100000 : ℝ)+(7181/100000 : ℝ)))^(4333/1024 : ℝ) := by
    rw [show (6021482800683644851/6023000000000000000 : ℝ)+(542524799009/301150000000000 : ℝ)*((19227/100000 : ℝ)+(7181/100000 : ℝ))=(5001119209415649/5000000000000000 : ℝ) by norm_num, show 1+(5831641286463049/6250000000000000000 : ℝ)+(1445469957714771/100000000000000000000 : ℝ)=(20018950346108224711/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5831641286463049/6250000000000000000 : ℝ) ≤ ((6021482800683644851/6023000000000000000 : ℝ)+2*(542524799009/301150000000000 : ℝ)*(19227/100000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (6021482800683644851/6023000000000000000 : ℝ)+2*(542524799009/301150000000000 : ℝ)*(19227/100000 : ℝ)=(5002204259013667/5000000000000000 : ℝ) by norm_num, show 1+2*(5831641286463049/6250000000000000000 : ℝ)=(3130831641286463049/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6021482800683644851/6023000000000000000 : ℝ)*(X 1 0+X 2 0)+(542524799009/301150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (7181/100000 : ℝ)) (hi := (19227/100000 : ℝ)) (c := (6021482800683644851/6023000000000000000 : ℝ)) (alpha := (542524799009/301150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6021482800683644851/6023000000000000000 : ℝ)*(X 0 1+X 2 1)+(542524799009/301150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (7181/100000 : ℝ)) (hi := (19227/100000 : ℝ)) (c := (6021482800683644851/6023000000000000000 : ℝ)) (alpha := (542524799009/301150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6021482800683644851/6023000000000000000 : ℝ)*(X 0 2+X 1 2)+(542524799009/301150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (7181/100000 : ℝ)) (hi := (19227/100000 : ℝ)) (c := (6021482800683644851/6023000000000000000 : ℝ)) (alpha := (542524799009/301150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1004014449/5000000000 : ℝ)*X 0 0+(547131191/1000000000 : ℝ)*X 0 1+(1297728643/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((670468199/1250000000 : ℝ)*X 1 0+(-269083487/1250000000 : ℝ)*X 1 1+(519091471/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681872777/5000000000 : ℝ)*X 2 0+(1038182947/2000000000 : ℝ)*X 2 1+(-1076333957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312859809/10000000000 : ℝ)*X 0 0+(805015449/2000000000 : ℝ)*X 0 1+(4619468177/10000000000 : ℝ)*X 0 2+(4312859809/10000000000 : ℝ)*X 1 0+(805015449/2000000000 : ℝ)*X 1 1+(4619468177/10000000000 : ℝ)*X 1 2+(4312859809/10000000000 : ℝ)*X 2 0+(805015449/2000000000 : ℝ)*X 2 1+(4619468177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-502021511/2500000000 : ℝ)*X 0 0+(207704537/400000000 : ℝ)*X 0 1+(1093919681/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291227579/10000000000 : ℝ)*X 1 0+(-468496187/2500000000 : ℝ)*X 1 1+(2734799057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5291229059/10000000000 : ℝ)*X 2 0+(5469598251/10000000000 : ℝ)*X 2 1+(-1873982517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((269561419/625000000 : ℝ)*X 0 0+(2307933847/5000000000 : ℝ)*X 0 1+(4028707953/10000000000 : ℝ)*X 0 2+(269561419/625000000 : ℝ)*X 1 0+(2307933847/5000000000 : ℝ)*X 1 1+(4028707953/10000000000 : ℝ)*X 1 2+(269561419/625000000 : ℝ)*X 2 0+(2307933847/5000000000 : ℝ)*X 2 1+(4028707953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1050852957722339126290875447/301150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (497130659/100000000000000 : ℝ)*(base19) + (439560201/100000000000000 : ℝ)*(base23) + (693083/4000000000000 : ℝ)*(lower2) + (3464033/4000000000000 : ℝ)*(upper3) + (41612517/100000000000000 : ℝ)*(upper5) + (328048977406751/12500000000000 : ℝ)*(major0) + (328048977406751/12500000000000 : ℝ)*(major1) + (2624391819254009/100000000000000 : ℝ)*(major2) + (891593937656043/25000000000000 : ℝ)*(sp0) + (89159562267849/2500000000000 : ℝ)*(sp1) + (1783191274142209/50000000000000 : ℝ)*(sp2) + (841198623839219/50000000000000 : ℝ)*(sp3) + (7237220447/100000000000000 : ℝ)*(sp4) + (3286669387/100000000000000 : ℝ)*(sp7) + (841200267173913/50000000000000 : ℝ)*(f.failure) + (1783191493922309/50000000000000 : ℝ)*(f.sum) + (144701000241437/30115000000000000000000000000 : ℝ)*base66 + (461733456588620899/75287500000000000000000000000000 : ℝ)*base68 + (5984586521236597659/602300000000000000000000000000000 : ℝ)*base69 + (133110918127366601/75287500000000000000000000000000 : ℝ)*base71 + (40927181538567/30115000000000000000000000000 : ℝ)*base74 + (1592897893220297659/602300000000000000000000000000000 : ℝ)*base75 + (131157870330105899/75287500000000000000000000000000 : ℝ)*base78 + (417383460259955899/75287500000000000000000000000000 : ℝ)*base80 + (168978745403369/30115000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16252253/1000000000000000000000 : ℝ)*base89 + (16252253/1000000000000000000000 : ℝ)*base91 + (6252253/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (167100985589460141305048013/37643750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (465210091/50000000000000 : ℝ)*(base19) + (1578988859/50000000000000 : ℝ)*(base23) + (72938267/25000000000000 : ℝ)*(upper3) + (64531323/20000000000000 : ℝ)*(lower4) + (26774167/100000000000000 : ℝ)*(upper5) + (664177423532071/25000000000000 : ℝ)*(major0) + (664177423532071/25000000000000 : ℝ)*(major1) + (664177423532071/25000000000000 : ℝ)*(major2) + (443243301/50000000000000 : ℝ)*(sp1) + (1131119647/2500000000000 : ℝ)*(sp2) + (1805150455804949/50000000000000 : ℝ)*(sp4) + (1805149547351557/50000000000000 : ℝ)*(sp5) + (36102525088463/1000000000000 : ℝ)*(sp6) + (340623665735933/20000000000000 : ℝ)*(sp7) + (340623665735933/20000000000000 : ℝ)*(f.failure) + (1805150455804949/50000000000000 : ℝ)*(f.sum) + (4686982992287/1882187500000000000000000000 : ℝ)*base65 + (91873447108296421/150575000000000000000000000000000 : ℝ)*base67 + (296032639174828579/150575000000000000000000000000000 : ℝ)*base70 + (741970306365953579/150575000000000000000000000000000 : ℝ)*base72 + (49403979429411/15057500000000000000000000000 : ℝ)*base73 + (22141190167278579/150575000000000000000000000000000 : ℝ)*base76 + (621219671018203579/150575000000000000000000000000000 : ℝ)*base78 + (842005117800453579/150575000000000000000000000000000 : ℝ)*base80 + (11658868693737/30115000000000000000000000000 : ℝ)*base81 + (62127/400000000000000000000 : ℝ)*base90 + (62127/400000000000000000000 : ℝ)*base92 + (62127/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1374_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5027/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15983/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1374_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1374_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5027/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15983/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1374_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1374_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1374_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5027/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15983/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1374_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1355_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:43.683598+00:00
-- url     : https://prove2.me/submissions/5a15a7e9-aba4-4750-9e70-257eba64d8d8

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
theorem support_rectangle_w1355_s3_0 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031162769/10000000000 : ℝ)*x 0 + (2712765459/5000000000 : ℝ)*x 1 + (5232575749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031162769/10000000000 : ℝ)^4315 ≤ (1546174074419/12500000000000 : ℝ)^3291 := by
    have hnat : (2031162769 : ℕ)^4315*12500000000000^3291 ≤ 1546174074419^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031162769 10000000000 1546174074419 12500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712765459/5000000000 : ℝ)^4315 ≤ (44855274092037/100000000000000 : ℝ)^3291 := by
    have hnat : (2712765459 : ℕ)^4315*100000000000000^3291 ≤ 44855274092037^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712765459 5000000000 44855274092037 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232575749/10000000000 : ℝ)^4315 ≤ (42775333294647/100000000000000 : ℝ)^3291 := by
    have hnat : (5232575749 : ℕ)^4315*100000000000000^3291 ≤ 42775333294647^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232575749 10000000000 42775333294647 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031162769/10000000000 : ℝ), (2712765459/5000000000 : ℝ), (5232575749/10000000000 : ℝ)] ![(1546174074419/12500000000000 : ℝ), (44855274092037/100000000000000 : ℝ), (42775333294647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031162769/10000000000 : ℝ)|^4315 ≤ (1546174074419/12500000000000 : ℝ)^3291
        have hw : |(-2031162769/10000000000 : ℝ)|=(2031162769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712765459/5000000000 : ℝ)|^4315 ≤ (44855274092037/100000000000000 : ℝ)^3291
        have hw : |(2712765459/5000000000 : ℝ)|=(2712765459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232575749/10000000000 : ℝ)|^4315 ≤ (42775333294647/100000000000000 : ℝ)^3291
        have hw : |(5232575749/10000000000 : ℝ)|=(5232575749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_1 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352218277/10000000000 : ℝ)*x 0 + (-2129745063/10000000000 : ℝ)*x 1 + (2616287819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352218277/10000000000 : ℝ)^4315 ≤ (22031125115439/50000000000000 : ℝ)^3291 := by
    have hnat : (5352218277 : ℕ)^4315*50000000000000^3291 ≤ 22031125115439^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352218277 10000000000 22031125115439 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2129745063/10000000000 : ℝ)^4315 ≤ (6581208828429/50000000000000 : ℝ)^3291 := by
    have hnat : (2129745063 : ℕ)^4315*50000000000000^3291 ≤ 6581208828429^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129745063 10000000000 6581208828429 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616287819/5000000000 : ℝ)^4315 ≤ (21387666052451/50000000000000 : ℝ)^3291 := by
    have hnat : (2616287819 : ℕ)^4315*50000000000000^3291 ≤ 21387666052451^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616287819 5000000000 21387666052451 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352218277/10000000000 : ℝ), (-2129745063/10000000000 : ℝ), (2616287819/5000000000 : ℝ)] ![(22031125115439/50000000000000 : ℝ), (6581208828429/50000000000000 : ℝ), (21387666052451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352218277/10000000000 : ℝ)|^4315 ≤ (22031125115439/50000000000000 : ℝ)^3291
        have hw : |(5352218277/10000000000 : ℝ)|=(5352218277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2129745063/10000000000 : ℝ)|^4315 ≤ (6581208828429/50000000000000 : ℝ)^3291
        have hw : |(-2129745063/10000000000 : ℝ)|=(2129745063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616287819/5000000000 : ℝ)|^4315 ≤ (21387666052451/50000000000000 : ℝ)^3291
        have hw : |(2616287819/5000000000 : ℝ)|=(2616287819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_2 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676109073/5000000000 : ℝ)*x 0 + (5232575833/10000000000 : ℝ)*x 1 + (-1064872489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676109073/5000000000 : ℝ)^4315 ≤ (44062248816853/100000000000000 : ℝ)^3291 := by
    have hnat : (2676109073 : ℕ)^4315*100000000000000^3291 ≤ 44062248816853^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676109073 5000000000 44062248816853 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232575833/10000000000 : ℝ)^4315 ≤ (21387667097497/50000000000000 : ℝ)^3291 := by
    have hnat : (5232575833 : ℕ)^4315*50000000000000^3291 ≤ 21387667097497^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232575833 10000000000 21387667097497 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064872489/5000000000 : ℝ)^4315 ≤ (13162416968079/100000000000000 : ℝ)^3291 := by
    have hnat : (1064872489 : ℕ)^4315*100000000000000^3291 ≤ 13162416968079^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064872489 5000000000 13162416968079 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676109073/5000000000 : ℝ), (5232575833/10000000000 : ℝ), (-1064872489/5000000000 : ℝ)] ![(44062248816853/100000000000000 : ℝ), (21387667097497/50000000000000 : ℝ), (13162416968079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676109073/5000000000 : ℝ)|^4315 ≤ (44062248816853/100000000000000 : ℝ)^3291
        have hw : |(2676109073/5000000000 : ℝ)|=(2676109073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232575833/10000000000 : ℝ)|^4315 ≤ (21387667097497/50000000000000 : ℝ)^3291
        have hw : |(5232575833/10000000000 : ℝ)|=(5232575833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1064872489/5000000000 : ℝ)|^4315 ≤ (13162416968079/100000000000000 : ℝ)^3291
        have hw : |(-1064872489/5000000000 : ℝ)|=(1064872489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_3 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2161121837/5000000000 : ℝ)*x 0 + (4123605691/10000000000 : ℝ)*x 1 + (4529742251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161121837/5000000000 : ℝ)^4315 ≤ (16646755152069/50000000000000 : ℝ)^3291 := by
    have hnat : (2161121837 : ℕ)^4315*50000000000000^3291 ≤ 16646755152069^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161121837 5000000000 16646755152069 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4123605691/10000000000 : ℝ)^4315 ≤ (31301848417987/100000000000000 : ℝ)^3291 := by
    have hnat : (4123605691 : ℕ)^4315*100000000000000^3291 ≤ 31301848417987^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123605691 10000000000 31301848417987 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4529742251/10000000000 : ℝ)^4315 ≤ (2212790078903/6250000000000 : ℝ)^3291 := by
    have hnat : (4529742251 : ℕ)^4315*6250000000000^3291 ≤ 2212790078903^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529742251 10000000000 2212790078903 6250000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161121837/5000000000 : ℝ), (4123605691/10000000000 : ℝ), (4529742251/10000000000 : ℝ)] ![(16646755152069/50000000000000 : ℝ), (31301848417987/100000000000000 : ℝ), (2212790078903/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161121837/5000000000 : ℝ)|^4315 ≤ (16646755152069/50000000000000 : ℝ)^3291
        have hw : |(2161121837/5000000000 : ℝ)|=(2161121837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4123605691/10000000000 : ℝ)|^4315 ≤ (31301848417987/100000000000000 : ℝ)^3291
        have hw : |(4123605691/10000000000 : ℝ)|=(4123605691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4529742251/10000000000 : ℝ)|^4315 ≤ (2212790078903/6250000000000 : ℝ)^3291
        have hw : |(4529742251/10000000000 : ℝ)|=(4529742251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_4 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-507795387/2500000000 : ℝ)*x 0 + (1308343463/2500000000 : ℝ)*x 1 + (339045493/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507795387/2500000000 : ℝ)^4315 ≤ (2473908507909/20000000000000 : ℝ)^3291 := by
    have hnat : (507795387 : ℕ)^4315*20000000000000^3291 ≤ 2473908507909^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507795387 2500000000 2473908507909 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308343463/2500000000 : ℝ)^4315 ≤ (42783887901279/100000000000000 : ℝ)^3291 := by
    have hnat : (1308343463 : ℕ)^4315*100000000000000^3291 ≤ 42783887901279^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308343463 2500000000 42783887901279 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339045493/625000000 : ℝ)^4315 ≤ (22423284774677/50000000000000 : ℝ)^3291 := by
    have hnat : (339045493 : ℕ)^4315*50000000000000^3291 ≤ 22423284774677^3291*625000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339045493 625000000 22423284774677 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-507795387/2500000000 : ℝ), (1308343463/2500000000 : ℝ), (339045493/625000000 : ℝ)] ![(2473908507909/20000000000000 : ℝ), (42783887901279/100000000000000 : ℝ), (22423284774677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-507795387/2500000000 : ℝ)|^4315 ≤ (2473908507909/20000000000000 : ℝ)^3291
        have hw : |(-507795387/2500000000 : ℝ)|=(507795387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308343463/2500000000 : ℝ)|^4315 ≤ (42783887901279/100000000000000 : ℝ)^3291
        have hw : |(1308343463/2500000000 : ℝ)|=(1308343463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339045493/625000000 : ℝ)|^4315 ≤ (22423284774677/50000000000000 : ℝ)^3291
        have hw : |(339045493/625000000 : ℝ)|=(339045493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_5 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302442083/10000000000 : ℝ)*x 0 + (-242199127/1250000000 : ℝ)*x 1 + (5424728581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302442083/10000000000 : ℝ)^4315 ≤ (43525740890139/100000000000000 : ℝ)^3291 := by
    have hnat : (5302442083 : ℕ)^4315*100000000000000^3291 ≤ 43525740890139^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302442083 10000000000 43525740890139 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242199127/1250000000 : ℝ)^4315 ≤ (11627682039189/100000000000000 : ℝ)^3291 := by
    have hnat : (242199127 : ℕ)^4315*100000000000000^3291 ≤ 11627682039189^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242199127 1250000000 11627682039189 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424728581/10000000000 : ℝ)^4315 ≤ (560582213263/1250000000000 : ℝ)^3291 := by
    have hnat : (5424728581 : ℕ)^4315*1250000000000^3291 ≤ 560582213263^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424728581 10000000000 560582213263 1250000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302442083/10000000000 : ℝ), (-242199127/1250000000 : ℝ), (5424728581/10000000000 : ℝ)] ![(43525740890139/100000000000000 : ℝ), (11627682039189/100000000000000 : ℝ), (560582213263/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302442083/10000000000 : ℝ)|^4315 ≤ (43525740890139/100000000000000 : ℝ)^3291
        have hw : |(5302442083/10000000000 : ℝ)|=(5302442083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-242199127/1250000000 : ℝ)|^4315 ≤ (11627682039189/100000000000000 : ℝ)^3291
        have hw : |(-242199127/1250000000 : ℝ)|=(242199127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424728581/10000000000 : ℝ)|^4315 ≤ (560582213263/1250000000000 : ℝ)^3291
        have hw : |(5424728581/10000000000 : ℝ)|=(5424728581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_6 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651221899/5000000000 : ℝ)*x 0 + (5424727427/10000000000 : ℝ)*x 1 + (-96879613/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651221899/5000000000 : ℝ)^4315 ≤ (10881439837063/25000000000000 : ℝ)^3291 := by
    have hnat : (2651221899 : ℕ)^4315*25000000000000^3291 ≤ 10881439837063^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651221899 5000000000 10881439837063 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424727427/10000000000 : ℝ)^4315 ≤ (44846564552403/100000000000000 : ℝ)^3291 := by
    have hnat : (5424727427 : ℕ)^4315*100000000000000^3291 ≤ 44846564552403^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424727427 10000000000 44846564552403 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96879613/500000000 : ℝ)^4315 ≤ (11627676090719/100000000000000 : ℝ)^3291 := by
    have hnat : (96879613 : ℕ)^4315*100000000000000^3291 ≤ 11627676090719^3291*500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96879613 500000000 11627676090719 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651221899/5000000000 : ℝ), (5424727427/10000000000 : ℝ), (-96879613/500000000 : ℝ)] ![(10881439837063/25000000000000 : ℝ), (44846564552403/100000000000000 : ℝ), (11627676090719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651221899/5000000000 : ℝ)|^4315 ≤ (10881439837063/25000000000000 : ℝ)^3291
        have hw : |(2651221899/5000000000 : ℝ)|=(2651221899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424727427/10000000000 : ℝ)|^4315 ≤ (44846564552403/100000000000000 : ℝ)^3291
        have hw : |(5424727427/10000000000 : ℝ)|=(5424727427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96879613/500000000 : ℝ)|^4315 ≤ (11627676090719/100000000000000 : ℝ)^3291
        have hw : |(-96879613/500000000 : ℝ)|=(96879613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_7 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322284407/10000000000 : ℝ)*x 0 + (1132015377/2500000000 : ℝ)*x 1 + (515661843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322284407/10000000000 : ℝ)^4315 ≤ (33293921690881/100000000000000 : ℝ)^3291 := by
    have hnat : (4322284407 : ℕ)^4315*100000000000000^3291 ≤ 33293921690881^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322284407 10000000000 33293921690881 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132015377/2500000000 : ℝ)^4315 ≤ (2211713623899/6250000000000 : ℝ)^3291 := by
    have hnat : (1132015377 : ℕ)^4315*6250000000000^3291 ≤ 2211713623899^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132015377 2500000000 2211713623899 6250000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515661843/1250000000 : ℝ)^4315 ≤ (31318660314987/100000000000000 : ℝ)^3291 := by
    have hnat : (515661843 : ℕ)^4315*100000000000000^3291 ≤ 31318660314987^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515661843 1250000000 31318660314987 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322284407/10000000000 : ℝ), (1132015377/2500000000 : ℝ), (515661843/1250000000 : ℝ)] ![(33293921690881/100000000000000 : ℝ), (2211713623899/6250000000000 : ℝ), (31318660314987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322284407/10000000000 : ℝ)|^4315 ≤ (33293921690881/100000000000000 : ℝ)^3291
        have hw : |(4322284407/10000000000 : ℝ)|=(4322284407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132015377/2500000000 : ℝ)|^4315 ≤ (2211713623899/6250000000000 : ℝ)^3291
        have hw : |(1132015377/2500000000 : ℝ)|=(1132015377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(515661843/1250000000 : ℝ)|^4315 ≤ (31318660314987/100000000000000 : ℝ)^3291
        have hw : |(515661843/1250000000 : ℝ)|=(515661843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_8 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41894987/5000000000 : ℝ)*x 0 + (285964821/500000000 : ℝ)*x 1 + (756272543/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41894987/5000000000 : ℝ)^4315 ≤ (189229955669/100000000000000 : ℝ)^3291 := by
    have hnat : (41894987 : ℕ)^4315*100000000000000^3291 ≤ 189229955669^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41894987 5000000000 189229955669 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285964821/500000000 : ℝ)^4315 ≤ (48066152839121/100000000000000 : ℝ)^3291 := by
    have hnat : (285964821 : ℕ)^4315*100000000000000^3291 ≤ 48066152839121^3291*500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285964821 500000000 48066152839121 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (756272543/1250000000 : ℝ)^4315 ≤ (1034892343927/2000000000000 : ℝ)^3291 := by
    have hnat : (756272543 : ℕ)^4315*2000000000000^3291 ≤ 1034892343927^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756272543 1250000000 1034892343927 2000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41894987/5000000000 : ℝ), (285964821/500000000 : ℝ), (756272543/1250000000 : ℝ)] ![(189229955669/100000000000000 : ℝ), (48066152839121/100000000000000 : ℝ), (1034892343927/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41894987/5000000000 : ℝ)|^4315 ≤ (189229955669/100000000000000 : ℝ)^3291
        have hw : |(-41894987/5000000000 : ℝ)|=(41894987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285964821/500000000 : ℝ)|^4315 ≤ (48066152839121/100000000000000 : ℝ)^3291
        have hw : |(285964821/500000000 : ℝ)|=(285964821/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(756272543/1250000000 : ℝ)|^4315 ≤ (1034892343927/2000000000000 : ℝ)^3291
        have hw : |(756272543/1250000000 : ℝ)|=(756272543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_9 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (508954077/5000000000 : ℝ)*x 0 + (-4258261203/10000000000 : ℝ)*x 1 + (1743698513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508954077/5000000000 : ℝ)^4315 ≤ (249991655959/5000000000000 : ℝ)^3291 := by
    have hnat : (508954077 : ℕ)^4315*5000000000000^3291 ≤ 249991655959^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508954077 5000000000 249991655959 5000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4258261203/10000000000 : ℝ)^4315 ≤ (32648807581981/100000000000000 : ℝ)^3291 := by
    have hnat : (4258261203 : ℕ)^4315*100000000000000^3291 ≤ 32648807581981^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258261203 10000000000 32648807581981 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1743698513/2500000000 : ℝ)^4315 ≤ (31175679641069/50000000000000 : ℝ)^3291 := by
    have hnat : (1743698513 : ℕ)^4315*50000000000000^3291 ≤ 31175679641069^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743698513 2500000000 31175679641069 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(508954077/5000000000 : ℝ), (-4258261203/10000000000 : ℝ), (1743698513/2500000000 : ℝ)] ![(249991655959/5000000000000 : ℝ), (32648807581981/100000000000000 : ℝ), (31175679641069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(508954077/5000000000 : ℝ)|^4315 ≤ (249991655959/5000000000000 : ℝ)^3291
        have hw : |(508954077/5000000000 : ℝ)|=(508954077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4258261203/10000000000 : ℝ)|^4315 ≤ (32648807581981/100000000000000 : ℝ)^3291
        have hw : |(-4258261203/10000000000 : ℝ)|=(4258261203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1743698513/2500000000 : ℝ)|^4315 ≤ (31175679641069/50000000000000 : ℝ)^3291
        have hw : |(1743698513/2500000000 : ℝ)|=(1743698513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_10 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (203585311/2000000000 : ℝ)*x 0 + (6974834829/10000000000 : ℝ)*x 1 + (-4258201871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203585311/2000000000 : ℝ)^4315 ≤ (1249987906441/25000000000000 : ℝ)^3291 := by
    have hnat : (203585311 : ℕ)^4315*25000000000000^3291 ≤ 1249987906441^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203585311 2000000000 1249987906441 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6974834829/10000000000 : ℝ)^4315 ≤ (62351837232859/100000000000000 : ℝ)^3291 := by
    have hnat : (6974834829 : ℕ)^4315*100000000000000^3291 ≤ 62351837232859^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6974834829 10000000000 62351837232859 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4258201871/10000000000 : ℝ)^4315 ≤ (6529642225861/20000000000000 : ℝ)^3291 := by
    have hnat : (4258201871 : ℕ)^4315*20000000000000^3291 ≤ 6529642225861^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258201871 10000000000 6529642225861 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(203585311/2000000000 : ℝ), (6974834829/10000000000 : ℝ), (-4258201871/10000000000 : ℝ)] ![(1249987906441/25000000000000 : ℝ), (62351837232859/100000000000000 : ℝ), (6529642225861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(203585311/2000000000 : ℝ)|^4315 ≤ (1249987906441/25000000000000 : ℝ)^3291
        have hw : |(203585311/2000000000 : ℝ)|=(203585311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6974834829/10000000000 : ℝ)|^4315 ≤ (62351837232859/100000000000000 : ℝ)^3291
        have hw : |(6974834829/10000000000 : ℝ)|=(6974834829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4258201871/10000000000 : ℝ)|^4315 ≤ (6529642225861/20000000000000 : ℝ)^3291
        have hw : |(-4258201871/10000000000 : ℝ)|=(4258201871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s3_11 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (473411693/5000000000 : ℝ)*x 0 + (5847676047/10000000000 : ℝ)*x 1 + (2763905011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473411693/5000000000 : ℝ)^4315 ≤ (4547088468381/100000000000000 : ℝ)^3291 := by
    have hnat : (473411693 : ℕ)^4315*100000000000000^3291 ≤ 4547088468381^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473411693 5000000000 4547088468381 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5847676047/10000000000 : ℝ)^4315 ≤ (49485707292897/100000000000000 : ℝ)^3291 := by
    have hnat : (5847676047 : ℕ)^4315*100000000000000^3291 ≤ 49485707292897^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5847676047 10000000000 49485707292897 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2763905011/5000000000 : ℝ)^4315 ≤ (22983602110439/50000000000000 : ℝ)^3291 := by
    have hnat : (2763905011 : ℕ)^4315*50000000000000^3291 ≤ 22983602110439^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2763905011 5000000000 22983602110439 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(473411693/5000000000 : ℝ), (5847676047/10000000000 : ℝ), (2763905011/5000000000 : ℝ)] ![(4547088468381/100000000000000 : ℝ), (49485707292897/100000000000000 : ℝ), (22983602110439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(473411693/5000000000 : ℝ)|^4315 ≤ (4547088468381/100000000000000 : ℝ)^3291
        have hw : |(473411693/5000000000 : ℝ)|=(473411693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5847676047/10000000000 : ℝ)|^4315 ≤ (49485707292897/100000000000000 : ℝ)^3291
        have hw : |(5847676047/10000000000 : ℝ)|=(5847676047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2763905011/5000000000 : ℝ)|^4315 ≤ (22983602110439/50000000000000 : ℝ)^3291
        have hw : |(2763905011/5000000000 : ℝ)|=(2763905011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1355_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (621/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5457/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14997/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (621/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (621/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (621/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (621/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (621/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (621/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (621/6250 : ℝ) ^ (2157/512 : ℝ) ≤ (5961589639354009/100000000000000000000 : ℝ) := by
    have hpowers : (621/6250 : ℝ)^2157 ≤ (5961589639354009/100000000000000000000 : ℝ)^512 := by
      have hnat : (621 : ℕ)^2157*100000000000000000000^512 ≤ 5961589639354009^512*6250^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        621 6250 5961589639354009 100000000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (621/6250 : ℝ)) (X := (5961589639354009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16053/100000 : ℝ) ^ (2157/512 : ℝ) ≤ (22493922329809899/50000000000000000000 : ℝ) := by
    have hpowers : (16053/100000 : ℝ)^2157 ≤ (22493922329809899/50000000000000000000 : ℝ)^512 := by
      have hnat : (16053 : ℕ)^2157*50000000000000000000^512 ≤ 22493922329809899^512*100000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16053 100000 22493922329809899 50000000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16053/100000 : ℝ)) (X := (22493922329809899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005961589639354009/50000000000000000000 : ℝ) ≤ (2500070750930239/2500000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (50005961589639354009/50000000000000000000 : ℝ)^512 ≤ (2500070750930239/2500000000000000 : ℝ)^2157 := by
      have hnat : (50005961589639354009 : ℕ)^512*2500000000000000^2157 ≤ 2500070750930239^2157*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005961589639354009 50000000000000000000 2500070750930239 2500000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070750930239/2500000000000000 : ℝ)) (X := (50005961589639354009/50000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050949434298973807/100000000000000000000 : ℝ) ≤ (10001209135090531/10000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (100050949434298973807/100000000000000000000 : ℝ)^512 ≤ (10001209135090531/10000000000000000 : ℝ)^2157 := by
      have hnat : (100050949434298973807 : ℕ)^512*10000000000000000^2157 ≤ 10001209135090531^2157*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050949434298973807 100000000000000000000 10001209135090531 10000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001209135090531/10000000000000000 : ℝ)) (X := (100050949434298973807/100000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022493922329809899/25000000000000000000 : ℝ) ≤ (5001067633230053/5000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (25022493922329809899/25000000000000000000 : ℝ)^512 ≤ (5001067633230053/5000000000000000 : ℝ)^2157 := by
      have hnat : (25022493922329809899 : ℕ)^512*5000000000000000^2157 ≤ 5001067633230053^2157*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022493922329809899 25000000000000000000 5001067633230053 5000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001067633230053/5000000000000000 : ℝ)) (X := (25022493922329809899/25000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5961589639354009/100000000000000000000 : ℝ) ≤ ((5096110587598741121/5097500000000000000 : ℝ)+2*(12348418261/8156000000000 : ℝ)*(621/6250 : ℝ))^(2157/512 : ℝ) := by
    rw [show (5096110587598741121/5097500000000000000 : ℝ)+2*(12348418261/8156000000000 : ℝ)*(621/6250 : ℝ)=(2500070750930239/2500000000000000 : ℝ) by norm_num, show 1+2*(5961589639354009/100000000000000000000 : ℝ)=(50005961589639354009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22493922329809899/50000000000000000000 : ℝ)+(5961589639354009/100000000000000000000 : ℝ) ≤ ((5096110587598741121/5097500000000000000 : ℝ)+(12348418261/8156000000000 : ℝ)*((16053/100000 : ℝ)+(621/6250 : ℝ)))^(2157/512 : ℝ) := by
    rw [show (5096110587598741121/5097500000000000000 : ℝ)+(12348418261/8156000000000 : ℝ)*((16053/100000 : ℝ)+(621/6250 : ℝ))=(10001209135090531/10000000000000000 : ℝ) by norm_num, show 1+(22493922329809899/50000000000000000000 : ℝ)+(5961589639354009/100000000000000000000 : ℝ)=(100050949434298973807/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22493922329809899/50000000000000000000 : ℝ) ≤ ((5096110587598741121/5097500000000000000 : ℝ)+2*(12348418261/8156000000000 : ℝ)*(16053/100000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (5096110587598741121/5097500000000000000 : ℝ)+2*(12348418261/8156000000000 : ℝ)*(16053/100000 : ℝ)=(5001067633230053/5000000000000000 : ℝ) by norm_num, show 1+2*(22493922329809899/50000000000000000000 : ℝ)=(25022493922329809899/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5096110587598741121/5097500000000000000 : ℝ)*(X 1 0+X 2 0)+(12348418261/8156000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (621/6250 : ℝ)) (hi := (16053/100000 : ℝ)) (c := (5096110587598741121/5097500000000000000 : ℝ)) (alpha := (12348418261/8156000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5096110587598741121/5097500000000000000 : ℝ)*(X 0 1+X 2 1)+(12348418261/8156000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (621/6250 : ℝ)) (hi := (16053/100000 : ℝ)) (c := (5096110587598741121/5097500000000000000 : ℝ)) (alpha := (12348418261/8156000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5096110587598741121/5097500000000000000 : ℝ)*(X 0 2+X 1 2)+(12348418261/8156000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (621/6250 : ℝ)) (hi := (16053/100000 : ℝ)) (c := (5096110587598741121/5097500000000000000 : ℝ)) (alpha := (12348418261/8156000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2031162769/10000000000 : ℝ)*X 0 0+(2712765459/5000000000 : ℝ)*X 0 1+(5232575749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352218277/10000000000 : ℝ)*X 1 0+(-2129745063/10000000000 : ℝ)*X 1 1+(2616287819/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676109073/5000000000 : ℝ)*X 2 0+(5232575833/10000000000 : ℝ)*X 2 1+(-1064872489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161121837/5000000000 : ℝ)*X 0 0+(4123605691/10000000000 : ℝ)*X 0 1+(4529742251/10000000000 : ℝ)*X 0 2+(2161121837/5000000000 : ℝ)*X 1 0+(4123605691/10000000000 : ℝ)*X 1 1+(4529742251/10000000000 : ℝ)*X 1 2+(2161121837/5000000000 : ℝ)*X 2 0+(4123605691/10000000000 : ℝ)*X 2 1+(4529742251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-507795387/2500000000 : ℝ)*X 0 0+(1308343463/2500000000 : ℝ)*X 0 1+(339045493/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302442083/10000000000 : ℝ)*X 1 0+(-242199127/1250000000 : ℝ)*X 1 1+(5424728581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651221899/5000000000 : ℝ)*X 2 0+(5424727427/10000000000 : ℝ)*X 2 1+(-96879613/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322284407/10000000000 : ℝ)*X 0 0+(1132015377/2500000000 : ℝ)*X 0 1+(515661843/1250000000 : ℝ)*X 0 2+(4322284407/10000000000 : ℝ)*X 1 0+(1132015377/2500000000 : ℝ)*X 1 1+(515661843/1250000000 : ℝ)*X 1 2+(4322284407/10000000000 : ℝ)*X 2 0+(1132015377/2500000000 : ℝ)*X 2 1+(515661843/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-41894987/5000000000 : ℝ)*X 0 0+(285964821/500000000 : ℝ)*X 0 1+(756272543/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((508954077/5000000000 : ℝ)*X 1 0+(-4258261203/10000000000 : ℝ)*X 1 1+(1743698513/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((203585311/2000000000 : ℝ)*X 2 0+(6974834829/10000000000 : ℝ)*X 2 1+(-4258201871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((473411693/5000000000 : ℝ)*X 0 0+(5847676047/10000000000 : ℝ)*X 0 1+(2763905011/5000000000 : ℝ)*X 0 2+(473411693/5000000000 : ℝ)*X 1 0+(5847676047/10000000000 : ℝ)*X 1 1+(2763905011/5000000000 : ℝ)*X 1 2+(473411693/5000000000 : ℝ)*X 2 0+(5847676047/10000000000 : ℝ)*X 2 1+(2763905011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (154268390239673727129899739/25487500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39569613/25000000000000 : ℝ)*(lower2) + (18928563/12500000000000 : ℝ)*(lower4) + (764478518501947/20000000000000 : ℝ)*(major0) + (764478518501947/20000000000000 : ℝ)*(major1) + (764478518501947/20000000000000 : ℝ)*(major2) + (647819206887153/12500000000000 : ℝ)*(sp0) + (5182550607592867/100000000000000 : ℝ)*(sp1) + (5182554656828997/100000000000000 : ℝ)*(sp2) + (615556995865897/25000000000000 : ℝ)*(sp3) + (1960917989/50000000000000 : ℝ)*(sp5) + (945048327/50000000000000 : ℝ)*(sp7) + (1454605069/100000000000000 : ℝ)*(sp8) + (72534181/12500000000000 : ℝ)*(sp9) + (452873297/100000000000000 : ℝ)*(sp10) + (1231114936780121/50000000000000 : ℝ)*(f.failure) + (5182555109702293/100000000000000 : ℝ)*(f.sum) + (4075131482083/2039000000000000000000000000 : ℝ)*base65 + (418576826245437587/101950000000000000000000000000000 : ℝ)*base67 + (649327446273637587/101950000000000000000000000000000 : ℝ)*base69 + (1630211218902587587/101950000000000000000000000000000 : ℝ)*base71 + (2595506436289/1019500000000000000000000000 : ℝ)*base74 + (48310975585037587/101950000000000000000000000000000 : ℝ)*base75 + (1556469911737812413/101950000000000000000000000000000 : ℝ)*base78 + (173696382146537587/101950000000000000000000000000000 : ℝ)*base79 + (8291388793427/1019500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (35746187/2500000000000000000000 : ℝ)*base89 + (35746187/2500000000000000000000 : ℝ)*base91 + (35746187/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5196347476916954413377/2039000000000000000000000000 : ℝ) := by norm_num
    linear_combination (503179661/100000000000000 : ℝ)*(lower2) + (192719266960969/5000000000000 : ℝ)*(major0) + (192719266960969/5000000000000 : ℝ)*(major1) + (192719266960969/5000000000000 : ℝ)*(major2) + (5227529781/50000000000000 : ℝ)*(sp1) + (4639956459/100000000000000 : ℝ)*(sp2) + (487602483/25000000000000 : ℝ)*(sp3) + (5225929715163847/100000000000000 : ℝ)*(sp4) + (1045184367679749/20000000000000 : ℝ)*(sp5) + (5225926803647637/100000000000000 : ℝ)*(sp6) + (248283545771221/10000000000000 : ℝ)*(sp7) + (128914723/5000000000000 : ℝ)*(sp8) + (212463553/25000000000000 : ℝ)*(sp10) + (891909021/100000000000000 : ℝ)*(sp11) + (620709575007791/25000000000000 : ℝ)*(f.failure) + (5225932293458307/100000000000000 : ℝ)*(f.sum) + (205516975671/63718750000000000000000000 : ℝ)*base66 + (65205282042968749/25487500000000000000000000000000 : ℝ)*base67 + (294444661768056249/25487500000000000000000000000000 : ℝ)*base69 + (43249834725406251/25487500000000000000000000000000 : ℝ)*base72 + (6058236899133/2039000000000000000000000000 : ℝ)*base73 + (36633427094131251/25487500000000000000000000000000 : ℝ)*base76 + (270534182122731249/25487500000000000000000000000000 : ℝ)*base77 + (227235317291406251/25487500000000000000000000000000 : ℝ)*base80 + (134130419681/12743750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16681677/1250000000000000000000 : ℝ)*base89 + (16681677/1250000000000000000000 : ℝ)*base91 + (16681677/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1355_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (621/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5457/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14997/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1355_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1355_s4_0 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-406504509/2000000000 : ℝ)*x 0 + (2707183383/5000000000 : ℝ)*x 1 + (1048569317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406504509/2000000000 : ℝ)^4315 ≤ (386882846201/3125000000000 : ℝ)^3291 := by
    have hnat : (406504509 : ℕ)^4315*3125000000000^3291 ≤ 386882846201^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406504509 2000000000 386882846201 3125000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707183383/5000000000 : ℝ)^4315 ≤ (174743339309/390625000000 : ℝ)^3291 := by
    have hnat : (2707183383 : ℕ)^4315*390625000000^3291 ≤ 174743339309^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707183383 5000000000 174743339309 390625000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048569317/2000000000 : ℝ)^4315 ≤ (21442727018807/50000000000000 : ℝ)^3291 := by
    have hnat : (1048569317 : ℕ)^4315*50000000000000^3291 ≤ 21442727018807^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048569317 2000000000 21442727018807 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-406504509/2000000000 : ℝ), (2707183383/5000000000 : ℝ), (1048569317/2000000000 : ℝ)] ![(386882846201/3125000000000 : ℝ), (174743339309/390625000000 : ℝ), (21442727018807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-406504509/2000000000 : ℝ)|^4315 ≤ (386882846201/3125000000000 : ℝ)^3291
        have hw : |(-406504509/2000000000 : ℝ)|=(406504509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707183383/5000000000 : ℝ)|^4315 ≤ (174743339309/390625000000 : ℝ)^3291
        have hw : |(2707183383/5000000000 : ℝ)|=(2707183383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048569317/2000000000 : ℝ)|^4315 ≤ (21442727018807/50000000000000 : ℝ)^3291
        have hw : |(1048569317/2000000000 : ℝ)|=(1048569317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s4_1 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674683467/5000000000 : ℝ)*x 0 + (-529986561/2500000000 : ℝ)*x 1 + (1310711619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674683467/5000000000 : ℝ)^4315 ≤ (44031475147643/100000000000000 : ℝ)^3291 := by
    have hnat : (2674683467 : ℕ)^4315*100000000000000^3291 ≤ 44031475147643^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674683467 5000000000 44031475147643 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529986561/2500000000 : ℝ)^4315 ≤ (3270767989283/25000000000000 : ℝ)^3291 := by
    have hnat : (529986561 : ℕ)^4315*25000000000000^3291 ≤ 3270767989283^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529986561 2500000000 3270767989283 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310711619/2500000000 : ℝ)^4315 ≤ (42885452868593/100000000000000 : ℝ)^3291 := by
    have hnat : (1310711619 : ℕ)^4315*100000000000000^3291 ≤ 42885452868593^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310711619 2500000000 42885452868593 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674683467/5000000000 : ℝ), (-529986561/2500000000 : ℝ), (1310711619/2500000000 : ℝ)] ![(44031475147643/100000000000000 : ℝ), (3270767989283/25000000000000 : ℝ), (42885452868593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674683467/5000000000 : ℝ)|^4315 ≤ (44031475147643/100000000000000 : ℝ)^3291
        have hw : |(2674683467/5000000000 : ℝ)|=(2674683467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529986561/2500000000 : ℝ)|^4315 ≤ (3270767989283/25000000000000 : ℝ)^3291
        have hw : |(-529986561/2500000000 : ℝ)|=(529986561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310711619/2500000000 : ℝ)|^4315 ≤ (42885452868593/100000000000000 : ℝ)^3291
        have hw : |(1310711619/2500000000 : ℝ)|=(1310711619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s4_2 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069873383/2000000000 : ℝ)*x 0 + (5242846617/10000000000 : ℝ)*x 1 + (-529986521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069873383/2000000000 : ℝ)^4315 ≤ (4403147494259/10000000000000 : ℝ)^3291 := by
    have hnat : (1069873383 : ℕ)^4315*10000000000000^3291 ≤ 4403147494259^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069873383 2000000000 4403147494259 10000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242846617/10000000000 : ℝ)^4315 ≤ (42885454380813/100000000000000 : ℝ)^3291 := by
    have hnat : (5242846617 : ℕ)^4315*100000000000000^3291 ≤ 42885454380813^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242846617 10000000000 42885454380813 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529986521/2500000000 : ℝ)^4315 ≤ (6541535331233/50000000000000 : ℝ)^3291 := by
    have hnat : (529986521 : ℕ)^4315*50000000000000^3291 ≤ 6541535331233^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529986521 2500000000 6541535331233 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069873383/2000000000 : ℝ), (5242846617/10000000000 : ℝ), (-529986521/2500000000 : ℝ)] ![(4403147494259/10000000000000 : ℝ), (42885454380813/100000000000000 : ℝ), (6541535331233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069873383/2000000000 : ℝ)|^4315 ≤ (4403147494259/10000000000000 : ℝ)^3291
        have hw : |(1069873383/2000000000 : ℝ)|=(1069873383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242846617/10000000000 : ℝ)|^4315 ≤ (42885454380813/100000000000000 : ℝ)^3291
        have hw : |(5242846617/10000000000 : ℝ)|=(5242846617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529986521/2500000000 : ℝ)|^4315 ≤ (6541535331233/50000000000000 : ℝ)^3291
        have hw : |(-529986521/2500000000 : ℝ)|=(529986521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s4_3 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2161535181/5000000000 : ℝ)*x 0 + (829212471/2000000000 : ℝ)*x 1 + (901416323/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161535181/5000000000 : ℝ)^4315 ≤ (6660371950617/20000000000000 : ℝ)^3291 := by
    have hnat : (2161535181 : ℕ)^4315*20000000000000^3291 ≤ 6660371950617^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161535181 5000000000 6660371950617 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829212471/2000000000 : ℝ)^4315 ≤ (31525544487263/100000000000000 : ℝ)^3291 := by
    have hnat : (829212471 : ℕ)^4315*100000000000000^3291 ≤ 31525544487263^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829212471 2000000000 31525544487263 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901416323/2000000000 : ℝ)^4315 ≤ (4396574467507/12500000000000 : ℝ)^3291 := by
    have hnat : (901416323 : ℕ)^4315*12500000000000^3291 ≤ 4396574467507^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901416323 2000000000 4396574467507 12500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161535181/5000000000 : ℝ), (829212471/2000000000 : ℝ), (901416323/2000000000 : ℝ)] ![(6660371950617/20000000000000 : ℝ), (31525544487263/100000000000000 : ℝ), (4396574467507/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161535181/5000000000 : ℝ)|^4315 ≤ (6660371950617/20000000000000 : ℝ)^3291
        have hw : |(2161535181/5000000000 : ℝ)|=(2161535181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(829212471/2000000000 : ℝ)|^4315 ≤ (31525544487263/100000000000000 : ℝ)^3291
        have hw : |(829212471/2000000000 : ℝ)|=(829212471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901416323/2000000000 : ℝ)|^4315 ≤ (4396574467507/12500000000000 : ℝ)^3291
        have hw : |(901416323/2000000000 : ℝ)|=(901416323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s4_4 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2032535649/10000000000 : ℝ)*x 0 + (2621738861/5000000000 : ℝ)*x 1 + (1353433059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032535649/10000000000 : ℝ)^4315 ≤ (2476071146269/20000000000000 : ℝ)^3291 := by
    have hnat : (2032535649 : ℕ)^4315*20000000000000^3291 ≤ 2476071146269^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032535649 10000000000 2476071146269 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621738861/5000000000 : ℝ)^4315 ≤ (42892223085009/100000000000000 : ℝ)^3291 := by
    have hnat : (2621738861 : ℕ)^4315*100000000000000^3291 ≤ 42892223085009^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621738861 5000000000 42892223085009 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353433059/2500000000 : ℝ)^4315 ≤ (22363710585427/50000000000000 : ℝ)^3291 := by
    have hnat : (1353433059 : ℕ)^4315*50000000000000^3291 ≤ 22363710585427^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353433059 2500000000 22363710585427 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2032535649/10000000000 : ℝ), (2621738861/5000000000 : ℝ), (1353433059/2500000000 : ℝ)] ![(2476071146269/20000000000000 : ℝ), (42892223085009/100000000000000 : ℝ), (22363710585427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2032535649/10000000000 : ℝ)|^4315 ≤ (2476071146269/20000000000000 : ℝ)^3291
        have hw : |(-2032535649/10000000000 : ℝ)|=(2032535649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621738861/5000000000 : ℝ)|^4315 ≤ (42892223085009/100000000000000 : ℝ)^3291
        have hw : |(2621738861/5000000000 : ℝ)|=(2621738861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353433059/2500000000 : ℝ)|^4315 ≤ (22363710585427/50000000000000 : ℝ)^3291
        have hw : |(1353433059/2500000000 : ℝ)|=(1353433059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s4_5 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305121333/10000000000 : ℝ)*x 0 + (-389812147/2000000000 : ℝ)*x 1 + (5413732473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305121333/10000000000 : ℝ)^4315 ≤ (43554579248259/100000000000000 : ℝ)^3291 := by
    have hnat : (5305121333 : ℕ)^4315*100000000000000^3291 ≤ 43554579248259^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305121333 10000000000 43554579248259 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389812147/2000000000 : ℝ)^4315 ≤ (468719880119/4000000000000 : ℝ)^3291 := by
    have hnat : (389812147 : ℕ)^4315*4000000000000^3291 ≤ 468719880119^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389812147 2000000000 468719880119 4000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413732473/10000000000 : ℝ)^4315 ≤ (11181855934541/25000000000000 : ℝ)^3291 := by
    have hnat : (5413732473 : ℕ)^4315*25000000000000^3291 ≤ 11181855934541^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413732473 10000000000 11181855934541 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305121333/10000000000 : ℝ), (-389812147/2000000000 : ℝ), (5413732473/10000000000 : ℝ)] ![(43554579248259/100000000000000 : ℝ), (468719880119/4000000000000 : ℝ), (11181855934541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305121333/10000000000 : ℝ)|^4315 ≤ (43554579248259/100000000000000 : ℝ)^3291
        have hw : |(5305121333/10000000000 : ℝ)|=(5305121333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389812147/2000000000 : ℝ)|^4315 ≤ (468719880119/4000000000000 : ℝ)^3291
        have hw : |(-389812147/2000000000 : ℝ)|=(389812147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413732473/10000000000 : ℝ)|^4315 ≤ (11181855934541/25000000000000 : ℝ)^3291
        have hw : |(5413732473/10000000000 : ℝ)|=(5413732473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s4_6 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652560843/5000000000 : ℝ)*x 0 + (5413732207/10000000000 : ℝ)*x 1 + (-974530309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652560843/5000000000 : ℝ)^4315 ≤ (21777291524053/50000000000000 : ℝ)^3291 := by
    have hnat : (2652560843 : ℕ)^4315*50000000000000^3291 ≤ 21777291524053^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652560843 5000000000 21777291524053 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413732207/10000000000 : ℝ)^4315 ≤ (4472742085671/10000000000000 : ℝ)^3291 := by
    have hnat : (5413732207 : ℕ)^4315*10000000000000^3291 ≤ 4472742085671^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413732207 10000000000 4472742085671 10000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974530309/5000000000 : ℝ)^4315 ≤ (5858998040343/50000000000000 : ℝ)^3291 := by
    have hnat : (974530309 : ℕ)^4315*50000000000000^3291 ≤ 5858998040343^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974530309 5000000000 5858998040343 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652560843/5000000000 : ℝ), (5413732207/10000000000 : ℝ), (-974530309/5000000000 : ℝ)] ![(21777291524053/50000000000000 : ℝ), (4472742085671/10000000000000 : ℝ), (5858998040343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652560843/5000000000 : ℝ)|^4315 ≤ (21777291524053/50000000000000 : ℝ)^3291
        have hw : |(2652560843/5000000000 : ℝ)|=(2652560843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413732207/10000000000 : ℝ)|^4315 ≤ (4472742085671/10000000000000 : ℝ)^3291
        have hw : |(5413732207/10000000000 : ℝ)|=(5413732207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-974530309/5000000000 : ℝ)|^4315 ≤ (5858998040343/50000000000000 : ℝ)^3291
        have hw : |(-974530309/5000000000 : ℝ)|=(974530309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s4_7 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080774539/2500000000 : ℝ)*x 0 + (901150673/2000000000 : ℝ)*x 1 + (1036849319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080774539/2500000000 : ℝ)^4315 ≤ (33302140477761/100000000000000 : ℝ)^3291 := by
    have hnat : (1080774539 : ℕ)^4315*100000000000000^3291 ≤ 33302140477761^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080774539 2500000000 33302140477761 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901150673/2000000000 : ℝ)^4315 ≤ (35159005665893/100000000000000 : ℝ)^3291 := by
    have hnat : (901150673 : ℕ)^4315*100000000000000^3291 ≤ 35159005665893^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901150673 2000000000 35159005665893 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036849319/2500000000 : ℝ)^4315 ≤ (15769426921019/50000000000000 : ℝ)^3291 := by
    have hnat : (1036849319 : ℕ)^4315*50000000000000^3291 ≤ 15769426921019^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036849319 2500000000 15769426921019 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080774539/2500000000 : ℝ), (901150673/2000000000 : ℝ), (1036849319/2500000000 : ℝ)] ![(33302140477761/100000000000000 : ℝ), (35159005665893/100000000000000 : ℝ), (15769426921019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080774539/2500000000 : ℝ)|^4315 ≤ (33302140477761/100000000000000 : ℝ)^3291
        have hw : |(1080774539/2500000000 : ℝ)|=(1080774539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901150673/2000000000 : ℝ)|^4315 ≤ (35159005665893/100000000000000 : ℝ)^3291
        have hw : |(901150673/2000000000 : ℝ)|=(901150673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036849319/2500000000 : ℝ)|^4315 ≤ (15769426921019/50000000000000 : ℝ)^3291
        have hw : |(1036849319/2500000000 : ℝ)|=(1036849319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1355_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5457/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11133/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3691/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5457/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5457/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5457/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5457/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5457/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5457/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5457/50000 : ℝ) ^ (2157/512 : ℝ) ≤ (8853838574129341/100000000000000000000 : ℝ) := by
    have hpowers : (5457/50000 : ℝ)^2157 ≤ (8853838574129341/100000000000000000000 : ℝ)^512 := by
      have hnat : (5457 : ℕ)^2157*100000000000000000000^512 ≤ 8853838574129341^512*50000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5457 50000 8853838574129341 100000000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5457/50000 : ℝ)) (X := (8853838574129341/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14997/100000 : ℝ) ^ (2157/512 : ℝ) ≤ (4221887327487893/12500000000000000000 : ℝ) := by
    have hpowers : (14997/100000 : ℝ)^2157 ≤ (4221887327487893/12500000000000000000 : ℝ)^512 := by
      have hnat : (14997 : ℕ)^2157*12500000000000000000^512 ≤ 4221887327487893^512*100000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14997 100000 4221887327487893 12500000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14997/100000 : ℝ)) (X := (4221887327487893/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008853838574129341/50000000000000000000 : ℝ) ≤ (5000210146466943/5000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (50008853838574129341/50000000000000000000 : ℝ)^512 ≤ (5000210146466943/5000000000000000 : ℝ)^2157 := by
      have hnat : (50008853838574129341 : ℕ)^512*5000000000000000^2157 ≤ 5000210146466943^2157*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008853838574129341 50000000000000000000 5000210146466943 5000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000210146466943/5000000000000000 : ℝ)) (X := (50008853838574129341/50000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008525787438806497/20000000000000000000 : ℝ) ≤ (500050585231539/500000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (20008525787438806497/20000000000000000000 : ℝ)^512 ≤ (500050585231539/500000000000000 : ℝ)^2157 := by
      have hnat : (20008525787438806497 : ℕ)^512*500000000000000^2157 ≤ 500050585231539^2157*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008525787438806497 20000000000000000000 500050585231539 500000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500050585231539/500000000000000 : ℝ)) (X := (20008525787438806497/20000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254221887327487893/6250000000000000000 : ℝ) ≤ (5000801558163837/5000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (6254221887327487893/6250000000000000000 : ℝ)^512 ≤ (5000801558163837/5000000000000000 : ℝ)^2157 := by
      have hnat : (6254221887327487893 : ℕ)^512*5000000000000000^2157 ≤ 5000801558163837^2157*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254221887327487893 6250000000000000000 5000801558163837 5000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000801558163837/5000000000000000 : ℝ)) (X := (6254221887327487893/6250000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8853838574129341/100000000000000000000 : ℝ) ≤ ((6803134453588209051/6805000000000000000 : ℝ)+2*(98568616149/68050000000000 : ℝ)*(5457/50000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (6803134453588209051/6805000000000000000 : ℝ)+2*(98568616149/68050000000000 : ℝ)*(5457/50000 : ℝ)=(5000210146466943/5000000000000000 : ℝ) by norm_num, show 1+2*(8853838574129341/100000000000000000000 : ℝ)=(50008853838574129341/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4221887327487893/12500000000000000000 : ℝ)+(8853838574129341/100000000000000000000 : ℝ) ≤ ((6803134453588209051/6805000000000000000 : ℝ)+(98568616149/68050000000000 : ℝ)*((14997/100000 : ℝ)+(5457/50000 : ℝ)))^(2157/512 : ℝ) := by
    rw [show (6803134453588209051/6805000000000000000 : ℝ)+(98568616149/68050000000000 : ℝ)*((14997/100000 : ℝ)+(5457/50000 : ℝ))=(500050585231539/500000000000000 : ℝ) by norm_num, show 1+(4221887327487893/12500000000000000000 : ℝ)+(8853838574129341/100000000000000000000 : ℝ)=(20008525787438806497/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4221887327487893/12500000000000000000 : ℝ) ≤ ((6803134453588209051/6805000000000000000 : ℝ)+2*(98568616149/68050000000000 : ℝ)*(14997/100000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (6803134453588209051/6805000000000000000 : ℝ)+2*(98568616149/68050000000000 : ℝ)*(14997/100000 : ℝ)=(5000801558163837/5000000000000000 : ℝ) by norm_num, show 1+2*(4221887327487893/12500000000000000000 : ℝ)=(6254221887327487893/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6803134453588209051/6805000000000000000 : ℝ)*(X 1 0+X 2 0)+(98568616149/68050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (5457/50000 : ℝ)) (hi := (14997/100000 : ℝ)) (c := (6803134453588209051/6805000000000000000 : ℝ)) (alpha := (98568616149/68050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6803134453588209051/6805000000000000000 : ℝ)*(X 0 1+X 2 1)+(98568616149/68050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (5457/50000 : ℝ)) (hi := (14997/100000 : ℝ)) (c := (6803134453588209051/6805000000000000000 : ℝ)) (alpha := (98568616149/68050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6803134453588209051/6805000000000000000 : ℝ)*(X 0 2+X 1 2)+(98568616149/68050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (5457/50000 : ℝ)) (hi := (14997/100000 : ℝ)) (c := (6803134453588209051/6805000000000000000 : ℝ)) (alpha := (98568616149/68050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-406504509/2000000000 : ℝ)*X 0 0+(2707183383/5000000000 : ℝ)*X 0 1+(1048569317/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674683467/5000000000 : ℝ)*X 1 0+(-529986561/2500000000 : ℝ)*X 1 1+(1310711619/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069873383/2000000000 : ℝ)*X 2 0+(5242846617/10000000000 : ℝ)*X 2 1+(-529986521/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161535181/5000000000 : ℝ)*X 0 0+(829212471/2000000000 : ℝ)*X 0 1+(901416323/2000000000 : ℝ)*X 0 2+(2161535181/5000000000 : ℝ)*X 1 0+(829212471/2000000000 : ℝ)*X 1 1+(901416323/2000000000 : ℝ)*X 1 2+(2161535181/5000000000 : ℝ)*X 2 0+(829212471/2000000000 : ℝ)*X 2 1+(901416323/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2032535649/10000000000 : ℝ)*X 0 0+(2621738861/5000000000 : ℝ)*X 0 1+(1353433059/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305121333/10000000000 : ℝ)*X 1 0+(-389812147/2000000000 : ℝ)*X 1 1+(5413732473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652560843/5000000000 : ℝ)*X 2 0+(5413732207/10000000000 : ℝ)*X 2 1+(-974530309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080774539/2500000000 : ℝ)*X 0 0+(901150673/2000000000 : ℝ)*X 0 1+(1036849319/2500000000 : ℝ)*X 0 2+(1080774539/2500000000 : ℝ)*X 1 0+(901150673/2000000000 : ℝ)*X 1 1+(1036849319/2500000000 : ℝ)*X 1 2+(1080774539/2500000000 : ℝ)*X 2 0+(901150673/2000000000 : ℝ)*X 2 1+(1036849319/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64022097889990368438362097/8506250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282842307/20000000000000 : ℝ)*(base19) + (167578107/12500000000000 : ℝ)*(base23) + (7071673/25000000000000 : ℝ)*(lower2) + (27197423/50000000000000 : ℝ)*(upper3) + (102472529/50000000000000 : ℝ)*(upper5) + (107502983245251/2500000000000 : ℝ)*(major0) + (107502983245251/2500000000000 : ℝ)*(major1) + (107502983245251/2500000000000 : ℝ)*(major2) + (5830243930217733/100000000000000 : ℝ)*(sp0) + (5830274983172163/100000000000000 : ℝ)*(sp1) + (5830275056758843/100000000000000 : ℝ)*(sp2) + (1384974814952431/50000000000000 : ℝ)*(sp3) + (6493433193/20000000000000 : ℝ)*(sp4) + (12381448937/100000000000000 : ℝ)*(sp7) + (1384981005676899/50000000000000 : ℝ)*(f.failure) + (2915138198691849/50000000000000 : ℝ)*(f.sum) + (1653340217811/680500000000000000000000000 : ℝ)*base66 + (176768249962079301/17012500000000000000000000000000 : ℝ)*base67 + (62057027360779301/17012500000000000000000000000000 : ℝ)*base69 + (119991885314141801/17012500000000000000000000000000 : ℝ)*base71 + (4496744003339/1361000000000000000000000000 : ℝ)*base74 + (74686181970758199/17012500000000000000000000000000 : ℝ)*base76 + (6069021299354301/17012500000000000000000000000000 : ℝ)*base77 + (33407423115458199/17012500000000000000000000000000 : ℝ)*base80 + (2419790161327/680500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5643753/2500000000000000000000 : ℝ)*base89 + (5643753/2500000000000000000000 : ℝ)*base91 + (5643753/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1049713928667100731844788489/170125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (433158607/100000000000000 : ℝ)*(base19) + (135532513/12500000000000 : ℝ)*(base23) + (253412257/100000000000000 : ℝ)*(upper3) + (78212727/100000000000000 : ℝ)*(lower4) + (96963431/100000000000000 : ℝ)*(upper5) + (2166019866423829/50000000000000 : ℝ)*(major0) + (2166019866423829/50000000000000 : ℝ)*(major1) + (2166019866423829/50000000000000 : ℝ)*(major2) + (4941840319/100000000000000 : ℝ)*(sp1) + (738913739/4000000000000 : ℝ)*(sp2) + (2936777711523639/50000000000000 : ℝ)*(sp4) + (183548439001511/3125000000000 : ℝ)*(sp5) + (58735358659437/1000000000000 : ℝ)*(sp6) + (2790523836972997/100000000000000 : ℝ)*(sp7) + (2790523836972997/100000000000000 : ℝ)*(f.failure) + (2936777711523639/50000000000000 : ℝ)*(f.sum) + (12337810554767/3402500000000000000000000000 : ℝ)*base65 + (3072762483126726279/340250000000000000000000000000000 : ℝ)*base67 + (4259764023026976279/340250000000000000000000000000000 : ℝ)*base69 + (5672247620038476279/340250000000000000000000000000000 : ℝ)*base71 + (5710978386861/6805000000000000000000000000 : ℝ)*base74 + (1313285197463976279/340250000000000000000000000000000 : ℝ)*base75 + (2240349113952726279/340250000000000000000000000000000 : ℝ)*base77 + (1416670715251976279/340250000000000000000000000000000 : ℝ)*base79 + (8904740587531/1701250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (48630641/5000000000000000000000 : ℝ)*base90 + (48630641/5000000000000000000000 : ℝ)*base92 + (48630641/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1355_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5457/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11133/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1355_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1355_s5_0 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-101637597/500000000 : ℝ)*x 0 + (2706190719/5000000000 : ℝ)*x 1 + (5244680863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101637597/500000000 : ℝ)^4315 ≤ (12382083133703/100000000000000 : ℝ)^3291 := by
    have hnat : (101637597 : ℕ)^4315*100000000000000^3291 ≤ 12382083133703^3291*500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101637597 500000000 12382083133703 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706190719/5000000000 : ℝ)^4315 ≤ (22356394587757/50000000000000 : ℝ)^3291 := by
    have hnat : (2706190719 : ℕ)^4315*50000000000000^3291 ≤ 22356394587757^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706190719 5000000000 22356394587757 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244680863/10000000000 : ℝ)^4315 ≤ (42905127670991/100000000000000 : ℝ)^3291 := by
    have hnat : (5244680863 : ℕ)^4315*100000000000000^3291 ≤ 42905127670991^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244680863 10000000000 42905127670991 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101637597/500000000 : ℝ), (2706190719/5000000000 : ℝ), (5244680863/10000000000 : ℝ)] ![(12382083133703/100000000000000 : ℝ), (22356394587757/50000000000000 : ℝ), (42905127670991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101637597/500000000 : ℝ)|^4315 ≤ (12382083133703/100000000000000 : ℝ)^3291
        have hw : |(-101637597/500000000 : ℝ)|=(101637597/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706190719/5000000000 : ℝ)|^4315 ≤ (22356394587757/50000000000000 : ℝ)^3291
        have hw : |(2706190719/5000000000 : ℝ)|=(2706190719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244680863/10000000000 : ℝ)|^4315 ≤ (42905127670991/100000000000000 : ℝ)^3291
        have hw : |(5244680863/10000000000 : ℝ)|=(5244680863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s5_1 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348858537/10000000000 : ℝ)*x 0 + (-26477407/125000000 : ℝ)*x 1 + (524468089/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348858537/10000000000 : ℝ)^4315 ≤ (44025988458921/100000000000000 : ℝ)^3291 := by
    have hnat : (5348858537 : ℕ)^4315*100000000000000^3291 ≤ 44025988458921^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348858537 10000000000 44025988458921 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26477407/125000000 : ℝ)^4315 ≤ (1633610445423/12500000000000 : ℝ)^3291 := by
    have hnat : (26477407 : ℕ)^4315*12500000000000^3291 ≤ 1633610445423^3291*125000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26477407 125000000 1633610445423 12500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524468089/1000000000 : ℝ)^4315 ≤ (10726281990149/25000000000000 : ℝ)^3291 := by
    have hnat : (524468089 : ℕ)^4315*25000000000000^3291 ≤ 10726281990149^3291*1000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524468089 1000000000 10726281990149 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348858537/10000000000 : ℝ), (-26477407/125000000 : ℝ), (524468089/1000000000 : ℝ)] ![(44025988458921/100000000000000 : ℝ), (1633610445423/12500000000000 : ℝ), (10726281990149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348858537/10000000000 : ℝ)|^4315 ≤ (44025988458921/100000000000000 : ℝ)^3291
        have hw : |(5348858537/10000000000 : ℝ)|=(5348858537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26477407/125000000 : ℝ)|^4315 ≤ (1633610445423/12500000000000 : ℝ)^3291
        have hw : |(-26477407/125000000 : ℝ)|=(26477407/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524468089/1000000000 : ℝ)|^4315 ≤ (10726281990149/25000000000000 : ℝ)^3291
        have hw : |(524468089/1000000000 : ℝ)|=(524468089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s5_2 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674429289/5000000000 : ℝ)*x 0 + (5244680891/10000000000 : ℝ)*x 1 + (-264774063/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674429289/5000000000 : ℝ)^4315 ≤ (2751624306337/6250000000000 : ℝ)^3291 := by
    have hnat : (2674429289 : ℕ)^4315*6250000000000^3291 ≤ 2751624306337^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674429289 5000000000 2751624306337 6250000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244680891/10000000000 : ℝ)^4315 ≤ (21452563985661/50000000000000 : ℝ)^3291 := by
    have hnat : (5244680891 : ℕ)^4315*50000000000000^3291 ≤ 21452563985661^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244680891 10000000000 21452563985661 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264774063/1250000000 : ℝ)^4315 ≤ (408402597199/3125000000000 : ℝ)^3291 := by
    have hnat : (264774063 : ℕ)^4315*3125000000000^3291 ≤ 408402597199^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264774063 1250000000 408402597199 3125000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674429289/5000000000 : ℝ), (5244680891/10000000000 : ℝ), (-264774063/1250000000 : ℝ)] ![(2751624306337/6250000000000 : ℝ), (21452563985661/50000000000000 : ℝ), (408402597199/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674429289/5000000000 : ℝ)|^4315 ≤ (2751624306337/6250000000000 : ℝ)^3291
        have hw : |(2674429289/5000000000 : ℝ)|=(2674429289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244680891/10000000000 : ℝ)|^4315 ≤ (21452563985661/50000000000000 : ℝ)^3291
        have hw : |(5244680891/10000000000 : ℝ)|=(5244680891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-264774063/1250000000 : ℝ)|^4315 ≤ (408402597199/3125000000000 : ℝ)^3291
        have hw : |(-264774063/1250000000 : ℝ)|=(264774063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s5_3 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4323207667/10000000000 : ℝ)*x 0 + (4150065057/10000000000 : ℝ)*x 1 + (2251522437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323207667/10000000000 : ℝ)^4315 ≤ (33303246565113/100000000000000 : ℝ)^3291 := by
    have hnat : (4323207667 : ℕ)^4315*100000000000000^3291 ≤ 33303246565113^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323207667 10000000000 33303246565113 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4150065057/10000000000 : ℝ)^4315 ≤ (31565455996689/100000000000000 : ℝ)^3291 := by
    have hnat : (4150065057 : ℕ)^4315*100000000000000^3291 ≤ 31565455996689^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150065057 10000000000 31565455996689 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251522437/5000000000 : ℝ)^4315 ≤ (17565648715501/50000000000000 : ℝ)^3291 := by
    have hnat : (2251522437 : ℕ)^4315*50000000000000^3291 ≤ 17565648715501^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251522437 5000000000 17565648715501 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323207667/10000000000 : ℝ), (4150065057/10000000000 : ℝ), (2251522437/5000000000 : ℝ)] ![(33303246565113/100000000000000 : ℝ), (31565455996689/100000000000000 : ℝ), (17565648715501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323207667/10000000000 : ℝ)|^4315 ≤ (33303246565113/100000000000000 : ℝ)^3291
        have hw : |(4323207667/10000000000 : ℝ)|=(4323207667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4150065057/10000000000 : ℝ)|^4315 ≤ (31565455996689/100000000000000 : ℝ)^3291
        have hw : |(4150065057/10000000000 : ℝ)|=(4150065057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251522437/5000000000 : ℝ)|^4315 ≤ (17565648715501/50000000000000 : ℝ)^3291
        have hw : |(2251522437/5000000000 : ℝ)|=(2251522437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s5_4 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1016382031/5000000000 : ℝ)*x 0 + (262264213/500000000 : ℝ)*x 1 + (2705887481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1016382031/5000000000 : ℝ)^4315 ≤ (12382179947429/100000000000000 : ℝ)^3291 := by
    have hnat : (1016382031 : ℕ)^4315*100000000000000^3291 ≤ 12382179947429^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016382031 5000000000 12382179947429 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262264213/500000000 : ℝ)^4315 ≤ (42911599901397/100000000000000 : ℝ)^3291 := by
    have hnat : (262264213 : ℕ)^4315*100000000000000^3291 ≤ 42911599901397^3291*500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262264213 500000000 42911599901397 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705887481/5000000000 : ℝ)^4315 ≤ (1117655503227/2500000000000 : ℝ)^3291 := by
    have hnat : (2705887481 : ℕ)^4315*2500000000000^3291 ≤ 1117655503227^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705887481 5000000000 1117655503227 2500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1016382031/5000000000 : ℝ), (262264213/500000000 : ℝ), (2705887481/5000000000 : ℝ)] ![(12382179947429/100000000000000 : ℝ), (42911599901397/100000000000000 : ℝ), (1117655503227/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1016382031/5000000000 : ℝ)|^4315 ≤ (12382179947429/100000000000000 : ℝ)^3291
        have hw : |(-1016382031/5000000000 : ℝ)|=(1016382031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262264213/500000000 : ℝ)|^4315 ≤ (42911599901397/100000000000000 : ℝ)^3291
        have hw : |(262264213/500000000 : ℝ)|=(262264213/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705887481/5000000000 : ℝ)|^4315 ≤ (1117655503227/2500000000000 : ℝ)^3291
        have hw : |(2705887481/5000000000 : ℝ)|=(2705887481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s5_5 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061119733/2000000000 : ℝ)*x 0 + (-1951098409/10000000000 : ℝ)*x 1 + (1352943743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061119733/2000000000 : ℝ)^4315 ≤ (10889929382899/25000000000000 : ℝ)^3291 := by
    have hnat : (1061119733 : ℕ)^4315*25000000000000^3291 ≤ 10889929382899^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061119733 2000000000 10889929382899 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1951098409/10000000000 : ℝ)^4315 ≤ (11734062207053/100000000000000 : ℝ)^3291 := by
    have hnat : (1951098409 : ℕ)^4315*100000000000000^3291 ≤ 11734062207053^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951098409 10000000000 11734062207053 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352943743/2500000000 : ℝ)^4315 ≤ (44706220237393/100000000000000 : ℝ)^3291 := by
    have hnat : (1352943743 : ℕ)^4315*100000000000000^3291 ≤ 44706220237393^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352943743 2500000000 44706220237393 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061119733/2000000000 : ℝ), (-1951098409/10000000000 : ℝ), (1352943743/2500000000 : ℝ)] ![(10889929382899/25000000000000 : ℝ), (11734062207053/100000000000000 : ℝ), (44706220237393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061119733/2000000000 : ℝ)|^4315 ≤ (10889929382899/25000000000000 : ℝ)^3291
        have hw : |(1061119733/2000000000 : ℝ)|=(1061119733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1951098409/10000000000 : ℝ)|^4315 ≤ (11734062207053/100000000000000 : ℝ)^3291
        have hw : |(-1951098409/10000000000 : ℝ)|=(1951098409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352943743/2500000000 : ℝ)|^4315 ≤ (44706220237393/100000000000000 : ℝ)^3291
        have hw : |(1352943743/2500000000 : ℝ)|=(1352943743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s5_6 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305598689/10000000000 : ℝ)*x 0 + (2705887469/5000000000 : ℝ)*x 1 + (-243887303/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305598689/10000000000 : ℝ)^4315 ≤ (871194355799/2000000000000 : ℝ)^3291 := by
    have hnat : (5305598689 : ℕ)^4315*2000000000000^3291 ≤ 871194355799^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305598689 10000000000 871194355799 2000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705887469/5000000000 : ℝ)^4315 ≤ (5588277483641/12500000000000 : ℝ)^3291 := by
    have hnat : (2705887469 : ℕ)^4315*12500000000000^3291 ≤ 5588277483641^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705887469 5000000000 5588277483641 12500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243887303/1250000000 : ℝ)^4315 ≤ (11734062325333/100000000000000 : ℝ)^3291 := by
    have hnat : (243887303 : ℕ)^4315*100000000000000^3291 ≤ 11734062325333^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243887303 1250000000 11734062325333 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305598689/10000000000 : ℝ), (2705887469/5000000000 : ℝ), (-243887303/1250000000 : ℝ)] ![(871194355799/2000000000000 : ℝ), (5588277483641/12500000000000 : ℝ), (11734062325333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305598689/10000000000 : ℝ)|^4315 ≤ (871194355799/2000000000000 : ℝ)^3291
        have hw : |(5305598689/10000000000 : ℝ)|=(5305598689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705887469/5000000000 : ℝ)|^4315 ≤ (5588277483641/12500000000000 : ℝ)^3291
        have hw : |(2705887469/5000000000 : ℝ)|=(2705887469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-243887303/1250000000 : ℝ)|^4315 ≤ (11734062325333/100000000000000 : ℝ)^3291
        have hw : |(-243887303/1250000000 : ℝ)|=(243887303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_s5_7 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4323233259/10000000000 : ℝ)*x 0 + (2250887451/5000000000 : ℝ)*x 1 + (207567083/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323233259/10000000000 : ℝ)^4315 ≤ (4162938131463/12500000000000 : ℝ)^3291 := by
    have hnat : (4323233259 : ℕ)^4315*12500000000000^3291 ≤ 4162938131463^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323233259 10000000000 4162938131463 12500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250887451/5000000000 : ℝ)^4315 ≤ (1097447100891/3125000000000 : ℝ)^3291 := by
    have hnat : (2250887451 : ℕ)^4315*3125000000000^3291 ≤ 1097447100891^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250887451 5000000000 1097447100891 3125000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207567083/500000000 : ℝ)^4315 ≤ (15789093853129/50000000000000 : ℝ)^3291 := by
    have hnat : (207567083 : ℕ)^4315*50000000000000^3291 ≤ 15789093853129^3291*500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207567083 500000000 15789093853129 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323233259/10000000000 : ℝ), (2250887451/5000000000 : ℝ), (207567083/500000000 : ℝ)] ![(4162938131463/12500000000000 : ℝ), (1097447100891/3125000000000 : ℝ), (15789093853129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323233259/10000000000 : ℝ)|^4315 ≤ (4162938131463/12500000000000 : ℝ)^3291
        have hw : |(4323233259/10000000000 : ℝ)|=(4323233259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250887451/5000000000 : ℝ)|^4315 ≤ (1097447100891/3125000000000 : ℝ)^3291
        have hw : |(2250887451/5000000000 : ℝ)|=(2250887451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207567083/500000000 : ℝ)|^4315 ≤ (15789093853129/50000000000000 : ℝ)^3291
        have hw : |(207567083/500000000 : ℝ)|=(207567083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1355_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2793/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14723/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11133/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11133/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11133/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11133/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11133/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11133/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11133/100000 : ℝ) ^ (2157/512 : ℝ) ≤ (4813395171021169/50000000000000000000 : ℝ) := by
    have hpowers : (11133/100000 : ℝ)^2157 ≤ (4813395171021169/50000000000000000000 : ℝ)^512 := by
      have hnat : (11133 : ℕ)^2157*50000000000000000000^512 ≤ 4813395171021169^512*100000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11133 100000 4813395171021169 50000000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11133/100000 : ℝ)) (X := (4813395171021169/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3691/25000 : ℝ) ^ (2157/512 : ℝ) ≤ (31618952211046269/100000000000000000000 : ℝ) := by
    have hpowers : (3691/25000 : ℝ)^2157 ≤ (31618952211046269/100000000000000000000 : ℝ)^512 := by
      have hnat : (3691 : ℕ)^2157*100000000000000000000^512 ≤ 31618952211046269^512*25000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 25000 31618952211046269 100000000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/25000 : ℝ)) (X := (31618952211046269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004813395171021169/25000000000000000000 : ℝ) ≤ (2500114245591777/2500000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (25004813395171021169/25000000000000000000 : ℝ)^512 ≤ (2500114245591777/2500000000000000 : ℝ)^2157 := by
      have hnat : (25004813395171021169 : ℕ)^512*2500000000000000^2157 ≤ 2500114245591777^2157*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004813395171021169 25000000000000000000 2500114245591777 2500000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500114245591777/2500000000000000 : ℝ)) (X := (25004813395171021169/25000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041245742553088607/100000000000000000000 : ℝ) ≤ (10000978882691097/10000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (100041245742553088607/100000000000000000000 : ℝ)^512 ≤ (10000978882691097/10000000000000000 : ℝ)^2157 := by
      have hnat : (100041245742553088607 : ℕ)^512*10000000000000000^2157 ≤ 10000978882691097^2157*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041245742553088607 100000000000000000000 10000978882691097 10000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000978882691097/10000000000000000 : ℝ)) (X := (100041245742553088607/100000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031618952211046269/50000000000000000000 : ℝ) ≤ (5000750391507543/5000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (50031618952211046269/50000000000000000000 : ℝ)^512 ≤ (5000750391507543/5000000000000000 : ℝ)^2157 := by
      have hnat : (50031618952211046269 : ℕ)^512*5000000000000000^2157 ≤ 5000750391507543^2157*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031618952211046269 50000000000000000000 5000750391507543 5000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000750391507543/5000000000000000 : ℝ)) (X := (50031618952211046269/50000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4813395171021169/50000000000000000000 : ℝ) ≤ ((18150019335180515037/18155000000000000000 : ℝ)+2*(521900323989/363100000000000 : ℝ)*(11133/100000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (18150019335180515037/18155000000000000000 : ℝ)+2*(521900323989/363100000000000 : ℝ)*(11133/100000 : ℝ)=(2500114245591777/2500000000000000 : ℝ) by norm_num, show 1+2*(4813395171021169/50000000000000000000 : ℝ)=(25004813395171021169/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31618952211046269/100000000000000000000 : ℝ)+(4813395171021169/50000000000000000000 : ℝ) ≤ ((18150019335180515037/18155000000000000000 : ℝ)+(521900323989/363100000000000 : ℝ)*((3691/25000 : ℝ)+(11133/100000 : ℝ)))^(2157/512 : ℝ) := by
    rw [show (18150019335180515037/18155000000000000000 : ℝ)+(521900323989/363100000000000 : ℝ)*((3691/25000 : ℝ)+(11133/100000 : ℝ))=(10000978882691097/10000000000000000 : ℝ) by norm_num, show 1+(31618952211046269/100000000000000000000 : ℝ)+(4813395171021169/50000000000000000000 : ℝ)=(100041245742553088607/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31618952211046269/100000000000000000000 : ℝ) ≤ ((18150019335180515037/18155000000000000000 : ℝ)+2*(521900323989/363100000000000 : ℝ)*(3691/25000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (18150019335180515037/18155000000000000000 : ℝ)+2*(521900323989/363100000000000 : ℝ)*(3691/25000 : ℝ)=(5000750391507543/5000000000000000 : ℝ) by norm_num, show 1+2*(31618952211046269/100000000000000000000 : ℝ)=(50031618952211046269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18150019335180515037/18155000000000000000 : ℝ)*(X 1 0+X 2 0)+(521900323989/363100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (11133/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (18150019335180515037/18155000000000000000 : ℝ)) (alpha := (521900323989/363100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18150019335180515037/18155000000000000000 : ℝ)*(X 0 1+X 2 1)+(521900323989/363100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (11133/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (18150019335180515037/18155000000000000000 : ℝ)) (alpha := (521900323989/363100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18150019335180515037/18155000000000000000 : ℝ)*(X 0 2+X 1 2)+(521900323989/363100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (11133/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (18150019335180515037/18155000000000000000 : ℝ)) (alpha := (521900323989/363100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-101637597/500000000 : ℝ)*X 0 0+(2706190719/5000000000 : ℝ)*X 0 1+(5244680863/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348858537/10000000000 : ℝ)*X 1 0+(-26477407/125000000 : ℝ)*X 1 1+(524468089/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674429289/5000000000 : ℝ)*X 2 0+(5244680891/10000000000 : ℝ)*X 2 1+(-264774063/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323207667/10000000000 : ℝ)*X 0 0+(4150065057/10000000000 : ℝ)*X 0 1+(2251522437/5000000000 : ℝ)*X 0 2+(4323207667/10000000000 : ℝ)*X 1 0+(4150065057/10000000000 : ℝ)*X 1 1+(2251522437/5000000000 : ℝ)*X 1 2+(4323207667/10000000000 : ℝ)*X 2 0+(4150065057/10000000000 : ℝ)*X 2 1+(2251522437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1016382031/5000000000 : ℝ)*X 0 0+(262264213/500000000 : ℝ)*X 0 1+(2705887481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061119733/2000000000 : ℝ)*X 1 0+(-1951098409/10000000000 : ℝ)*X 1 1+(1352943743/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305598689/10000000000 : ℝ)*X 2 0+(2705887469/5000000000 : ℝ)*X 2 1+(-243887303/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4323233259/10000000000 : ℝ)*X 0 0+(2250887451/5000000000 : ℝ)*X 0 1+(207567083/500000000 : ℝ)*X 0 2+(4323233259/10000000000 : ℝ)*X 1 0+(2250887451/5000000000 : ℝ)*X 1 1+(207567083/500000000 : ℝ)*X 1 2+(4323233259/10000000000 : ℝ)*X 2 0+(2250887451/5000000000 : ℝ)*X 2 1+(207567083/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1621808624853878031183350199/181550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1659308467/100000000000000 : ℝ)*(base19) + (82910797/5000000000000 : ℝ)*(base23) + (6258249/25000000000000 : ℝ)*(lower2) + (9727399/5000000000000 : ℝ)*(upper3) + (59203397/25000000000000 : ℝ)*(upper5) + (879613590952209/20000000000000 : ℝ)*(major0) + (879613590952209/20000000000000 : ℝ)*(major1) + (879613590952209/20000000000000 : ℝ)*(major2) + (745380317066993/12500000000000 : ℝ)*(sp0) + (2981538709949001/50000000000000 : ℝ)*(sp1) + (596307742099053/10000000000000 : ℝ)*(sp2) + (1416519960078601/50000000000000 : ℝ)*(sp3) + (1461706821/4000000000000 : ℝ)*(sp4) + (16612387619/100000000000000 : ℝ)*(sp7) + (141652826627241/5000000000000 : ℝ)*(f.failure) + (5963079079206469/100000000000000 : ℝ)*(f.sum) + (179842044397/1815500000000000000000000000 : ℝ)*base66 + (172984035563516733/363100000000000000000000000000000 : ℝ)*base67 + (2489756070553083267/363100000000000000000000000000000 : ℝ)*base70 + (4014923604981983267/363100000000000000000000000000000 : ℝ)*base72 + (583642669191/3631000000000000000000000000 : ℝ)*base74 + (698353772687116733/363100000000000000000000000000000 : ℝ)*base75 + (1102978982866583267/363100000000000000000000000000000 : ℝ)*base78 + (4078596803916283267/363100000000000000000000000000000 : ℝ)*base80 + (15037343735107/3631000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (979173/250000000000000000000 : ℝ)*base90 + (979173/250000000000000000000 : ℝ)*base92 + (979173/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4719853828002393978266958873/453875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1845662599/100000000000000 : ℝ)*(base19) + (1992964663/100000000000000 : ℝ)*(base23) + (215210757/100000000000000 : ℝ)*(upper3) + (56782783/100000000000000 : ℝ)*(lower4) + (223245961/100000000000000 : ℝ)*(upper5) + (2214987790103143/50000000000000 : ℝ)*(major0) + (2214987790103143/50000000000000 : ℝ)*(major1) + (2214987790103143/50000000000000 : ℝ)*(major2) + (38159766587/100000000000000 : ℝ)*(sp1) + (19883688267/50000000000000 : ℝ)*(sp2) + (187698146450627/3125000000000 : ℝ)*(sp4) + (6006300680990879/100000000000000 : ℝ)*(sp5) + (1501574731519717/25000000000000 : ℝ)*(sp6) + (1426805063679301/50000000000000 : ℝ)*(sp7) + (1426805063679301/50000000000000 : ℝ)*(f.failure) + (187698146450627/3125000000000 : ℝ)*(f.sum) + (2525688329349/4538750000000000000000000000 : ℝ)*base66 + (6969710894877188709/907750000000000000000000000000000 : ℝ)*base68 + (4236374581881811291/907750000000000000000000000000000 : ℝ)*base69 + (4644077206294188709/907750000000000000000000000000000 : ℝ)*base72 + (102798530948961/18155000000000000000000000000 : ℝ)*base74 + (358896698805688709/907750000000000000000000000000000 : ℝ)*base76 + (5652889691656688709/907750000000000000000000000000000 : ℝ)*base78 + (3852457973553311291/907750000000000000000000000000000 : ℝ)*base79 + (40199004617353/9077500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (26197647/2500000000000000000000 : ℝ)*base89 + (26197647/2500000000000000000000 : ℝ)*base91 + (26197647/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1355_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1355_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1355_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (621/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1355_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1355_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1355_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (621/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1355_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1636_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:01:40.340986+00:00
-- url     : https://prove2.me/submissions/a7f2f656-eed2-443e-8d14-95102e2271c7

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
theorem support_rectangle_w1636_s3_0 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-410227677/2500000000 : ℝ)*x 0 + (5451838453/10000000000 : ℝ)*x 1 + (5182805397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410227677/2500000000 : ℝ)^4863 ≤ (1013257312469/10000000000000 : ℝ)^3839 := by
    have hnat : (410227677 : ℕ)^4863*10000000000000^3839 ≤ 1013257312469^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410227677 2500000000 1013257312469 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451838453/10000000000 : ℝ)^4863 ≤ (927469139843/2000000000000 : ℝ)^3839 := by
    have hnat : (5451838453 : ℕ)^4863*2000000000000^3839 ≤ 927469139843^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451838453 10000000000 927469139843 2000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182805397/10000000000 : ℝ)^4863 ≤ (8698793973343/20000000000000 : ℝ)^3839 := by
    have hnat : (5182805397 : ℕ)^4863*20000000000000^3839 ≤ 8698793973343^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182805397 10000000000 8698793973343 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410227677/2500000000 : ℝ), (5451838453/10000000000 : ℝ), (5182805397/10000000000 : ℝ)] ![(1013257312469/10000000000000 : ℝ), (927469139843/2000000000000 : ℝ), (8698793973343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410227677/2500000000 : ℝ)|^4863 ≤ (1013257312469/10000000000000 : ℝ)^3839
        have hw : |(-410227677/2500000000 : ℝ)|=(410227677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451838453/10000000000 : ℝ)|^4863 ≤ (927469139843/2000000000000 : ℝ)^3839
        have hw : |(5451838453/10000000000 : ℝ)|=(5451838453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182805397/10000000000 : ℝ)|^4863 ≤ (8698793973343/20000000000000 : ℝ)^3839
        have hw : |(5182805397/10000000000 : ℝ)|=(5182805397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s3_1 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674935539/5000000000 : ℝ)*x 0 + (-111218063/625000000 : ℝ)*x 1 + (5182805441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674935539/5000000000 : ℝ)^4863 ≤ (45277523454073/100000000000000 : ℝ)^3839 := by
    have hnat : (2674935539 : ℕ)^4863*100000000000000^3839 ≤ 45277523454073^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674935539 5000000000 45277523454073 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111218063/625000000 : ℝ)^4863 ≤ (5614253092487/50000000000000 : ℝ)^3839 := by
    have hnat : (111218063 : ℕ)^4863*50000000000000^3839 ≤ 5614253092487^3839*625000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111218063 625000000 5614253092487 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182805441/10000000000 : ℝ)^4863 ≤ (43493970334453/100000000000000 : ℝ)^3839 := by
    have hnat : (5182805441 : ℕ)^4863*100000000000000^3839 ≤ 43493970334453^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182805441 10000000000 43493970334453 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674935539/5000000000 : ℝ), (-111218063/625000000 : ℝ), (5182805441/10000000000 : ℝ)] ![(45277523454073/100000000000000 : ℝ), (5614253092487/50000000000000 : ℝ), (43493970334453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674935539/5000000000 : ℝ)|^4863 ≤ (45277523454073/100000000000000 : ℝ)^3839
        have hw : |(2674935539/5000000000 : ℝ)|=(2674935539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111218063/625000000 : ℝ)|^4863 ≤ (5614253092487/50000000000000 : ℝ)^3839
        have hw : |(-111218063/625000000 : ℝ)|=(111218063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182805441/10000000000 : ℝ)|^4863 ≤ (43493970334453/100000000000000 : ℝ)^3839
        have hw : |(5182805441/10000000000 : ℝ)|=(5182805441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s3_2 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349870711/10000000000 : ℝ)*x 0 + (2591402911/5000000000 : ℝ)*x 1 + (-355897799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349870711/10000000000 : ℝ)^4863 ≤ (9055503903911/20000000000000 : ℝ)^3839 := by
    have hnat : (5349870711 : ℕ)^4863*20000000000000^3839 ≤ 9055503903911^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349870711 10000000000 9055503903911 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591402911/5000000000 : ℝ)^4863 ≤ (21746987192321/50000000000000 : ℝ)^3839 := by
    have hnat : (2591402911 : ℕ)^4863*50000000000000^3839 ≤ 21746987192321^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591402911 5000000000 21746987192321 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355897799/2000000000 : ℝ)^4863 ≤ (1403563260133/12500000000000 : ℝ)^3839 := by
    have hnat : (355897799 : ℕ)^4863*12500000000000^3839 ≤ 1403563260133^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355897799 2000000000 1403563260133 12500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349870711/10000000000 : ℝ), (2591402911/5000000000 : ℝ), (-355897799/2000000000 : ℝ)] ![(9055503903911/20000000000000 : ℝ), (21746987192321/50000000000000 : ℝ), (1403563260133/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349870711/10000000000 : ℝ)|^4863 ≤ (9055503903911/20000000000000 : ℝ)^3839
        have hw : |(5349870711/10000000000 : ℝ)|=(5349870711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591402911/5000000000 : ℝ)|^4863 ≤ (21746987192321/50000000000000 : ℝ)^3839
        have hw : |(2591402911/5000000000 : ℝ)|=(2591402911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355897799/2000000000 : ℝ)|^4863 ≤ (1403563260133/12500000000000 : ℝ)^3839
        have hw : |(-355897799/2000000000 : ℝ)|=(355897799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s3_3 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209578797/500000000 : ℝ)*x 0 + (241250223/625000000 : ℝ)*x 1 + (227189857/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209578797/500000000 : ℝ)^4863 ≤ (16619644743357/50000000000000 : ℝ)^3839 := by
    have hnat : (209578797 : ℕ)^4863*50000000000000^3839 ≤ 16619644743357^3839*500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209578797 500000000 16619644743357 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241250223/625000000 : ℝ)^4863 ≤ (29944406590703/100000000000000 : ℝ)^3839 := by
    have hnat : (241250223 : ℕ)^4863*100000000000000^3839 ≤ 29944406590703^3839*625000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241250223 625000000 29944406590703 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227189857/500000000 : ℝ)^4863 ≤ (9204075977279/25000000000000 : ℝ)^3839 := by
    have hnat : (227189857 : ℕ)^4863*25000000000000^3839 ≤ 9204075977279^3839*500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227189857 500000000 9204075977279 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209578797/500000000 : ℝ), (241250223/625000000 : ℝ), (227189857/500000000 : ℝ)] ![(16619644743357/50000000000000 : ℝ), (29944406590703/100000000000000 : ℝ), (9204075977279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209578797/500000000 : ℝ)|^4863 ≤ (16619644743357/50000000000000 : ℝ)^3839
        have hw : |(209578797/500000000 : ℝ)|=(209578797/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241250223/625000000 : ℝ)|^4863 ≤ (29944406590703/100000000000000 : ℝ)^3839
        have hw : |(241250223/625000000 : ℝ)|=(241250223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227189857/500000000 : ℝ)|^4863 ≤ (9204075977279/25000000000000 : ℝ)^3839
        have hw : |(227189857/500000000 : ℝ)|=(227189857/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s3_4 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-820488757/5000000000 : ℝ)*x 0 + (5184831429/10000000000 : ℝ)*x 1 + (5449790881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (820488757/5000000000 : ℝ)^4863 ≤ (5066547843921/50000000000000 : ℝ)^3839 := by
    have hnat : (820488757 : ℕ)^4863*50000000000000^3839 ≤ 5066547843921^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820488757 5000000000 5066547843921 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184831429/10000000000 : ℝ)^4863 ≤ (43515508554663/100000000000000 : ℝ)^3839 := by
    have hnat : (5184831429 : ℕ)^4863*100000000000000^3839 ≤ 43515508554663^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184831429 10000000000 43515508554663 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449790881/10000000000 : ℝ)^4863 ≤ (362120279251/781250000000 : ℝ)^3839 := by
    have hnat : (5449790881 : ℕ)^4863*781250000000^3839 ≤ 362120279251^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449790881 10000000000 362120279251 781250000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-820488757/5000000000 : ℝ), (5184831429/10000000000 : ℝ), (5449790881/10000000000 : ℝ)] ![(5066547843921/50000000000000 : ℝ), (43515508554663/100000000000000 : ℝ), (362120279251/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-820488757/5000000000 : ℝ)|^4863 ≤ (5066547843921/50000000000000 : ℝ)^3839
        have hw : |(-820488757/5000000000 : ℝ)|=(820488757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184831429/10000000000 : ℝ)|^4863 ≤ (43515508554663/100000000000000 : ℝ)^3839
        have hw : |(5184831429/10000000000 : ℝ)|=(5184831429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449790881/10000000000 : ℝ)|^4863 ≤ (362120279251/781250000000 : ℝ)^3839
        have hw : |(5449790881/10000000000 : ℝ)|=(5449790881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s3_5 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639063253/5000000000 : ℝ)*x 0 + (-1512503711/10000000000 : ℝ)*x 1 + (1089958183/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639063253/5000000000 : ℝ)^4863 ≤ (22254873718327/50000000000000 : ℝ)^3839 := by
    have hnat : (2639063253 : ℕ)^4863*50000000000000^3839 ≤ 22254873718327^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639063253 5000000000 22254873718327 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512503711/10000000000 : ℝ)^4863 ≤ (2284714108621/25000000000000 : ℝ)^3839 := by
    have hnat : (1512503711 : ℕ)^4863*25000000000000^3839 ≤ 2284714108621^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512503711 10000000000 2284714108621 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089958183/2000000000 : ℝ)^4863 ≤ (23175698055219/50000000000000 : ℝ)^3839 := by
    have hnat : (1089958183 : ℕ)^4863*50000000000000^3839 ≤ 23175698055219^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089958183 2000000000 23175698055219 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639063253/5000000000 : ℝ), (-1512503711/10000000000 : ℝ), (1089958183/2000000000 : ℝ)] ![(22254873718327/50000000000000 : ℝ), (2284714108621/25000000000000 : ℝ), (23175698055219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639063253/5000000000 : ℝ)|^4863 ≤ (22254873718327/50000000000000 : ℝ)^3839
        have hw : |(2639063253/5000000000 : ℝ)|=(2639063253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1512503711/10000000000 : ℝ)|^4863 ≤ (2284714108621/25000000000000 : ℝ)^3839
        have hw : |(-1512503711/10000000000 : ℝ)|=(1512503711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089958183/2000000000 : ℝ)|^4863 ≤ (23175698055219/50000000000000 : ℝ)^3839
        have hw : |(1089958183/2000000000 : ℝ)|=(1089958183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s3_6 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319531643/2500000000 : ℝ)*x 0 + (5449790971/10000000000 : ℝ)*x 1 + (-75625177/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319531643/2500000000 : ℝ)^4863 ≤ (44509748141681/100000000000000 : ℝ)^3839 := by
    have hnat : (1319531643 : ℕ)^4863*100000000000000^3839 ≤ 44509748141681^3839*2500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319531643 2500000000 44509748141681 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5449790971/10000000000 : ℝ)^4863 ≤ (46351396713771/100000000000000 : ℝ)^3839 := by
    have hnat : (5449790971 : ℕ)^4863*100000000000000^3839 ≤ 46351396713771^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449790971 10000000000 46351396713771 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75625177/500000000 : ℝ)^4863 ≤ (9138855125671/100000000000000 : ℝ)^3839 := by
    have hnat : (75625177 : ℕ)^4863*100000000000000^3839 ≤ 9138855125671^3839*500000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75625177 500000000 9138855125671 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319531643/2500000000 : ℝ), (5449790971/10000000000 : ℝ), (-75625177/500000000 : ℝ)] ![(44509748141681/100000000000000 : ℝ), (46351396713771/100000000000000 : ℝ), (9138855125671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319531643/2500000000 : ℝ)|^4863 ≤ (44509748141681/100000000000000 : ℝ)^3839
        have hw : |(1319531643/2500000000 : ℝ)|=(1319531643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5449790971/10000000000 : ℝ)|^4863 ≤ (46351396713771/100000000000000 : ℝ)^3839
        have hw : |(5449790971/10000000000 : ℝ)|=(5449790971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75625177/500000000 : ℝ)|^4863 ≤ (9138855125671/100000000000000 : ℝ)^3839
        have hw : |(-75625177/500000000 : ℝ)|=(75625177/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s3_7 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4191745671/10000000000 : ℝ)*x 0 + (283665493/625000000 : ℝ)*x 1 + (3865206521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191745671/10000000000 : ℝ)^4863 ≤ (8310248621367/25000000000000 : ℝ)^3839 := by
    have hnat : (4191745671 : ℕ)^4863*25000000000000^3839 ≤ 8310248621367^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191745671 10000000000 8310248621367 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283665493/625000000 : ℝ)^4863 ≤ (36763461100289/100000000000000 : ℝ)^3839 := by
    have hnat : (283665493 : ℕ)^4863*100000000000000^3839 ≤ 36763461100289^3839*625000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283665493 625000000 36763461100289 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3865206521/10000000000 : ℝ)^4863 ≤ (1199821775933/4000000000000 : ℝ)^3839 := by
    have hnat : (3865206521 : ℕ)^4863*4000000000000^3839 ≤ 1199821775933^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865206521 10000000000 1199821775933 4000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191745671/10000000000 : ℝ), (283665493/625000000 : ℝ), (3865206521/10000000000 : ℝ)] ![(8310248621367/25000000000000 : ℝ), (36763461100289/100000000000000 : ℝ), (1199821775933/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191745671/10000000000 : ℝ)|^4863 ≤ (8310248621367/25000000000000 : ℝ)^3839
        have hw : |(4191745671/10000000000 : ℝ)|=(4191745671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283665493/625000000 : ℝ)|^4863 ≤ (36763461100289/100000000000000 : ℝ)^3839
        have hw : |(283665493/625000000 : ℝ)|=(283665493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3865206521/10000000000 : ℝ)|^4863 ≤ (1199821775933/4000000000000 : ℝ)^3839
        have hw : |(3865206521/10000000000 : ℝ)|=(3865206521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1636_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2647/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16301/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16393/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5253/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16393/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5253/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16393/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5253/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16393/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5253/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16393/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5253/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16393/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5253/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5253/50000 : ℝ) ^ (4859/1024 : ℝ) ≤ (284129144661479/12500000000000000000 : ℝ) := by
    have hpowers : (5253/50000 : ℝ)^4859 ≤ (284129144661479/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5253 : ℕ)^4859*12500000000000000000^1024 ≤ 284129144661479^1024*50000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5253 50000 284129144661479 12500000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5253/50000 : ℝ)) (X := (284129144661479/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16393/100000 : ℝ) ^ (4859/1024 : ℝ) ≤ (18769913027381863/100000000000000000000 : ℝ) := by
    have hpowers : (16393/100000 : ℝ)^4859 ≤ (18769913027381863/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16393 : ℕ)^4859*100000000000000000000^1024 ≤ 18769913027381863^1024*100000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16393 100000 18769913027381863 100000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16393/100000 : ℝ)) (X := (18769913027381863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250284129144661479/6250000000000000000 : ℝ) ≤ (2000019160684891/2000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (6250284129144661479/6250000000000000000 : ℝ)^1024 ≤ (2000019160684891/2000000000000000 : ℝ)^4859 := by
      have hnat : (6250284129144661479 : ℕ)^1024*2000000000000000^4859 ≤ 2000019160684891^4859*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250284129144661479 6250000000000000000 2000019160684891 2000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000019160684891/2000000000000000 : ℝ)) (X := (6250284129144661479/6250000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004208589236934739/20000000000000000000 : ℝ) ≤ (10000443428436757/10000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (20004208589236934739/20000000000000000000 : ℝ)^1024 ≤ (10000443428436757/10000000000000000 : ℝ)^4859 := by
      have hnat : (20004208589236934739 : ℕ)^1024*10000000000000000^4859 ≤ 10000443428436757^4859*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004208589236934739 20000000000000000000 10000443428436757 10000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000443428436757/10000000000000000 : ℝ)) (X := (20004208589236934739/20000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018769913027381863/50000000000000000000 : ℝ) ≤ (10000791053449059/10000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (50018769913027381863/50000000000000000000 : ℝ)^1024 ≤ (10000791053449059/10000000000000000 : ℝ)^4859 := by
      have hnat : (50018769913027381863 : ℕ)^1024*10000000000000000^4859 ≤ 10000791053449059^4859*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018769913027381863 50000000000000000000 10000791053449059 10000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000791053449059/10000000000000000 : ℝ)) (X := (50018769913027381863/50000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(284129144661479/12500000000000000000 : ℝ) ≤ ((58863259698001276961/58870000000000000000 : ℝ)+2*(173812506151/294350000000000 : ℝ)*(5253/50000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (58863259698001276961/58870000000000000000 : ℝ)+2*(173812506151/294350000000000 : ℝ)*(5253/50000 : ℝ)=(2000019160684891/2000000000000000 : ℝ) by norm_num, show 1+2*(284129144661479/12500000000000000000 : ℝ)=(6250284129144661479/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18769913027381863/100000000000000000000 : ℝ)+(284129144661479/12500000000000000000 : ℝ) ≤ ((58863259698001276961/58870000000000000000 : ℝ)+(173812506151/294350000000000 : ℝ)*((16393/100000 : ℝ)+(5253/50000 : ℝ)))^(4859/1024 : ℝ) := by
    rw [show (58863259698001276961/58870000000000000000 : ℝ)+(173812506151/294350000000000 : ℝ)*((16393/100000 : ℝ)+(5253/50000 : ℝ))=(10000443428436757/10000000000000000 : ℝ) by norm_num, show 1+(18769913027381863/100000000000000000000 : ℝ)+(284129144661479/12500000000000000000 : ℝ)=(20004208589236934739/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18769913027381863/100000000000000000000 : ℝ) ≤ ((58863259698001276961/58870000000000000000 : ℝ)+2*(173812506151/294350000000000 : ℝ)*(16393/100000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (58863259698001276961/58870000000000000000 : ℝ)+2*(173812506151/294350000000000 : ℝ)*(16393/100000 : ℝ)=(10000791053449059/10000000000000000 : ℝ) by norm_num, show 1+2*(18769913027381863/100000000000000000000 : ℝ)=(50018769913027381863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58863259698001276961/58870000000000000000 : ℝ)*(X 1 0+X 2 0)+(173812506151/294350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (5253/50000 : ℝ)) (hi := (16393/100000 : ℝ)) (c := (58863259698001276961/58870000000000000000 : ℝ)) (alpha := (173812506151/294350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58863259698001276961/58870000000000000000 : ℝ)*(X 0 1+X 2 1)+(173812506151/294350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (5253/50000 : ℝ)) (hi := (16393/100000 : ℝ)) (c := (58863259698001276961/58870000000000000000 : ℝ)) (alpha := (173812506151/294350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58863259698001276961/58870000000000000000 : ℝ)*(X 0 2+X 1 2)+(173812506151/294350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (5253/50000 : ℝ)) (hi := (16393/100000 : ℝ)) (c := (58863259698001276961/58870000000000000000 : ℝ)) (alpha := (173812506151/294350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-410227677/2500000000 : ℝ)*X 0 0+(5451838453/10000000000 : ℝ)*X 0 1+(5182805397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674935539/5000000000 : ℝ)*X 1 0+(-111218063/625000000 : ℝ)*X 1 1+(5182805441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349870711/10000000000 : ℝ)*X 2 0+(2591402911/5000000000 : ℝ)*X 2 1+(-355897799/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((209578797/500000000 : ℝ)*X 0 0+(241250223/625000000 : ℝ)*X 0 1+(227189857/500000000 : ℝ)*X 0 2+(209578797/500000000 : ℝ)*X 1 0+(241250223/625000000 : ℝ)*X 1 1+(227189857/500000000 : ℝ)*X 1 2+(209578797/500000000 : ℝ)*X 2 0+(241250223/625000000 : ℝ)*X 2 1+(227189857/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-820488757/5000000000 : ℝ)*X 0 0+(5184831429/10000000000 : ℝ)*X 0 1+(5449790881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639063253/5000000000 : ℝ)*X 1 0+(-1512503711/10000000000 : ℝ)*X 1 1+(1089958183/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319531643/2500000000 : ℝ)*X 2 0+(5449790971/10000000000 : ℝ)*X 2 1+(-75625177/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4191745671/10000000000 : ℝ)*X 0 0+(283665493/625000000 : ℝ)*X 0 1+(3865206521/10000000000 : ℝ)*X 0 2+(4191745671/10000000000 : ℝ)*X 1 0+(283665493/625000000 : ℝ)*X 1 1+(3865206521/10000000000 : ℝ)*X 1 2+(4191745671/10000000000 : ℝ)*X 2 0+(283665493/625000000 : ℝ)*X 2 1+(3865206521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18090457627982879674737/1839687500000000000000000000 : ℝ) := by norm_num
    linear_combination (1307738007/100000000000000 : ℝ)*(base19) + (456943067/50000000000000 : ℝ)*(base23) + (1857247/2500000000000 : ℝ)*(lower2) + (92612717/50000000000000 : ℝ)*(upper3) + (1842943/3125000000000 : ℝ)*(upper5) + (2589747440851899/100000000000000 : ℝ)*(major0) + (2589747440851899/100000000000000 : ℝ)*(major1) + (2589747440851899/100000000000000 : ℝ)*(major2) + (1858517633948869/50000000000000 : ℝ)*(sp0) + (929262807619587/25000000000000 : ℝ)*(sp1) + (1858525812165111/50000000000000 : ℝ)*(sp2) + (1462435340559827/100000000000000 : ℝ)*(sp3) + (17270318617/100000000000000 : ℝ)*(sp4) + (3337573127/50000000000000 : ℝ)*(sp7) + (9140262598163/625000000000 : ℝ)*(f.failure) + (929263134554089/25000000000000 : ℝ)*(f.sum) + (17616754910661/14717500000000000000000000000 : ℝ)*base66 + (458084588547628723/841000000000000000000000000000000 : ℝ)*base68 + (6982382537190371277/841000000000000000000000000000000 : ℝ)*base69 + (9072513713869371277/841000000000000000000000000000000 : ℝ)*base71 + (118627421699371/14717500000000000000000000000 : ℝ)*base74 + (423015970914628723/841000000000000000000000000000000 : ℝ)*base76 + (6045326898851371277/841000000000000000000000000000000 : ℝ)*base77 + (11110711568704628723/841000000000000000000000000000000 : ℝ)*base80 + (14404484690971/14717500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (358653/62500000000000000000 : ℝ)*base90 + (358653/62500000000000000000 : ℝ)*base92 + (358653/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47024152191997181042057301/20300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151595111/50000000000000 : ℝ)*(base19) + (450800697/100000000000000 : ℝ)*(base23) + (8623713/10000000000000 : ℝ)*(upper3) + (23369923/100000000000000 : ℝ)*(lower4) + (14515947/50000000000000 : ℝ)*(upper5) + (525907191131079/20000000000000 : ℝ)*(major0) + (525907191131079/20000000000000 : ℝ)*(major1) + (525907191131079/20000000000000 : ℝ)*(major2) + (604460867/25000000000000 : ℝ)*(sp1) + (130959849/2000000000000 : ℝ)*(sp2) + (235885066581759/6250000000000 : ℝ)*(sp4) + (1887079172137227/50000000000000 : ℝ)*(sp5) + (943538516628749/25000000000000 : ℝ)*(sp6) + (742455384393641/50000000000000 : ℝ)*(sp7) + (742455384393641/50000000000000 : ℝ)*(f.failure) + (235885066581759/6250000000000 : ℝ)*(f.sum) + (292873142087/45992187500000000000000000 : ℝ)*base65 + (212758658579824417/168200000000000000000000000000000 : ℝ)*base67 + (481595646269024417/168200000000000000000000000000000 : ℝ)*base69 + (602741416384224417/168200000000000000000000000000000 : ℝ)*base71 + (4197217057259/735875000000000000000000000 : ℝ)*base73 + (1409006725370224417/168200000000000000000000000000000 : ℝ)*base75 + (544256689585424417/168200000000000000000000000000000 : ℝ)*base77 + (1166774384811824417/168200000000000000000000000000000 : ℝ)*base79 + (9445923487687/2943500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (22087071/5000000000000000000000 : ℝ)*base90 + (22087071/5000000000000000000000 : ℝ)*base92 + (22087071/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1636_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16301/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1636_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1636_s4_0 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1640974711/10000000000 : ℝ)*x 0 + (2725759777/5000000000 : ℝ)*x 1 + (518308153/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1640974711/10000000000 : ℝ)^4863 ≤ (633317110149/6250000000000 : ℝ)^3839 := by
    have hnat : (1640974711 : ℕ)^4863*6250000000000^3839 ≤ 633317110149^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1640974711 10000000000 633317110149 6250000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725759777/5000000000 : ℝ)^4863 ≤ (11592505229711/25000000000000 : ℝ)^3839 := by
    have hnat : (2725759777 : ℕ)^4863*25000000000000^3839 ≤ 11592505229711^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725759777 5000000000 11592505229711 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518308153/1000000000 : ℝ)^4863 ≤ (43496905296533/100000000000000 : ℝ)^3839 := by
    have hnat : (518308153 : ℕ)^4863*100000000000000^3839 ≤ 43496905296533^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518308153 1000000000 43496905296533 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1640974711/10000000000 : ℝ), (2725759777/5000000000 : ℝ), (518308153/1000000000 : ℝ)] ![(633317110149/6250000000000 : ℝ), (11592505229711/25000000000000 : ℝ), (43496905296533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1640974711/10000000000 : ℝ)|^4863 ≤ (633317110149/6250000000000 : ℝ)^3839
        have hw : |(-1640974711/10000000000 : ℝ)|=(1640974711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725759777/5000000000 : ℝ)|^4863 ≤ (11592505229711/25000000000000 : ℝ)^3839
        have hw : |(2725759777/5000000000 : ℝ)|=(2725759777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518308153/1000000000 : ℝ)|^4863 ≤ (43496905296533/100000000000000 : ℝ)^3839
        have hw : |(518308153/1000000000 : ℝ)|=(518308153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s4_1 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349784799/10000000000 : ℝ)*x 0 + (-889618803/5000000000 : ℝ)*x 1 + (5183081479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349784799/10000000000 : ℝ)^4863 ≤ (45276598479757/100000000000000 : ℝ)^3839 := by
    have hnat : (5349784799 : ℕ)^4863*100000000000000^3839 ≤ 45276598479757^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349784799 10000000000 45276598479757 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (889618803/5000000000 : ℝ)^4863 ≤ (1122649675269/10000000000000 : ℝ)^3839 := by
    have hnat : (889618803 : ℕ)^4863*10000000000000^3839 ≤ 1122649675269^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889618803 5000000000 1122649675269 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183081479/10000000000 : ℝ)^4863 ≤ (21748452377187/50000000000000 : ℝ)^3839 := by
    have hnat : (5183081479 : ℕ)^4863*50000000000000^3839 ≤ 21748452377187^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183081479 10000000000 21748452377187 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349784799/10000000000 : ℝ), (-889618803/5000000000 : ℝ), (5183081479/10000000000 : ℝ)] ![(45276598479757/100000000000000 : ℝ), (1122649675269/10000000000000 : ℝ), (21748452377187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349784799/10000000000 : ℝ)|^4863 ≤ (45276598479757/100000000000000 : ℝ)^3839
        have hw : |(5349784799/10000000000 : ℝ)|=(5349784799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-889618803/5000000000 : ℝ)|^4863 ≤ (1122649675269/10000000000000 : ℝ)^3839
        have hw : |(-889618803/5000000000 : ℝ)|=(889618803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183081479/10000000000 : ℝ)|^4863 ≤ (21748452377187/50000000000000 : ℝ)^3839
        have hw : |(5183081479/10000000000 : ℝ)|=(5183081479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s4_2 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674892377/5000000000 : ℝ)*x 0 + (207323261/400000000 : ℝ)*x 1 + (-355847521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674892377/5000000000 : ℝ)^4863 ≤ (1811063919893/4000000000000 : ℝ)^3839 := by
    have hnat : (2674892377 : ℕ)^4863*4000000000000^3839 ≤ 1811063919893^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674892377 5000000000 1811063919893 4000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207323261/400000000 : ℝ)^4863 ≤ (43496905243381/100000000000000 : ℝ)^3839 := by
    have hnat : (207323261 : ℕ)^4863*100000000000000^3839 ≤ 43496905243381^3839*400000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207323261 400000000 43496905243381 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (355847521/2000000000 : ℝ)^4863 ≤ (5613248372349/50000000000000 : ℝ)^3839 := by
    have hnat : (355847521 : ℕ)^4863*50000000000000^3839 ≤ 5613248372349^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355847521 2000000000 5613248372349 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674892377/5000000000 : ℝ), (207323261/400000000 : ℝ), (-355847521/2000000000 : ℝ)] ![(1811063919893/4000000000000 : ℝ), (43496905243381/100000000000000 : ℝ), (5613248372349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674892377/5000000000 : ℝ)|^4863 ≤ (1811063919893/4000000000000 : ℝ)^3839
        have hw : |(2674892377/5000000000 : ℝ)|=(2674892377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207323261/400000000 : ℝ)|^4863 ≤ (43496905243381/100000000000000 : ℝ)^3839
        have hw : |(207323261/400000000 : ℝ)|=(207323261/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-355847521/2000000000 : ℝ)|^4863 ≤ (5613248372349/50000000000000 : ℝ)^3839
        have hw : |(-355847521/2000000000 : ℝ)|=(355847521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s4_3 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095808859/5000000000 : ℝ)*x 0 + (3860754629/10000000000 : ℝ)*x 1 + (567879641/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095808859/5000000000 : ℝ)^4863 ≤ (16619854578767/50000000000000 : ℝ)^3839 := by
    have hnat : (2095808859 : ℕ)^4863*50000000000000^3839 ≤ 16619854578767^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095808859 5000000000 16619854578767 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3860754629/10000000000 : ℝ)^4863 ≤ (29951787343213/100000000000000 : ℝ)^3839 := by
    have hnat : (3860754629 : ℕ)^4863*100000000000000^3839 ≤ 29951787343213^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3860754629 10000000000 29951787343213 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567879641/1250000000 : ℝ)^4863 ≤ (36808503485817/100000000000000 : ℝ)^3839 := by
    have hnat : (567879641 : ℕ)^4863*100000000000000^3839 ≤ 36808503485817^3839*1250000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567879641 1250000000 36808503485817 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095808859/5000000000 : ℝ), (3860754629/10000000000 : ℝ), (567879641/1250000000 : ℝ)] ![(16619854578767/50000000000000 : ℝ), (29951787343213/100000000000000 : ℝ), (36808503485817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095808859/5000000000 : ℝ)|^4863 ≤ (16619854578767/50000000000000 : ℝ)^3839
        have hw : |(2095808859/5000000000 : ℝ)|=(2095808859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3860754629/10000000000 : ℝ)|^4863 ≤ (29951787343213/100000000000000 : ℝ)^3839
        have hw : |(3860754629/10000000000 : ℝ)|=(3860754629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567879641/1250000000 : ℝ)|^4863 ≤ (36808503485817/100000000000000 : ℝ)^3839
        have hw : |(567879641/1250000000 : ℝ)|=(567879641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s4_4 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-820520413/5000000000 : ℝ)*x 0 + (2592549217/5000000000 : ℝ)*x 1 + (544948143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (820520413/5000000000 : ℝ)^4863 ≤ (10133590925817/100000000000000 : ℝ)^3839 := by
    have hnat : (820520413 : ℕ)^4863*100000000000000^3839 ≤ 10133590925817^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820520413 5000000000 10133590925817 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592549217/5000000000 : ℝ)^4863 ≤ (4351834724459/10000000000000 : ℝ)^3839 := by
    have hnat : (2592549217 : ℕ)^4863*10000000000000^3839 ≤ 4351834724459^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592549217 5000000000 4351834724459 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544948143/1000000000 : ℝ)^4863 ≤ (46348061804453/100000000000000 : ℝ)^3839 := by
    have hnat : (544948143 : ℕ)^4863*100000000000000^3839 ≤ 46348061804453^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544948143 1000000000 46348061804453 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-820520413/5000000000 : ℝ), (2592549217/5000000000 : ℝ), (544948143/1000000000 : ℝ)] ![(10133590925817/100000000000000 : ℝ), (4351834724459/10000000000000 : ℝ), (46348061804453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-820520413/5000000000 : ℝ)|^4863 ≤ (10133590925817/100000000000000 : ℝ)^3839
        have hw : |(-820520413/5000000000 : ℝ)|=(820520413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592549217/5000000000 : ℝ)|^4863 ≤ (4351834724459/10000000000000 : ℝ)^3839
        have hw : |(2592549217/5000000000 : ℝ)|=(2592549217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544948143/1000000000 : ℝ)|^4863 ≤ (46348061804453/100000000000000 : ℝ)^3839
        have hw : |(544948143/1000000000 : ℝ)|=(544948143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s4_5 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278199351/10000000000 : ℝ)*x 0 + (-1512837671/10000000000 : ℝ)*x 1 + (544948143/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278199351/10000000000 : ℝ)^4863 ≤ (11127631396089/25000000000000 : ℝ)^3839 := by
    have hnat : (5278199351 : ℕ)^4863*25000000000000^3839 ≤ 11127631396089^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278199351 10000000000 11127631396089 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512837671/10000000000 : ℝ)^4863 ≤ (2285353149753/25000000000000 : ℝ)^3839 := by
    have hnat : (1512837671 : ℕ)^4863*25000000000000^3839 ≤ 2285353149753^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512837671 10000000000 2285353149753 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544948143/1000000000 : ℝ)^4863 ≤ (46348061804453/100000000000000 : ℝ)^3839 := by
    have hnat : (544948143 : ℕ)^4863*100000000000000^3839 ≤ 46348061804453^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544948143 1000000000 46348061804453 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278199351/10000000000 : ℝ), (-1512837671/10000000000 : ℝ), (544948143/1000000000 : ℝ)] ![(11127631396089/25000000000000 : ℝ), (2285353149753/25000000000000 : ℝ), (46348061804453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278199351/10000000000 : ℝ)|^4863 ≤ (11127631396089/25000000000000 : ℝ)^3839
        have hw : |(5278199351/10000000000 : ℝ)|=(5278199351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1512837671/10000000000 : ℝ)|^4863 ≤ (2285353149753/25000000000000 : ℝ)^3839
        have hw : |(-1512837671/10000000000 : ℝ)|=(1512837671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544948143/1000000000 : ℝ)|^4863 ≤ (46348061804453/100000000000000 : ℝ)^3839
        have hw : |(544948143/1000000000 : ℝ)|=(544948143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s4_6 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278199351/10000000000 : ℝ)*x 0 + (544948143/1000000000 : ℝ)*x 1 + (-1512837671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278199351/10000000000 : ℝ)^4863 ≤ (11127631396089/25000000000000 : ℝ)^3839 := by
    have hnat : (5278199351 : ℕ)^4863*25000000000000^3839 ≤ 11127631396089^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278199351 10000000000 11127631396089 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544948143/1000000000 : ℝ)^4863 ≤ (46348061804453/100000000000000 : ℝ)^3839 := by
    have hnat : (544948143 : ℕ)^4863*100000000000000^3839 ≤ 46348061804453^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544948143 1000000000 46348061804453 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1512837671/10000000000 : ℝ)^4863 ≤ (2285353149753/25000000000000 : ℝ)^3839 := by
    have hnat : (1512837671 : ℕ)^4863*25000000000000^3839 ≤ 2285353149753^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512837671 10000000000 2285353149753 25000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278199351/10000000000 : ℝ), (544948143/1000000000 : ℝ), (-1512837671/10000000000 : ℝ)] ![(11127631396089/25000000000000 : ℝ), (46348061804453/100000000000000 : ℝ), (2285353149753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278199351/10000000000 : ℝ)|^4863 ≤ (11127631396089/25000000000000 : ℝ)^3839
        have hw : |(5278199351/10000000000 : ℝ)|=(5278199351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544948143/1000000000 : ℝ)|^4863 ≤ (46348061804453/100000000000000 : ℝ)^3839
        have hw : |(544948143/1000000000 : ℝ)|=(544948143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1512837671/10000000000 : ℝ)|^4863 ≤ (2285353149753/25000000000000 : ℝ)^3839
        have hw : |(-1512837671/10000000000 : ℝ)|=(1512837671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s4_7 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2095892883/5000000000 : ℝ)*x 0 + (567238839/1250000000 : ℝ)*x 1 + (3865934959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095892883/5000000000 : ℝ)^4863 ≤ (16620698627223/50000000000000 : ℝ)^3839 := by
    have hnat : (2095892883 : ℕ)^4863*50000000000000^3839 ≤ 16620698627223^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095892883 5000000000 16620698627223 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (567238839/1250000000 : ℝ)^4863 ≤ (183779486693/500000000000 : ℝ)^3839 := by
    have hnat : (567238839 : ℕ)^4863*500000000000^3839 ≤ 183779486693^3839*1250000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567238839 1250000000 183779486693 500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3865934959/10000000000 : ℝ)^4863 ≤ (30002705398937/100000000000000 : ℝ)^3839 := by
    have hnat : (3865934959 : ℕ)^4863*100000000000000^3839 ≤ 30002705398937^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865934959 10000000000 30002705398937 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2095892883/5000000000 : ℝ), (567238839/1250000000 : ℝ), (3865934959/10000000000 : ℝ)] ![(16620698627223/50000000000000 : ℝ), (183779486693/500000000000 : ℝ), (30002705398937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2095892883/5000000000 : ℝ)|^4863 ≤ (16620698627223/50000000000000 : ℝ)^3839
        have hw : |(2095892883/5000000000 : ℝ)|=(2095892883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(567238839/1250000000 : ℝ)|^4863 ≤ (183779486693/500000000000 : ℝ)^3839
        have hw : |(567238839/1250000000 : ℝ)|=(567238839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3865934959/10000000000 : ℝ)|^4863 ≤ (30002705398937/100000000000000 : ℝ)^3839
        have hw : |(3865934959/10000000000 : ℝ)|=(3865934959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1636_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16301/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5297/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3259/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16301/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2647/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16301/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2647/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16301/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2647/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16301/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2647/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16301/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2647/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16301/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2647/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2647/25000 : ℝ) ^ (4859/1024 : ℝ) ≤ (2358456284387437/100000000000000000000 : ℝ) := by
    have hpowers : (2647/25000 : ℝ)^4859 ≤ (2358456284387437/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2647 : ℕ)^4859*100000000000000000000^1024 ≤ 2358456284387437^1024*25000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2647 25000 2358456284387437 100000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2647/25000 : ℝ)) (X := (2358456284387437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16301/100000 : ℝ) ^ (4859/1024 : ℝ) ≤ (18275290341372383/100000000000000000000 : ℝ) := by
    have hpowers : (16301/100000 : ℝ)^4859 ≤ (18275290341372383/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16301 : ℕ)^4859*100000000000000000000^1024 ≤ 18275290341372383^1024*100000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16301 100000 18275290341372383 100000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16301/100000 : ℝ)) (X := (18275290341372383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002358456284387437/50000000000000000000 : ℝ) ≤ (1000009940375723/1000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (50002358456284387437/50000000000000000000 : ℝ)^1024 ≤ (1000009940375723/1000000000000000 : ℝ)^4859 := by
      have hnat : (50002358456284387437 : ℕ)^1024*1000000000000000^4859 ≤ 1000009940375723^4859*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002358456284387437 50000000000000000000 1000009940375723 1000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000009940375723/1000000000000000 : ℝ)) (X := (50002358456284387437/50000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001031687331287991/5000000000000000000 : ℝ) ≤ (1000043480626253/1000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (5001031687331287991/5000000000000000000 : ℝ)^1024 ≤ (1000043480626253/1000000000000000 : ℝ)^4859 := by
      have hnat : (5001031687331287991 : ℕ)^1024*1000000000000000^4859 ≤ 1000043480626253^4859*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001031687331287991 5000000000000000000 1000043480626253 1000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000043480626253/1000000000000000 : ℝ)) (X := (5001031687331287991/5000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018275290341372383/50000000000000000000 : ℝ) ≤ (1000077020876783/1000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (50018275290341372383/50000000000000000000 : ℝ)^1024 ≤ (1000077020876783/1000000000000000 : ℝ)^4859 := by
      have hnat : (50018275290341372383 : ℕ)^1024*1000000000000000^4859 ≤ 1000077020876783^4859*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018275290341372383 50000000000000000000 1000077020876783 1000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000077020876783/1000000000000000 : ℝ)) (X := (50018275290341372383/50000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2358456284387437/100000000000000000000 : ℝ) ≤ ((5712346541021282219/5713000000000000000 : ℝ)+2*(3354025053/5713000000000 : ℝ)*(2647/25000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (5712346541021282219/5713000000000000000 : ℝ)+2*(3354025053/5713000000000 : ℝ)*(2647/25000 : ℝ)=(1000009940375723/1000000000000000 : ℝ) by norm_num, show 1+2*(2358456284387437/100000000000000000000 : ℝ)=(50002358456284387437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18275290341372383/100000000000000000000 : ℝ)+(2358456284387437/100000000000000000000 : ℝ) ≤ ((5712346541021282219/5713000000000000000 : ℝ)+(3354025053/5713000000000 : ℝ)*((16301/100000 : ℝ)+(2647/25000 : ℝ)))^(4859/1024 : ℝ) := by
    rw [show (5712346541021282219/5713000000000000000 : ℝ)+(3354025053/5713000000000 : ℝ)*((16301/100000 : ℝ)+(2647/25000 : ℝ))=(1000043480626253/1000000000000000 : ℝ) by norm_num, show 1+(18275290341372383/100000000000000000000 : ℝ)+(2358456284387437/100000000000000000000 : ℝ)=(5001031687331287991/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18275290341372383/100000000000000000000 : ℝ) ≤ ((5712346541021282219/5713000000000000000 : ℝ)+2*(3354025053/5713000000000 : ℝ)*(16301/100000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (5712346541021282219/5713000000000000000 : ℝ)+2*(3354025053/5713000000000 : ℝ)*(16301/100000 : ℝ)=(1000077020876783/1000000000000000 : ℝ) by norm_num, show 1+2*(18275290341372383/100000000000000000000 : ℝ)=(50018275290341372383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5712346541021282219/5713000000000000000 : ℝ)*(X 1 0+X 2 0)+(3354025053/5713000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (2647/25000 : ℝ)) (hi := (16301/100000 : ℝ)) (c := (5712346541021282219/5713000000000000000 : ℝ)) (alpha := (3354025053/5713000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5712346541021282219/5713000000000000000 : ℝ)*(X 0 1+X 2 1)+(3354025053/5713000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (2647/25000 : ℝ)) (hi := (16301/100000 : ℝ)) (c := (5712346541021282219/5713000000000000000 : ℝ)) (alpha := (3354025053/5713000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5712346541021282219/5713000000000000000 : ℝ)*(X 0 2+X 1 2)+(3354025053/5713000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (2647/25000 : ℝ)) (hi := (16301/100000 : ℝ)) (c := (5712346541021282219/5713000000000000000 : ℝ)) (alpha := (3354025053/5713000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1640974711/10000000000 : ℝ)*X 0 0+(2725759777/5000000000 : ℝ)*X 0 1+(518308153/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349784799/10000000000 : ℝ)*X 1 0+(-889618803/5000000000 : ℝ)*X 1 1+(5183081479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674892377/5000000000 : ℝ)*X 2 0+(207323261/400000000 : ℝ)*X 2 1+(-355847521/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2095808859/5000000000 : ℝ)*X 0 0+(3860754629/10000000000 : ℝ)*X 0 1+(567879641/1250000000 : ℝ)*X 0 2+(2095808859/5000000000 : ℝ)*X 1 0+(3860754629/10000000000 : ℝ)*X 1 1+(567879641/1250000000 : ℝ)*X 1 2+(2095808859/5000000000 : ℝ)*X 2 0+(3860754629/10000000000 : ℝ)*X 2 1+(567879641/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-820520413/5000000000 : ℝ)*X 0 0+(2592549217/5000000000 : ℝ)*X 0 1+(544948143/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278199351/10000000000 : ℝ)*X 1 0+(-1512837671/10000000000 : ℝ)*X 1 1+(544948143/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278199351/10000000000 : ℝ)*X 2 0+(544948143/1000000000 : ℝ)*X 2 1+(-1512837671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2095892883/5000000000 : ℝ)*X 0 0+(567238839/1250000000 : ℝ)*X 0 1+(3865934959/10000000000 : ℝ)*X 0 2+(2095892883/5000000000 : ℝ)*X 1 0+(567238839/1250000000 : ℝ)*X 1 1+(3865934959/10000000000 : ℝ)*X 1 2+(2095892883/5000000000 : ℝ)*X 2 0+(567238839/1250000000 : ℝ)*X 2 1+(3865934959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (299216723870454700461898857/35706250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1346204633/100000000000000 : ℝ)*(base19) + (1229554687/100000000000000 : ℝ)*(base23) + (22820711/50000000000000 : ℝ)*(lower2) + (102857987/50000000000000 : ℝ)*(upper3) + (140478913/100000000000000 : ℝ)*(upper5) + (648871167899149/25000000000000 : ℝ)*(major0) + (648871167899149/25000000000000 : ℝ)*(major1) + (648871167899149/25000000000000 : ℝ)*(major2) + (186263565099079/5000000000000 : ℝ)*(sp0) + (7450571723943/200000000000 : ℝ)*(sp1) + (745057195724289/20000000000000 : ℝ)*(sp2) + (91604676266199/6250000000000 : ℝ)*(sp3) + (15906194553/100000000000000 : ℝ)*(sp4) + (7035426073/100000000000000 : ℝ)*(sp7) + (732840927842629/50000000000000 : ℝ)*(f.failure) + (931321802044033/25000000000000 : ℝ)*(f.sum) + (595432513503/714125000000000000000000000 : ℝ)*base65 + (1956833248849881631/142825000000000000000000000000000 : ℝ)*base67 + (158504290355006631/142825000000000000000000000000000 : ℝ)*base69 + (2200731859883681631/142825000000000000000000000000000 : ℝ)*base71 + (2852615260819/357062500000000000000000000 : ℝ)*base73 + (389512422420743369/142825000000000000000000000000000 : ℝ)*base76 + (268706516273931631/142825000000000000000000000000000 : ℝ)*base77 + (1018350411723906631/142825000000000000000000000000000 : ℝ)*base79 + (5956138596809/2856500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (17811299/5000000000000000000000 : ℝ)*base90 + (17811299/5000000000000000000000 : ℝ)*base92 + (17811299/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2773497325221503596717150299/285650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (724571577/50000000000000 : ℝ)*(base19) + (1568318947/100000000000000 : ℝ)*(base23) + (455591963/100000000000000 : ℝ)*(lower1) + (50960829/25000000000000 : ℝ)*(upper3) + (2683157/5000000000000 : ℝ)*(lower4) + (100610463/50000000000000 : ℝ)*(upper5) + (2635257851305893/100000000000000 : ℝ)*(major0) + (2635257851305893/100000000000000 : ℝ)*(major1) + (2635257851305893/100000000000000 : ℝ)*(major2) + (1290796061/100000000000000 : ℝ)*(sp2) + (3782373429994397/100000000000000 : ℝ)*(sp4) + (3782371980851243/100000000000000 : ℝ)*(sp5) + (378237057087939/10000000000000 : ℝ)*(sp6) + (186017743621233/12500000000000 : ℝ)*(sp7) + (186017743621233/12500000000000 : ℝ)*(f.failure) + (3782373429994397/100000000000000 : ℝ)*(f.sum) + (7113634877227/2856500000000000000000000000 : ℝ)*base65 + (3152446401454016567/571300000000000000000000000000000 : ℝ)*base67 + (6821697308488016567/571300000000000000000000000000000 : ℝ)*base69 + (13769483393762283433/571300000000000000000000000000000 : ℝ)*base72 + (7069298557117/1142600000000000000000000000 : ℝ)*base73 + (17667288446825983433/571300000000000000000000000000000 : ℝ)*base76 + (4381753606799416567/571300000000000000000000000000000 : ℝ)*base77 + (654079273708916567/571300000000000000000000000000000 : ℝ)*base79 + (34116524642127/5713000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (14432823/1250000000000000000000 : ℝ)*base90 + (14432823/1250000000000000000000 : ℝ)*base92 + (14432823/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1636_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16301/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1636_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1636_s5_0 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349780007/10000000000 : ℝ)*x 0 + (1036620069/2000000000 : ℝ)*x 1 + (-1779218941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349780007/10000000000 : ℝ)^4863 ≤ (4527654710611/10000000000000 : ℝ)^3839 := by
    have hnat : (5349780007 : ℕ)^4863*10000000000000^3839 ≤ 4527654710611^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349780007 10000000000 4527654710611 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036620069/2000000000 : ℝ)^4863 ≤ (4349710531077/10000000000000 : ℝ)^3839 := by
    have hnat : (1036620069 : ℕ)^4863*10000000000000^3839 ≤ 4349710531077^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036620069 2000000000 4349710531077 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1779218941/10000000000 : ℝ)^4863 ≤ (561317378407/5000000000000 : ℝ)^3839 := by
    have hnat : (1779218941 : ℕ)^4863*5000000000000^3839 ≤ 561317378407^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779218941 10000000000 561317378407 5000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349780007/10000000000 : ℝ), (1036620069/2000000000 : ℝ), (-1779218941/10000000000 : ℝ)] ![(4527654710611/10000000000000 : ℝ), (4349710531077/10000000000000 : ℝ), (561317378407/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349780007/10000000000 : ℝ)|^4863 ≤ (4527654710611/10000000000000 : ℝ)^3839
        have hw : |(5349780007/10000000000 : ℝ)|=(5349780007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036620069/2000000000 : ℝ)|^4863 ≤ (4349710531077/10000000000000 : ℝ)^3839
        have hw : |(1036620069/2000000000 : ℝ)|=(1036620069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1779218941/10000000000 : ℝ)|^4863 ≤ (561317378407/5000000000000 : ℝ)^3839
        have hw : |(-1779218941/10000000000 : ℝ)|=(1779218941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s5_1 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-328208857/2000000000 : ℝ)*x 0 + (5185116757/10000000000 : ℝ)*x 1 + (2724730419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328208857/2000000000 : ℝ)^4863 ≤ (1013361798289/10000000000000 : ℝ)^3839 := by
    have hnat : (328208857 : ℕ)^4863*10000000000000^3839 ≤ 1013361798289^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328208857 2000000000 1013361798289 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185116757/10000000000 : ℝ)^4863 ≤ (43518542048797/100000000000000 : ℝ)^3839 := by
    have hnat : (5185116757 : ℕ)^4863*100000000000000^3839 ≤ 43518542048797^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185116757 10000000000 43518542048797 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724730419/5000000000 : ℝ)^4863 ≤ (1158695998843/2500000000000 : ℝ)^3839 := by
    have hnat : (2724730419 : ℕ)^4863*2500000000000^3839 ≤ 1158695998843^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724730419 5000000000 1158695998843 2500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-328208857/2000000000 : ℝ), (5185116757/10000000000 : ℝ), (2724730419/5000000000 : ℝ)] ![(1013361798289/10000000000000 : ℝ), (43518542048797/100000000000000 : ℝ), (1158695998843/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-328208857/2000000000 : ℝ)|^4863 ≤ (1013361798289/10000000000000 : ℝ)^3839
        have hw : |(-328208857/2000000000 : ℝ)|=(328208857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185116757/10000000000 : ℝ)|^4863 ≤ (43518542048797/100000000000000 : ℝ)^3839
        have hw : |(5185116757/10000000000 : ℝ)|=(5185116757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724730419/5000000000 : ℝ)|^4863 ≤ (1158695998843/2500000000000 : ℝ)^3839
        have hw : |(2724730419/5000000000 : ℝ)|=(2724730419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s5_2 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639102249/5000000000 : ℝ)*x 0 + (-1512859369/10000000000 : ℝ)*x 1 + (5449460911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639102249/5000000000 : ℝ)^4863 ≤ (44510580565949/100000000000000 : ℝ)^3839 := by
    have hnat : (2639102249 : ℕ)^4863*100000000000000^3839 ≤ 44510580565949^3839*5000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639102249 5000000000 44510580565949 100000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512859369/10000000000 : ℝ)^4863 ≤ (4570789341483/50000000000000 : ℝ)^3839 := by
    have hnat : (1512859369 : ℕ)^4863*50000000000000^3839 ≤ 4570789341483^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512859369 10000000000 4570789341483 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449460911/10000000000 : ℝ)^4863 ≤ (9269568148039/20000000000000 : ℝ)^3839 := by
    have hnat : (5449460911 : ℕ)^4863*20000000000000^3839 ≤ 9269568148039^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449460911 10000000000 9269568148039 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639102249/5000000000 : ℝ), (-1512859369/10000000000 : ℝ), (5449460911/10000000000 : ℝ)] ![(44510580565949/100000000000000 : ℝ), (4570789341483/50000000000000 : ℝ), (9269568148039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639102249/5000000000 : ℝ)|^4863 ≤ (44510580565949/100000000000000 : ℝ)^3839
        have hw : |(2639102249/5000000000 : ℝ)|=(2639102249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1512859369/10000000000 : ℝ)|^4863 ≤ (4570789341483/50000000000000 : ℝ)^3839
        have hw : |(-1512859369/10000000000 : ℝ)|=(1512859369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449460911/10000000000 : ℝ)|^4863 ≤ (9269568148039/20000000000000 : ℝ)^3839
        have hw : |(5449460911/10000000000 : ℝ)|=(5449460911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s5_3 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527820457/1000000000 : ℝ)*x 0 + (5449460849/10000000000 : ℝ)*x 1 + (-302571871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527820457/1000000000 : ℝ)^4863 ≤ (1390955666721/3125000000000 : ℝ)^3839 := by
    have hnat : (527820457 : ℕ)^4863*3125000000000^3839 ≤ 1390955666721^3839*1000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527820457 1000000000 1390955666721 3125000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5449460849/10000000000 : ℝ)^4863 ≤ (4634784007223/10000000000000 : ℝ)^3839 := by
    have hnat : (5449460849 : ℕ)^4863*10000000000000^3839 ≤ 4634784007223^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449460849 10000000000 4634784007223 10000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302571871/2000000000 : ℝ)^4863 ≤ (1828315715161/20000000000000 : ℝ)^3839 := by
    have hnat : (302571871 : ℕ)^4863*20000000000000^3839 ≤ 1828315715161^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302571871 2000000000 1828315715161 20000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527820457/1000000000 : ℝ), (5449460849/10000000000 : ℝ), (-302571871/2000000000 : ℝ)] ![(1390955666721/3125000000000 : ℝ), (4634784007223/10000000000000 : ℝ), (1828315715161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527820457/1000000000 : ℝ)|^4863 ≤ (1390955666721/3125000000000 : ℝ)^3839
        have hw : |(527820457/1000000000 : ℝ)|=(527820457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5449460849/10000000000 : ℝ)|^4863 ≤ (4634784007223/10000000000000 : ℝ)^3839
        have hw : |(5449460849/10000000000 : ℝ)|=(5449460849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302571871/2000000000 : ℝ)|^4863 ≤ (1828315715161/20000000000000 : ℝ)^3839
        have hw : |(-302571871/2000000000 : ℝ)|=(302571871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1636_s5_4 (p : ℝ) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4191788513/10000000000 : ℝ)*x 0 + (4537861229/10000000000 : ℝ)*x 1 + (773196759/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191788513/10000000000 : ℝ)^4863 ≤ (16620712424553/50000000000000 : ℝ)^3839 := by
    have hnat : (4191788513 : ℕ)^4863*50000000000000^3839 ≤ 16620712424553^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191788513 10000000000 16620712424553 50000000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4537861229/10000000000 : ℝ)^4863 ≤ (2297211852013/6250000000000 : ℝ)^3839 := by
    have hnat : (4537861229 : ℕ)^4863*6250000000000^3839 ≤ 2297211852013^3839*10000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537861229 10000000000 2297211852013 6250000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773196759/2000000000 : ℝ)^4863 ≤ (150015927501/500000000000 : ℝ)^3839 := by
    have hnat : (773196759 : ℕ)^4863*500000000000^3839 ≤ 150015927501^3839*2000000000^4863 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773196759 2000000000 150015927501 500000000000 4863 3839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4863/1024 : ℝ)) 4863 3839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191788513/10000000000 : ℝ), (4537861229/10000000000 : ℝ), (773196759/2000000000 : ℝ)] ![(16620712424553/50000000000000 : ℝ), (2297211852013/6250000000000 : ℝ), (150015927501/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191788513/10000000000 : ℝ)|^4863 ≤ (16620712424553/50000000000000 : ℝ)^3839
        have hw : |(4191788513/10000000000 : ℝ)|=(4191788513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4537861229/10000000000 : ℝ)|^4863 ≤ (2297211852013/6250000000000 : ℝ)^3839
        have hw : |(4537861229/10000000000 : ℝ)|=(4537861229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773196759/2000000000 : ℝ)|^4863 ≤ (150015927501/500000000000 : ℝ)^3839
        have hw : |(773196759/2000000000 : ℝ)|=(773196759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1636_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5297/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8147/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5297/50000 : ℝ) ^ (4859/1024 : ℝ) ≤ (47296096216537/2000000000000000000 : ℝ) := by
    have hpowers : (5297/50000 : ℝ)^4859 ≤ (47296096216537/2000000000000000000 : ℝ)^1024 := by
      have hnat : (5297 : ℕ)^4859*2000000000000000000^1024 ≤ 47296096216537^1024*50000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5297 50000 47296096216537 2000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5297/50000 : ℝ)) (X := (47296096216537/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3259/20000 : ℝ) ^ (4859/1024 : ℝ) ≤ (4560848352684443/25000000000000000000 : ℝ) := by
    have hpowers : (3259/20000 : ℝ)^4859 ≤ (4560848352684443/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3259 : ℕ)^4859*25000000000000000000^1024 ≤ 4560848352684443^1024*20000^4859 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3259 20000 4560848352684443 25000000000000000000 4859 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3259/20000 : ℝ)) (X := (4560848352684443/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000047296096216537/1000000000000000000 : ℝ) ≤ (2000019934265739/2000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (1000047296096216537/1000000000000000000 : ℝ)^1024 ≤ (2000019934265739/2000000000000000 : ℝ)^4859 := by
      have hnat : (1000047296096216537 : ℕ)^1024*2000000000000000^4859 ≤ 2000019934265739^4859*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000047296096216537 1000000000000000000 2000019934265739 2000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000019934265739/2000000000000000 : ℝ)) (X := (1000047296096216537/1000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010304099110782311/50000000000000000000 : ℝ) ≤ (10000434267935533/10000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (50010304099110782311/50000000000000000000 : ℝ)^1024 ≤ (10000434267935533/10000000000000000 : ℝ)^4859 := by
      have hnat : (50010304099110782311 : ℕ)^1024*10000000000000000^4859 ≤ 10000434267935533^4859*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010304099110782311 50000000000000000000 10000434267935533 10000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000434267935533/10000000000000000 : ℝ)) (X := (50010304099110782311/50000000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504560848352684443/12500000000000000000 : ℝ) ≤ (10000768864542371/10000000000000000 : ℝ) ^ (4859/1024 : ℝ) := by
    have hpowers : (12504560848352684443/12500000000000000000 : ℝ)^1024 ≤ (10000768864542371/10000000000000000 : ℝ)^4859 := by
      have hnat : (12504560848352684443 : ℕ)^1024*10000000000000000^4859 ≤ 10000768864542371^4859*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504560848352684443 12500000000000000000 10000768864542371 10000000000000000 1024 4859 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000768864542371/10000000000000000 : ℝ)) (X := (12504560848352684443/12500000000000000000 : ℝ)) (by norm_num) 4859 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(47296096216537/2000000000000000000 : ℝ) ≤ ((57003478793339206651/57010000000000000000 : ℝ)+2*(167298303419/285050000000000 : ℝ)*(5297/50000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (57003478793339206651/57010000000000000000 : ℝ)+2*(167298303419/285050000000000 : ℝ)*(5297/50000 : ℝ)=(2000019934265739/2000000000000000 : ℝ) by norm_num, show 1+2*(47296096216537/2000000000000000000 : ℝ)=(1000047296096216537/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4560848352684443/25000000000000000000 : ℝ)+(47296096216537/2000000000000000000 : ℝ) ≤ ((57003478793339206651/57010000000000000000 : ℝ)+(167298303419/285050000000000 : ℝ)*((3259/20000 : ℝ)+(5297/50000 : ℝ)))^(4859/1024 : ℝ) := by
    rw [show (57003478793339206651/57010000000000000000 : ℝ)+(167298303419/285050000000000 : ℝ)*((3259/20000 : ℝ)+(5297/50000 : ℝ))=(10000434267935533/10000000000000000 : ℝ) by norm_num, show 1+(4560848352684443/25000000000000000000 : ℝ)+(47296096216537/2000000000000000000 : ℝ)=(50010304099110782311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4560848352684443/25000000000000000000 : ℝ) ≤ ((57003478793339206651/57010000000000000000 : ℝ)+2*(167298303419/285050000000000 : ℝ)*(3259/20000 : ℝ))^(4859/1024 : ℝ) := by
    rw [show (57003478793339206651/57010000000000000000 : ℝ)+2*(167298303419/285050000000000 : ℝ)*(3259/20000 : ℝ)=(10000768864542371/10000000000000000 : ℝ) by norm_num, show 1+2*(4560848352684443/25000000000000000000 : ℝ)=(12504560848352684443/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57003478793339206651/57010000000000000000 : ℝ)*(X 1 0+X 2 0)+(167298303419/285050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (57003478793339206651/57010000000000000000 : ℝ)) (alpha := (167298303419/285050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57003478793339206651/57010000000000000000 : ℝ)*(X 0 1+X 2 1)+(167298303419/285050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (57003478793339206651/57010000000000000000 : ℝ)) (alpha := (167298303419/285050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57003478793339206651/57010000000000000000 : ℝ)*(X 0 2+X 1 2)+(167298303419/285050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4859/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (57003478793339206651/57010000000000000000 : ℝ)) (alpha := (167298303419/285050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5349780007/10000000000 : ℝ)*X 2 0+(1036620069/2000000000 : ℝ)*X 2 1+(-1779218941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s5_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-328208857/2000000000 : ℝ)*X 0 0+(5185116757/10000000000 : ℝ)*X 0 1+(2724730419/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s5_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2639102249/5000000000 : ℝ)*X 1 0+(-1512859369/10000000000 : ℝ)*X 1 1+(5449460911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s5_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((527820457/1000000000 : ℝ)*X 2 0+(5449460849/10000000000 : ℝ)*X 2 1+(-302571871/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s5_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4191788513/10000000000 : ℝ)*X 0 0+(4537861229/10000000000 : ℝ)*X 0 1+(773196759/2000000000 : ℝ)*X 0 2+(4191788513/10000000000 : ℝ)*X 1 0+(4537861229/10000000000 : ℝ)*X 1 1+(773196759/2000000000 : ℝ)*X 1 2+(4191788513/10000000000 : ℝ)*X 2 0+(4537861229/10000000000 : ℝ)*X 2 1+(773196759/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1636_s5_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4812779895321103442266344741/1425250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (447119037/100000000000000 : ℝ)*(base19) + (646709017/100000000000000 : ℝ)*(base23) + (135015321/100000000000000 : ℝ)*(lower1) + (96063403/100000000000000 : ℝ)*(upper3) + (28440771/50000000000000 : ℝ)*(lower4) + (22988643/100000000000000 : ℝ)*(upper5) + (1317826535788197/50000000000000 : ℝ)*(major0) + (1317826535788197/50000000000000 : ℝ)*(major1) + (1317826535788197/50000000000000 : ℝ)*(major2) + (2965956301/100000000000000 : ℝ)*(sp0) + (3782940898960509/100000000000000 : ℝ)*(sp1) + (59108444560023/1562500000000 : ℝ)*(sp2) + (472867160786899/12500000000000 : ℝ)*(sp3) + (37209128290809/2500000000000 : ℝ)*(sp4) + (37209128290809/2500000000000 : ℝ)*(f.failure) + (3782940898960509/100000000000000 : ℝ)*(f.sum) + (104326561056597/28505000000000000000000000000 : ℝ)*base65 + (72284801350131798247/2850500000000000000000000000000000 : ℝ)*base67 + (25639944435012701753/2850500000000000000000000000000000 : ℝ)*base70 + (18942248997590298247/2850500000000000000000000000000000 : ℝ)*base71 + (27108677858453/7126250000000000000000000000 : ℝ)*base73 + (313337073944737701753/2850500000000000000000000000000000 : ℝ)*base76 + (14167906182005201753/2850500000000000000000000000000000 : ℝ)*base78 + (44391330295138201753/2850500000000000000000000000000000 : ℝ)*base80 + (134529609428323/28505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (779121/250000000000000000000 : ℝ)*base89 + (779121/250000000000000000000 : ℝ)*base91 + (779121/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1636_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1636_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1636_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1636_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1636_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1636_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4859/1024 : ℝ) ≤ p) (hpb : p ≤ (4863/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (177083769/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8147/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1636_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

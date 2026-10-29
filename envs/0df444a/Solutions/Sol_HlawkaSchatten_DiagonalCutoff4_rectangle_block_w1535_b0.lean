-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1535_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:09.673149+00:00
-- url     : https://prove2.me/submissions/ebe44846-f6f1-4d73-bfcb-ccce71f6b421

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
theorem support_rectangle_w1535_s0_0 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-830854789/5000000000 : ℝ)*x 0 + (5895338307/10000000000 : ℝ)*x 1 + (2432516429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830854789/5000000000 : ℝ)^4567 ≤ (4945947457069/50000000000000 : ℝ)^3543 := by
    have hnat : (830854789 : ℕ)^4567*50000000000000^3543 ≤ 4945947457069^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830854789 5000000000 4945947457069 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5895338307/10000000000 : ℝ)^4567 ≤ (3162722184651/6250000000000 : ℝ)^3543 := by
    have hnat : (5895338307 : ℕ)^4567*6250000000000^3543 ≤ 3162722184651^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5895338307 10000000000 3162722184651 6250000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2432516429/5000000000 : ℝ)^4567 ≤ (39504550111531/100000000000000 : ℝ)^3543 := by
    have hnat : (2432516429 : ℕ)^4567*100000000000000^3543 ≤ 39504550111531^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432516429 5000000000 39504550111531 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-830854789/5000000000 : ℝ), (5895338307/10000000000 : ℝ), (2432516429/5000000000 : ℝ)] ![(4945947457069/50000000000000 : ℝ), (3162722184651/6250000000000 : ℝ), (39504550111531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-830854789/5000000000 : ℝ)|^4567 ≤ (4945947457069/50000000000000 : ℝ)^3543
        have hw : |(-830854789/5000000000 : ℝ)|=(830854789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5895338307/10000000000 : ℝ)|^4567 ≤ (3162722184651/6250000000000 : ℝ)^3543
        have hw : |(5895338307/10000000000 : ℝ)|=(5895338307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2432516429/5000000000 : ℝ)|^4567 ≤ (39504550111531/100000000000000 : ℝ)^3543
        have hw : |(2432516429/5000000000 : ℝ)|=(2432516429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s0_1 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2736496457/5000000000 : ℝ)*x 0 + (-2237528713/10000000000 : ℝ)*x 1 + (973006581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2736496457/5000000000 : ℝ)^4567 ≤ (459797371517/1000000000000 : ℝ)^3543 := by
    have hnat : (2736496457 : ℕ)^4567*1000000000000^3543 ≤ 459797371517^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736496457 5000000000 459797371517 1000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237528713/10000000000 : ℝ)^4567 ≤ (1451571223709/10000000000000 : ℝ)^3543 := by
    have hnat : (2237528713 : ℕ)^4567*10000000000000^3543 ≤ 1451571223709^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237528713 10000000000 1451571223709 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973006581/2000000000 : ℝ)^4567 ≤ (39504550603479/100000000000000 : ℝ)^3543 := by
    have hnat : (973006581 : ℕ)^4567*100000000000000^3543 ≤ 39504550603479^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973006581 2000000000 39504550603479 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2736496457/5000000000 : ℝ), (-2237528713/10000000000 : ℝ), (973006581/2000000000 : ℝ)] ![(459797371517/1000000000000 : ℝ), (1451571223709/10000000000000 : ℝ), (39504550603479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2736496457/5000000000 : ℝ)|^4567 ≤ (459797371517/1000000000000 : ℝ)^3543
        have hw : |(2736496457/5000000000 : ℝ)|=(2736496457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2237528713/10000000000 : ℝ)|^4567 ≤ (1451571223709/10000000000000 : ℝ)^3543
        have hw : |(-2237528713/10000000000 : ℝ)|=(2237528713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(973006581/2000000000 : ℝ)|^4567 ≤ (39504550603479/100000000000000 : ℝ)^3543
        have hw : |(973006581/2000000000 : ℝ)|=(973006581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s0_2 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (547299287/1000000000 : ℝ)*x 0 + (973006577/2000000000 : ℝ)*x 1 + (-2237528793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547299287/1000000000 : ℝ)^4567 ≤ (4597973667521/10000000000000 : ℝ)^3543 := by
    have hnat : (547299287 : ℕ)^4567*10000000000000^3543 ≤ 4597973667521^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547299287 1000000000 4597973667521 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973006577/2000000000 : ℝ)^4567 ≤ (39504550394139/100000000000000 : ℝ)^3543 := by
    have hnat : (973006577 : ℕ)^4567*100000000000000^3543 ≤ 39504550394139^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973006577 2000000000 39504550394139 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237528793/10000000000 : ℝ)^4567 ≤ (90723205663/625000000000 : ℝ)^3543 := by
    have hnat : (2237528793 : ℕ)^4567*625000000000^3543 ≤ 90723205663^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237528793 10000000000 90723205663 625000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547299287/1000000000 : ℝ), (973006577/2000000000 : ℝ), (-2237528793/10000000000 : ℝ)] ![(4597973667521/10000000000000 : ℝ), (39504550394139/100000000000000 : ℝ), (90723205663/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547299287/1000000000 : ℝ)|^4567 ≤ (4597973667521/10000000000000 : ℝ)^3543
        have hw : |(547299287/1000000000 : ℝ)|=(547299287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973006577/2000000000 : ℝ)|^4567 ≤ (39504550394139/100000000000000 : ℝ)^3543
        have hw : |(973006577/2000000000 : ℝ)|=(973006577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2237528793/10000000000 : ℝ)|^4567 ≤ (90723205663/625000000000 : ℝ)^3543
        have hw : |(-2237528793/10000000000 : ℝ)|=(2237528793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s0_3 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2069499103/5000000000 : ℝ)*x 0 + (772921827/2500000000 : ℝ)*x 1 + (5465906587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069499103/5000000000 : ℝ)^4567 ≤ (32075251364129/100000000000000 : ℝ)^3543 := by
    have hnat : (2069499103 : ℕ)^4567*100000000000000^3543 ≤ 32075251364129^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069499103 5000000000 32075251364129 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772921827/2500000000 : ℝ)^4567 ≤ (11010868630743/50000000000000 : ℝ)^3543 := by
    have hnat : (772921827 : ℕ)^4567*50000000000000^3543 ≤ 11010868630743^3543*2500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772921827 2500000000 11010868630743 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465906587/10000000000 : ℝ)^4567 ≤ (4590301136437/10000000000000 : ℝ)^3543 := by
    have hnat : (5465906587 : ℕ)^4567*10000000000000^3543 ≤ 4590301136437^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465906587 10000000000 4590301136437 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2069499103/5000000000 : ℝ), (772921827/2500000000 : ℝ), (5465906587/10000000000 : ℝ)] ![(32075251364129/100000000000000 : ℝ), (11010868630743/50000000000000 : ℝ), (4590301136437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2069499103/5000000000 : ℝ)|^4567 ≤ (32075251364129/100000000000000 : ℝ)^3543
        have hw : |(2069499103/5000000000 : ℝ)|=(2069499103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772921827/2500000000 : ℝ)|^4567 ≤ (11010868630743/50000000000000 : ℝ)^3543
        have hw : |(772921827/2500000000 : ℝ)|=(772921827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465906587/10000000000 : ℝ)|^4567 ≤ (4590301136437/10000000000000 : ℝ)^3543
        have hw : |(5465906587/10000000000 : ℝ)|=(5465906587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s0_4 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-832518543/5000000000 : ℝ)*x 0 + (4891194611/10000000000 : ℝ)*x 1 + (5868243861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832518543/5000000000 : ℝ)^4567 ≤ (2479358846773/25000000000000 : ℝ)^3543 := by
    have hnat : (832518543 : ℕ)^4567*25000000000000^3543 ≤ 2479358846773^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832518543 5000000000 2479358846773 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4891194611/10000000000 : ℝ)^4567 ≤ (1988929853157/5000000000000 : ℝ)^3543 := by
    have hnat : (4891194611 : ℕ)^4567*5000000000000^3543 ≤ 1988929853157^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4891194611 10000000000 1988929853157 5000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5868243861/10000000000 : ℝ)^4567 ≤ (50303967529783/100000000000000 : ℝ)^3543 := by
    have hnat : (5868243861 : ℕ)^4567*100000000000000^3543 ≤ 50303967529783^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5868243861 10000000000 50303967529783 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-832518543/5000000000 : ℝ), (4891194611/10000000000 : ℝ), (5868243861/10000000000 : ℝ)] ![(2479358846773/25000000000000 : ℝ), (1988929853157/5000000000000 : ℝ), (50303967529783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-832518543/5000000000 : ℝ)|^4567 ≤ (2479358846773/25000000000000 : ℝ)^3543
        have hw : |(-832518543/5000000000 : ℝ)|=(832518543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4891194611/10000000000 : ℝ)|^4567 ≤ (1988929853157/5000000000000 : ℝ)^3543
        have hw : |(4891194611/10000000000 : ℝ)|=(4891194611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5868243861/10000000000 : ℝ)|^4567 ≤ (50303967529783/100000000000000 : ℝ)^3543
        have hw : |(5868243861/10000000000 : ℝ)|=(5868243861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s0_5 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191415003/10000000000 : ℝ)*x 0 + (-1234317309/10000000000 : ℝ)*x 1 + (733530407/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191415003/10000000000 : ℝ)^4567 ≤ (42953391732593/100000000000000 : ℝ)^3543 := by
    have hnat : (5191415003 : ℕ)^4567*100000000000000^3543 ≤ 42953391732593^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191415003 10000000000 42953391732593 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1234317309/10000000000 : ℝ)^4567 ≤ (3371323703353/50000000000000 : ℝ)^3543 := by
    have hnat : (1234317309 : ℕ)^4567*50000000000000^3543 ≤ 3371323703353^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234317309 10000000000 3371323703353 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (733530407/1250000000 : ℝ)^4567 ≤ (50303960844661/100000000000000 : ℝ)^3543 := by
    have hnat : (733530407 : ℕ)^4567*100000000000000^3543 ≤ 50303960844661^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733530407 1250000000 50303960844661 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191415003/10000000000 : ℝ), (-1234317309/10000000000 : ℝ), (733530407/1250000000 : ℝ)] ![(42953391732593/100000000000000 : ℝ), (3371323703353/50000000000000 : ℝ), (50303960844661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191415003/10000000000 : ℝ)|^4567 ≤ (42953391732593/100000000000000 : ℝ)^3543
        have hw : |(5191415003/10000000000 : ℝ)|=(5191415003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1234317309/10000000000 : ℝ)|^4567 ≤ (3371323703353/50000000000000 : ℝ)^3543
        have hw : |(-1234317309/10000000000 : ℝ)|=(1234317309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(733530407/1250000000 : ℝ)|^4567 ≤ (50303960844661/100000000000000 : ℝ)^3543
        have hw : |(733530407/1250000000 : ℝ)|=(733530407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s0_6 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191414757/10000000000 : ℝ)*x 0 + (293412143/500000000 : ℝ)*x 1 + (-1234318303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191414757/10000000000 : ℝ)^4567 ≤ (21476694554469/50000000000000 : ℝ)^3543 := by
    have hnat : (5191414757 : ℕ)^4567*50000000000000^3543 ≤ 21476694554469^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191414757 10000000000 21476694554469 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293412143/500000000 : ℝ)^4567 ≤ (10060791293789/20000000000000 : ℝ)^3543 := by
    have hnat : (293412143 : ℕ)^4567*20000000000000^3543 ≤ 10060791293789^3543*500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293412143 500000000 10060791293789 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1234318303/10000000000 : ℝ)^4567 ≤ (6742654405931/100000000000000 : ℝ)^3543 := by
    have hnat : (1234318303 : ℕ)^4567*100000000000000^3543 ≤ 6742654405931^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1234318303 10000000000 6742654405931 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191414757/10000000000 : ℝ), (293412143/500000000 : ℝ), (-1234318303/10000000000 : ℝ)] ![(21476694554469/50000000000000 : ℝ), (10060791293789/20000000000000 : ℝ), (6742654405931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191414757/10000000000 : ℝ)|^4567 ≤ (21476694554469/50000000000000 : ℝ)^3543
        have hw : |(5191414757/10000000000 : ℝ)|=(5191414757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(293412143/500000000 : ℝ)|^4567 ≤ (10060791293789/20000000000000 : ℝ)^3543
        have hw : |(293412143/500000000 : ℝ)|=(293412143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1234318303/10000000000 : ℝ)|^4567 ≤ (6742654405931/100000000000000 : ℝ)^3543
        have hw : |(-1234318303/10000000000 : ℝ)|=(1234318303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s0_7 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2073334011/5000000000 : ℝ)*x 0 + (337851281/625000000 : ℝ)*x 1 + (3154124367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073334011/5000000000 : ℝ)^4567 ≤ (4018985987521/12500000000000 : ℝ)^3543 := by
    have hnat : (2073334011 : ℕ)^4567*12500000000000^3543 ≤ 4018985987521^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073334011 5000000000 4018985987521 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337851281/625000000 : ℝ)^4567 ≤ (2828215057823/6250000000000 : ℝ)^3543 := by
    have hnat : (337851281 : ℕ)^4567*6250000000000^3543 ≤ 2828215057823^3543*625000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337851281 625000000 2828215057823 6250000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154124367/10000000000 : ℝ)^4567 ≤ (11298335580143/50000000000000 : ℝ)^3543 := by
    have hnat : (3154124367 : ℕ)^4567*50000000000000^3543 ≤ 11298335580143^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154124367 10000000000 11298335580143 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2073334011/5000000000 : ℝ), (337851281/625000000 : ℝ), (3154124367/10000000000 : ℝ)] ![(4018985987521/12500000000000 : ℝ), (2828215057823/6250000000000 : ℝ), (11298335580143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2073334011/5000000000 : ℝ)|^4567 ≤ (4018985987521/12500000000000 : ℝ)^3543
        have hw : |(2073334011/5000000000 : ℝ)|=(2073334011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337851281/625000000 : ℝ)|^4567 ≤ (2828215057823/6250000000000 : ℝ)^3543
        have hw : |(337851281/625000000 : ℝ)|=(337851281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154124367/10000000000 : ℝ)|^4567 ≤ (11298335580143/50000000000000 : ℝ)^3543
        have hw : |(3154124367/10000000000 : ℝ)|=(3154124367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1535_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3119/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2519/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4565/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4565 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4565*1^1024 ≤ 0^1024*1^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4565/1024 : ℝ) ≤ (841298930403147167/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4565 ≤ (841298930403147167/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4565*50000000000000000000^1024 ≤ 841298930403147167^1024*5^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 841298930403147167 50000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (841298930403147167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4565 := by
      have hnat : (1 : ℕ)^1024*1^4565 ≤ 1^4565*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50841298930403147167/50000000000000000000 : ℝ) ≤ (10037499387286037/10000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (50841298930403147167/50000000000000000000 : ℝ)^1024 ≤ (10037499387286037/10000000000000000 : ℝ)^4565 := by
      have hnat : (50841298930403147167 : ℕ)^1024*10000000000000000^4565 ≤ 10037499387286037^4565*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50841298930403147167 50000000000000000000 10037499387286037 10000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10037499387286037/10000000000000000 : ℝ)) (X := (50841298930403147167/50000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25841298930403147167/25000000000000000000 : ℝ) ≤ (5037499387286037/5000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (25841298930403147167/25000000000000000000 : ℝ)^1024 ≤ (5037499387286037/5000000000000000 : ℝ)^4565 := by
      have hnat : (25841298930403147167 : ℕ)^1024*5000000000000000^4565 ≤ 5037499387286037^4565*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25841298930403147167 25000000000000000000 5037499387286037 5000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5037499387286037/5000000000000000 : ℝ)) (X := (25841298930403147167/25000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(37499387286037/4000000000000000 : ℝ)*(0 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(37499387286037/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(841298930403147167/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(37499387286037/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4565/1024 : ℝ) := by
    rw [show (1 : ℝ)+(37499387286037/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10037499387286037/10000000000000000 : ℝ) by norm_num, show 1+(841298930403147167/50000000000000000000 : ℝ)+(0 : ℝ)=(50841298930403147167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(841298930403147167/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(37499387286037/4000000000000000 : ℝ)*(2/5 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(37499387286037/4000000000000000 : ℝ)*(2/5 : ℝ)=(5037499387286037/5000000000000000 : ℝ) by norm_num, show 1+2*(841298930403147167/50000000000000000000 : ℝ)=(25841298930403147167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(37499387286037/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (37499387286037/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(37499387286037/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (37499387286037/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(37499387286037/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (37499387286037/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-830854789/5000000000 : ℝ)*X 0 0+(5895338307/10000000000 : ℝ)*X 0 1+(2432516429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2736496457/5000000000 : ℝ)*X 1 0+(-2237528713/10000000000 : ℝ)*X 1 1+(973006581/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((547299287/1000000000 : ℝ)*X 2 0+(973006577/2000000000 : ℝ)*X 2 1+(-2237528793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2069499103/5000000000 : ℝ)*X 0 0+(772921827/2500000000 : ℝ)*X 0 1+(5465906587/10000000000 : ℝ)*X 0 2+(2069499103/5000000000 : ℝ)*X 1 0+(772921827/2500000000 : ℝ)*X 1 1+(5465906587/10000000000 : ℝ)*X 1 2+(2069499103/5000000000 : ℝ)*X 2 0+(772921827/2500000000 : ℝ)*X 2 1+(5465906587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-832518543/5000000000 : ℝ)*X 0 0+(4891194611/10000000000 : ℝ)*X 0 1+(5868243861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5191415003/10000000000 : ℝ)*X 1 0+(-1234317309/10000000000 : ℝ)*X 1 1+(733530407/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5191414757/10000000000 : ℝ)*X 2 0+(293412143/500000000 : ℝ)*X 2 1+(-1234318303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2073334011/5000000000 : ℝ)*X 0 0+(337851281/625000000 : ℝ)*X 0 1+(3154124367/10000000000 : ℝ)*X 0 2+(2073334011/5000000000 : ℝ)*X 1 0+(337851281/625000000 : ℝ)*X 1 1+(3154124367/10000000000 : ℝ)*X 1 2+(2073334011/5000000000 : ℝ)*X 2 0+(337851281/625000000 : ℝ)*X 2 1+(3154124367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26474053682125075642377/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9960611/20000000000000 : ℝ)*(base1) + (27296693/3125000000000 : ℝ)*(base19) + (865691131/100000000000000 : ℝ)*(base23) + (62187151/50000000000000 : ℝ)*(upper3) + (98609797/100000000000000 : ℝ)*(upper5) + (86986618282893/12500000000000 : ℝ)*(major0) + (86986618282893/12500000000000 : ℝ)*(major1) + (86986618282893/12500000000000 : ℝ)*(major2) + (242647256858261/25000000000000 : ℝ)*(sp0) + (194118227866987/20000000000000 : ℝ)*(sp1) + (48529557356899/5000000000000 : ℝ)*(sp2) + (42119231843741/10000000000000 : ℝ)*(sp3) + (1517599561/50000000000000 : ℝ)*(sp4) + (171282719/12500000000000 : ℝ)*(sp7) + (210596869251109/50000000000000 : ℝ)*(f.failure) + (970592012829111/100000000000000 : ℝ)*(f.sum) + (21214197865041/25000000000000000000000000000 : ℝ)*base65 + (101689908765041/50000000000000000000000000000 : ℝ)*base67 + (318341352465041/50000000000000000000000000000 : ℝ)*base69 + (99968795165041/50000000000000000000000000000 : ℝ)*base71 + (18553940559959/25000000000000000000000000000 : ℝ)*base74 + (240992033415041/50000000000000000000000000000 : ℝ)*base75 + (124041194665041/50000000000000000000000000000 : ℝ)*base77 + (135523696265041/50000000000000000000000000000 : ℝ)*base79 + (65828562015041/25000000000000000000000000000 : ℝ)*base81 + (5130331/1000000000000000000000 : ℝ)*base90 + (5130331/1000000000000000000000 : ℝ)*base92 + (5130331/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (215178145279637795745549/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1711974891/100000000000000 : ℝ)*(base19) + (411464349/25000000000000 : ℝ)*(base23) + (33877701/10000000000000 : ℝ)*(base32) + (241730701/100000000000000 : ℝ)*(upper3) + (10823577/20000000000000 : ℝ)*(upper5) + (366909255172059/50000000000000 : ℝ)*(major0) + (366909255172059/50000000000000 : ℝ)*(major1) + (366909255172059/50000000000000 : ℝ)*(major2) + (4024027829/100000000000000 : ℝ)*(sp1) + (92479819/2500000000000 : ℝ)*(sp2) + (102348830058941/10000000000000 : ℝ)*(sp4) + (1023482564586691/100000000000000 : ℝ)*(sp5) + (511741477769627/50000000000000 : ℝ)*(sp6) + (444148094417617/100000000000000 : ℝ)*(sp7) + (444148433194627/100000000000000 : ℝ)*(f.failure) + (102348830058941/10000000000000 : ℝ)*(f.sum) + (167198948159817/100000000000000000000000000000 : ℝ)*base66 + (1576220025159817/200000000000000000000000000000 : ℝ)*base68 + (341072393440183/200000000000000000000000000000 : ℝ)*base69 + (1012284987359817/200000000000000000000000000000 : ℝ)*base72 + (706129460359817/100000000000000000000000000000 : ℝ)*base74 + (597869032759817/200000000000000000000000000000 : ℝ)*base76 + (1079617727159817/200000000000000000000000000000 : ℝ)*base78 + (469086068840183/200000000000000000000000000000 : ℝ)*base79 + (50297396459817/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (16642307/2000000000000000000000 : ℝ)*base89 + (16642307/2000000000000000000000 : ℝ)*base91 + (16642307/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1535_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3119/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2519/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1535_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1535_s1_0 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-36186443/200000000 : ℝ)*x 0 + (2777844497/5000000000 : ℝ)*x 1 + (638713451/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36186443/200000000 : ℝ)^4567 ≤ (11038821146263/100000000000000 : ℝ)^3543 := by
    have hnat : (36186443 : ℕ)^4567*100000000000000^3543 ≤ 11038821146263^3543*200000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36186443 200000000 11038821146263 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2777844497/5000000000 : ℝ)^4567 ≤ (9375445701737/20000000000000 : ℝ)^3543 := by
    have hnat : (2777844497 : ℕ)^4567*20000000000000^3543 ≤ 9375445701737^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2777844497 5000000000 9375445701737 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638713451/1250000000 : ℝ)^4567 ≤ (2630246895403/6250000000000 : ℝ)^3543 := by
    have hnat : (638713451 : ℕ)^4567*6250000000000^3543 ≤ 2630246895403^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638713451 1250000000 2630246895403 6250000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36186443/200000000 : ℝ), (2777844497/5000000000 : ℝ), (638713451/1250000000 : ℝ)] ![(11038821146263/100000000000000 : ℝ), (9375445701737/20000000000000 : ℝ), (2630246895403/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36186443/200000000 : ℝ)|^4567 ≤ (11038821146263/100000000000000 : ℝ)^3543
        have hw : |(-36186443/200000000 : ℝ)|=(36186443/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2777844497/5000000000 : ℝ)|^4567 ≤ (9375445701737/20000000000000 : ℝ)^3543
        have hw : |(2777844497/5000000000 : ℝ)|=(2777844497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638713451/1250000000 : ℝ)|^4567 ≤ (2630246895403/6250000000000 : ℝ)^3543
        have hw : |(638713451/1250000000 : ℝ)|=(638713451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s1_1 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672811607/1250000000 : ℝ)*x 0 + (-2043508857/10000000000 : ℝ)*x 1 + (5109708141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672811607/1250000000 : ℝ)^4567 ≤ (45002033621691/100000000000000 : ℝ)^3543 := by
    have hnat : (672811607 : ℕ)^4567*100000000000000^3543 ≤ 45002033621691^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672811607 1250000000 45002033621691 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2043508857/10000000000 : ℝ)^4567 ≤ (12914010373061/100000000000000 : ℝ)^3543 := by
    have hnat : (2043508857 : ℕ)^4567*100000000000000^3543 ≤ 12914010373061^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043508857 10000000000 12914010373061 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5109708141/10000000000 : ℝ)^4567 ≤ (42083955985029/100000000000000 : ℝ)^3543 := by
    have hnat : (5109708141 : ℕ)^4567*100000000000000^3543 ≤ 42083955985029^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5109708141 10000000000 42083955985029 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672811607/1250000000 : ℝ), (-2043508857/10000000000 : ℝ), (5109708141/10000000000 : ℝ)] ![(45002033621691/100000000000000 : ℝ), (12914010373061/100000000000000 : ℝ), (42083955985029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672811607/1250000000 : ℝ)|^4567 ≤ (45002033621691/100000000000000 : ℝ)^3543
        have hw : |(672811607/1250000000 : ℝ)|=(672811607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2043508857/10000000000 : ℝ)|^4567 ≤ (12914010373061/100000000000000 : ℝ)^3543
        have hw : |(-2043508857/10000000000 : ℝ)|=(2043508857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5109708141/10000000000 : ℝ)|^4567 ≤ (42083955985029/100000000000000 : ℝ)^3543
        have hw : |(5109708141/10000000000 : ℝ)|=(5109708141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s1_2 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336405847/625000000 : ℝ)*x 0 + (2554853641/5000000000 : ℝ)*x 1 + (-2043509057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336405847/625000000 : ℝ)^4567 ≤ (45002041122667/100000000000000 : ℝ)^3543 := by
    have hnat : (336405847 : ℕ)^4567*100000000000000^3543 ≤ 45002041122667^3543*625000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336405847 625000000 45002041122667 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2554853641/5000000000 : ℝ)^4567 ≤ (42083946865477/100000000000000 : ℝ)^3543 := by
    have hnat : (2554853641 : ℕ)^4567*100000000000000^3543 ≤ 42083946865477^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554853641 5000000000 42083946865477 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2043509057/10000000000 : ℝ)^4567 ≤ (12914012002261/100000000000000 : ℝ)^3543 := by
    have hnat : (2043509057 : ℕ)^4567*100000000000000^3543 ≤ 12914012002261^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043509057 10000000000 12914012002261 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336405847/625000000 : ℝ), (2554853641/5000000000 : ℝ), (-2043509057/10000000000 : ℝ)] ![(45002041122667/100000000000000 : ℝ), (42083946865477/100000000000000 : ℝ), (12914012002261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336405847/625000000 : ℝ)|^4567 ≤ (45002041122667/100000000000000 : ℝ)^3543
        have hw : |(336405847/625000000 : ℝ)|=(336405847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2554853641/5000000000 : ℝ)|^4567 ≤ (42083946865477/100000000000000 : ℝ)^3543
        have hw : |(2554853641/5000000000 : ℝ)|=(2554853641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2043509057/10000000000 : ℝ)|^4567 ≤ (12914012002261/100000000000000 : ℝ)^3543
        have hw : |(-2043509057/10000000000 : ℝ)|=(2043509057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s1_3 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (424121749/1000000000 : ℝ)*x 0 + (1876581649/5000000000 : ℝ)*x 1 + (95617489/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424121749/1000000000 : ℝ)^4567 ≤ (33099972703567/100000000000000 : ℝ)^3543 := by
    have hnat : (424121749 : ℕ)^4567*100000000000000^3543 ≤ 33099972703567^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424121749 1000000000 33099972703567 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1876581649/5000000000 : ℝ)^4567 ≤ (14137075002459/50000000000000 : ℝ)^3543 := by
    have hnat : (1876581649 : ℕ)^4567*50000000000000^3543 ≤ 14137075002459^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876581649 5000000000 14137075002459 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95617489/200000000 : ℝ)^4567 ≤ (7725175456881/20000000000000 : ℝ)^3543 := by
    have hnat : (95617489 : ℕ)^4567*20000000000000^3543 ≤ 7725175456881^3543*200000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95617489 200000000 7725175456881 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424121749/1000000000 : ℝ), (1876581649/5000000000 : ℝ), (95617489/200000000 : ℝ)] ![(33099972703567/100000000000000 : ℝ), (14137075002459/50000000000000 : ℝ), (7725175456881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424121749/1000000000 : ℝ)|^4567 ≤ (33099972703567/100000000000000 : ℝ)^3543
        have hw : |(424121749/1000000000 : ℝ)|=(424121749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1876581649/5000000000 : ℝ)|^4567 ≤ (14137075002459/50000000000000 : ℝ)^3543
        have hw : |(1876581649/5000000000 : ℝ)|=(1876581649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95617489/200000000 : ℝ)|^4567 ≤ (7725175456881/20000000000000 : ℝ)^3543
        have hw : |(95617489/200000000 : ℝ)|=(95617489/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s1_4 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-904791809/5000000000 : ℝ)*x 0 + (998933/1953125 : ℝ)*x 1 + (2775392353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (904791809/5000000000 : ℝ)^4567 ≤ (1104087748317/10000000000000 : ℝ)^3543 := by
    have hnat : (904791809 : ℕ)^4567*10000000000000^3543 ≤ 1104087748317^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904791809 5000000000 1104087748317 10000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998933/1953125 : ℝ)^4567 ≤ (42135228018489/100000000000000 : ℝ)^3543 := by
    have hnat : (998933 : ℕ)^4567*100000000000000^3543 ≤ 42135228018489^3543*1953125^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998933 1953125 42135228018489 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2775392353/5000000000 : ℝ)^4567 ≤ (46823894477599/100000000000000 : ℝ)^3543 := by
    have hnat : (2775392353 : ℕ)^4567*100000000000000^3543 ≤ 46823894477599^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775392353 5000000000 46823894477599 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-904791809/5000000000 : ℝ), (998933/1953125 : ℝ), (2775392353/5000000000 : ℝ)] ![(1104087748317/10000000000000 : ℝ), (42135228018489/100000000000000 : ℝ), (46823894477599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-904791809/5000000000 : ℝ)|^4567 ≤ (1104087748317/10000000000000 : ℝ)^3543
        have hw : |(-904791809/5000000000 : ℝ)|=(904791809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(998933/1953125 : ℝ)|^4567 ≤ (42135228018489/100000000000000 : ℝ)^3543
        have hw : |(998933/1953125 : ℝ)|=(998933/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2775392353/5000000000 : ℝ)|^4567 ≤ (46823894477599/100000000000000 : ℝ)^3543
        have hw : |(2775392353/5000000000 : ℝ)|=(2775392353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s1_5 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658088869/1250000000 : ℝ)*x 0 + (-320486399/2000000000 : ℝ)*x 1 + (2775392377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658088869/1250000000 : ℝ)^4567 ≤ (43736701950177/100000000000000 : ℝ)^3543 := by
    have hnat : (658088869 : ℕ)^4567*100000000000000^3543 ≤ 43736701950177^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658088869 1250000000 43736701950177 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320486399/2000000000 : ℝ)^4567 ≤ (9439403035757/100000000000000 : ℝ)^3543 := by
    have hnat : (320486399 : ℕ)^4567*100000000000000^3543 ≤ 9439403035757^3543*2000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320486399 2000000000 9439403035757 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2775392377/5000000000 : ℝ)^4567 ≤ (46823894999531/100000000000000 : ℝ)^3543 := by
    have hnat : (2775392377 : ℕ)^4567*100000000000000^3543 ≤ 46823894999531^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775392377 5000000000 46823894999531 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658088869/1250000000 : ℝ), (-320486399/2000000000 : ℝ), (2775392377/5000000000 : ℝ)] ![(43736701950177/100000000000000 : ℝ), (9439403035757/100000000000000 : ℝ), (46823894999531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658088869/1250000000 : ℝ)|^4567 ≤ (43736701950177/100000000000000 : ℝ)^3543
        have hw : |(658088869/1250000000 : ℝ)|=(658088869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-320486399/2000000000 : ℝ)|^4567 ≤ (9439403035757/100000000000000 : ℝ)^3543
        have hw : |(-320486399/2000000000 : ℝ)|=(320486399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2775392377/5000000000 : ℝ)|^4567 ≤ (46823894999531/100000000000000 : ℝ)^3543
        have hw : |(2775392377/5000000000 : ℝ)|=(2775392377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s1_6 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264711081/10000000000 : ℝ)*x 0 + (2775392389/5000000000 : ℝ)*x 1 + (-1602431779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264711081/10000000000 : ℝ)^4567 ≤ (21868351665791/50000000000000 : ℝ)^3543 := by
    have hnat : (5264711081 : ℕ)^4567*50000000000000^3543 ≤ 21868351665791^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264711081 10000000000 21868351665791 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2775392389/5000000000 : ℝ)^4567 ≤ (46823895260497/100000000000000 : ℝ)^3543 := by
    have hnat : (2775392389 : ℕ)^4567*100000000000000^3543 ≤ 46823895260497^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775392389 5000000000 46823895260497 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1602431779/10000000000 : ℝ)^4567 ≤ (4719700697813/50000000000000 : ℝ)^3543 := by
    have hnat : (1602431779 : ℕ)^4567*50000000000000^3543 ≤ 4719700697813^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602431779 10000000000 4719700697813 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264711081/10000000000 : ℝ), (2775392389/5000000000 : ℝ), (-1602431779/10000000000 : ℝ)] ![(21868351665791/50000000000000 : ℝ), (46823895260497/100000000000000 : ℝ), (4719700697813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264711081/10000000000 : ℝ)|^4567 ≤ (21868351665791/50000000000000 : ℝ)^3543
        have hw : |(5264711081/10000000000 : ℝ)|=(5264711081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2775392389/5000000000 : ℝ)|^4567 ≤ (46823895260497/100000000000000 : ℝ)^3543
        have hw : |(2775392389/5000000000 : ℝ)|=(2775392389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1602431779/10000000000 : ℝ)|^4567 ≤ (4719700697813/50000000000000 : ℝ)^3543
        have hw : |(-1602431779/10000000000 : ℝ)|=(1602431779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s1_7 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2120910539/5000000000 : ℝ)*x 0 + (2384873113/5000000000 : ℝ)*x 1 + (1882231787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120910539/5000000000 : ℝ)^4567 ≤ (33106044909327/100000000000000 : ℝ)^3543 := by
    have hnat : (2120910539 : ℕ)^4567*100000000000000^3543 ≤ 33106044909327^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120910539 5000000000 33106044909327 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2384873113/5000000000 : ℝ)^4567 ≤ (38510023414077/100000000000000 : ℝ)^3543 := by
    have hnat : (2384873113 : ℕ)^4567*100000000000000^3543 ≤ 38510023414077^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384873113 5000000000 38510023414077 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882231787/5000000000 : ℝ)^4567 ≤ (28383931664963/100000000000000 : ℝ)^3543 := by
    have hnat : (1882231787 : ℕ)^4567*100000000000000^3543 ≤ 28383931664963^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882231787 5000000000 28383931664963 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120910539/5000000000 : ℝ), (2384873113/5000000000 : ℝ), (1882231787/5000000000 : ℝ)] ![(33106044909327/100000000000000 : ℝ), (38510023414077/100000000000000 : ℝ), (28383931664963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120910539/5000000000 : ℝ)|^4567 ≤ (33106044909327/100000000000000 : ℝ)^3543
        have hw : |(2120910539/5000000000 : ℝ)|=(2120910539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2384873113/5000000000 : ℝ)|^4567 ≤ (38510023414077/100000000000000 : ℝ)^3543
        have hw : |(2384873113/5000000000 : ℝ)|=(2384873113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1882231787/5000000000 : ℝ)|^4567 ≤ (28383931664963/100000000000000 : ℝ)^3543
        have hw : |(1882231787/5000000000 : ℝ)|=(1882231787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1535_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2519/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3119/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4327/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2519/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3119/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2519/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3119/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2519/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3119/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2519/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3119/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2519/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3119/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2519/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3119/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3119/100000 : ℝ) ^ (4565/1024 : ℝ) ≤ (3866684796729/20000000000000000000 : ℝ) := by
    have hpowers : (3119/100000 : ℝ)^4565 ≤ (3866684796729/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3119 : ℕ)^4565*20000000000000000000^1024 ≤ 3866684796729^1024*100000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3119 100000 3866684796729 20000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3119/100000 : ℝ)) (X := (3866684796729/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2519/10000 : ℝ) ^ (4565/1024 : ℝ) ≤ (8565061469186021/4000000000000000000 : ℝ) := by
    have hpowers : (2519/10000 : ℝ)^4565 ≤ (8565061469186021/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2519 : ℕ)^4565*4000000000000000000^1024 ≤ 8565061469186021^1024*10000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2519 10000 8565061469186021 4000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2519/10000 : ℝ)) (X := (8565061469186021/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000003866684796729/10000000000000000000 : ℝ) ≤ (5000000433678493/5000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (10000003866684796729/10000000000000000000 : ℝ)^1024 ≤ (5000000433678493/5000000000000000 : ℝ)^4565 := by
      have hnat : (10000003866684796729 : ℕ)^1024*5000000000000000^4565 ≤ 5000000433678493^4565*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000003866684796729 10000000000000000000 5000000433678493 5000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000433678493/5000000000000000 : ℝ)) (X := (10000003866684796729/10000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10021414587015363417/10000000000000000000 : ℝ) ≤ (2501199909498737/2500000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (10021414587015363417/10000000000000000000 : ℝ)^1024 ≤ (2501199909498737/2500000000000000 : ℝ)^4565 := by
      have hnat : (10021414587015363417 : ℕ)^1024*2500000000000000^4565 ≤ 2501199909498737^4565*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10021414587015363417 10000000000000000000 2501199909498737 2500000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501199909498737/2500000000000000 : ℝ)) (X := (10021414587015363417/10000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2008565061469186021/2000000000000000000 : ℝ) ≤ (1000959840863291/1000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (2008565061469186021/2000000000000000000 : ℝ)^1024 ≤ (1000959840863291/1000000000000000 : ℝ)^4565 := by
      have hnat : (2008565061469186021 : ℕ)^1024*1000000000000000^4565 ≤ 1000959840863291^4565*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2008565061469186021 2000000000000000000 1000959840863291 1000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000959840863291/1000000000000000 : ℝ)) (X := (2008565061469186021/2000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3866684796729/20000000000000000000 : ℝ) ≤ ((210171508963996601/210200000000000000 : ℝ)+2*(114256443761/52550000000000 : ℝ)*(3119/100000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (210171508963996601/210200000000000000 : ℝ)+2*(114256443761/52550000000000 : ℝ)*(3119/100000 : ℝ)=(5000000433678493/5000000000000000 : ℝ) by norm_num, show 1+2*(3866684796729/20000000000000000000 : ℝ)=(10000003866684796729/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8565061469186021/4000000000000000000 : ℝ)+(3866684796729/20000000000000000000 : ℝ) ≤ ((210171508963996601/210200000000000000 : ℝ)+(114256443761/52550000000000 : ℝ)*((2519/10000 : ℝ)+(3119/100000 : ℝ)))^(4565/1024 : ℝ) := by
    rw [show (210171508963996601/210200000000000000 : ℝ)+(114256443761/52550000000000 : ℝ)*((2519/10000 : ℝ)+(3119/100000 : ℝ))=(2501199909498737/2500000000000000 : ℝ) by norm_num, show 1+(8565061469186021/4000000000000000000 : ℝ)+(3866684796729/20000000000000000000 : ℝ)=(10021414587015363417/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8565061469186021/4000000000000000000 : ℝ) ≤ ((210171508963996601/210200000000000000 : ℝ)+2*(114256443761/52550000000000 : ℝ)*(2519/10000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (210171508963996601/210200000000000000 : ℝ)+2*(114256443761/52550000000000 : ℝ)*(2519/10000 : ℝ)=(1000959840863291/1000000000000000 : ℝ) by norm_num, show 1+2*(8565061469186021/4000000000000000000 : ℝ)=(2008565061469186021/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (210171508963996601/210200000000000000 : ℝ)*(X 1 0+X 2 0)+(114256443761/52550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (3119/100000 : ℝ)) (hi := (2519/10000 : ℝ)) (c := (210171508963996601/210200000000000000 : ℝ)) (alpha := (114256443761/52550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (210171508963996601/210200000000000000 : ℝ)*(X 0 1+X 2 1)+(114256443761/52550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (3119/100000 : ℝ)) (hi := (2519/10000 : ℝ)) (c := (210171508963996601/210200000000000000 : ℝ)) (alpha := (114256443761/52550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (210171508963996601/210200000000000000 : ℝ)*(X 0 2+X 1 2)+(114256443761/52550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (3119/100000 : ℝ)) (hi := (2519/10000 : ℝ)) (c := (210171508963996601/210200000000000000 : ℝ)) (alpha := (114256443761/52550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-36186443/200000000 : ℝ)*X 0 0+(2777844497/5000000000 : ℝ)*X 0 1+(638713451/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((672811607/1250000000 : ℝ)*X 1 0+(-2043508857/10000000000 : ℝ)*X 1 1+(5109708141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((336405847/625000000 : ℝ)*X 2 0+(2554853641/5000000000 : ℝ)*X 2 1+(-2043509057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((424121749/1000000000 : ℝ)*X 0 0+(1876581649/5000000000 : ℝ)*X 0 1+(95617489/200000000 : ℝ)*X 0 2+(424121749/1000000000 : ℝ)*X 1 0+(1876581649/5000000000 : ℝ)*X 1 1+(95617489/200000000 : ℝ)*X 1 2+(424121749/1000000000 : ℝ)*X 2 0+(1876581649/5000000000 : ℝ)*X 2 1+(95617489/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-904791809/5000000000 : ℝ)*X 0 0+(998933/1953125 : ℝ)*X 0 1+(2775392353/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((658088869/1250000000 : ℝ)*X 1 0+(-320486399/2000000000 : ℝ)*X 1 1+(2775392377/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5264711081/10000000000 : ℝ)*X 2 0+(2775392389/5000000000 : ℝ)*X 2 1+(-1602431779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2120910539/5000000000 : ℝ)*X 0 0+(2384873113/5000000000 : ℝ)*X 0 1+(1882231787/5000000000 : ℝ)*X 0 2+(2120910539/5000000000 : ℝ)*X 1 0+(2384873113/5000000000 : ℝ)*X 1 1+(1882231787/5000000000 : ℝ)*X 1 2+(2120910539/5000000000 : ℝ)*X 2 0+(2384873113/5000000000 : ℝ)*X 2 1+(1882231787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20781131243767635072638043/2627500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1161307319/100000000000000 : ℝ)*(base19) + (1354056209/100000000000000 : ℝ)*(base23) + (43405843/20000000000000 : ℝ)*(upper3) + (52314783/100000000000000 : ℝ)*(upper4) + (95882753/100000000000000 : ℝ)*(upper5) + (803828066169581/50000000000000 : ℝ)*(major0) + (803828066169581/50000000000000 : ℝ)*(major1) + (803828066169581/50000000000000 : ℝ)*(major2) + (1121128495282871/50000000000000 : ℝ)*(sp0) + (1121133246994297/50000000000000 : ℝ)*(sp1) + (448453260247941/20000000000000 : ℝ)*(sp2) + (973039583110219/100000000000000 : ℝ)*(sp3) + (10664730171/100000000000000 : ℝ)*(sp4) + (1190658971/25000000000000 : ℝ)*(sp7) + (973044345746103/100000000000000 : ℝ)*(f.failure) + (1121133827647957/50000000000000 : ℝ)*(f.sum) + (4901939106357/656875000000000000000000000 : ℝ)*base66 + (70509950304381819/10510000000000000000000000000000 : ℝ)*base68 + (28386584477878181/10510000000000000000000000000000 : ℝ)*base69 + (122179190990101819/10510000000000000000000000000000 : ℝ)*base72 + (277536588209/82109375000000000000000000 : ℝ)*base74 + (7324439527041819/10510000000000000000000000000000 : ℝ)*base76 + (97148550775061819/10510000000000000000000000000000 : ℝ)*base78 + (108309881056401819/10510000000000000000000000000000 : ℝ)*base80 + (21471242457409/5255000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13901623/2000000000000000000000 : ℝ)*base89 + (13901623/2000000000000000000000 : ℝ)*base91 + (13901623/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24841153434233791304475213/2627500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (777438203/50000000000000 : ℝ)*(base19) + (890294893/50000000000000 : ℝ)*(base23) + (23999587/10000000000000 : ℝ)*(upper3) + (12148673/20000000000000 : ℝ)*(lower4) + (208083807/100000000000000 : ℝ)*(upper5) + (410877534085657/25000000000000 : ℝ)*(major0) + (410877534085657/25000000000000 : ℝ)*(major1) + (410877534085657/25000000000000 : ℝ)*(major2) + (10492622287/100000000000000 : ℝ)*(sp1) + (12913805031/100000000000000 : ℝ)*(sp2) + (2292274742333909/100000000000000 : ℝ)*(sp4) + (143266418427201/6250000000000 : ℝ)*(sp5) + (573065011984773/25000000000000 : ℝ)*(sp6) + (994745215208261/100000000000000 : ℝ)*(sp7) + (994745215208261/100000000000000 : ℝ)*(f.failure) + (2292274742333909/100000000000000 : ℝ)*(f.sum) + (2397021713541/1313750000000000000000000000 : ℝ)*base66 + (24585088349870143/5255000000000000000000000000000 : ℝ)*base68 + (21803779450080143/5255000000000000000000000000000 : ℝ)*base70 + (52138856004050143/5255000000000000000000000000000 : ℝ)*base72 + (1761039370531/5255000000000000000000000000 : ℝ)*base73 + (16625710427215143/5255000000000000000000000000000 : ℝ)*base76 + (20681223975350143/5255000000000000000000000000000 : ℝ)*base78 + (41043226412760143/5255000000000000000000000000000 : ℝ)*base80 + (3509585173829/5255000000000000000000000000 : ℝ)*base82 + (1629499/2000000000000000000000 : ℝ)*base90 + (1629499/2000000000000000000000 : ℝ)*base92 + (1629499/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1535_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2519/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3119/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4327/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1535_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1535_s2_0 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1831318319/10000000000 : ℝ)*x 0 + (5450914391/10000000000 : ℝ)*x 1 + (81253123/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1831318319/10000000000 : ℝ)^4567 ≤ (2242422255723/20000000000000 : ℝ)^3543 := by
    have hnat : (1831318319 : ℕ)^4567*20000000000000^3543 ≤ 2242422255723^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831318319 10000000000 2242422255723 20000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450914391/10000000000 : ℝ)^4567 ≤ (11435195282577/25000000000000 : ℝ)^3543 := by
    have hnat : (5450914391 : ℕ)^4567*25000000000000^3543 ≤ 11435195282577^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450914391 10000000000 11435195282577 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81253123/156250000 : ℝ)^4567 ≤ (10761776893583/25000000000000 : ℝ)^3543 := by
    have hnat : (81253123 : ℕ)^4567*25000000000000^3543 ≤ 10761776893583^3543*156250000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81253123 156250000 10761776893583 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1831318319/10000000000 : ℝ), (5450914391/10000000000 : ℝ), (81253123/156250000 : ℝ)] ![(2242422255723/20000000000000 : ℝ), (11435195282577/25000000000000 : ℝ), (10761776893583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1831318319/10000000000 : ℝ)|^4567 ≤ (2242422255723/20000000000000 : ℝ)^3543
        have hw : |(-1831318319/10000000000 : ℝ)|=(1831318319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450914391/10000000000 : ℝ)|^4567 ≤ (11435195282577/25000000000000 : ℝ)^3543
        have hw : |(5450914391/10000000000 : ℝ)|=(5450914391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81253123/156250000 : ℝ)|^4567 ≤ (10761776893583/25000000000000 : ℝ)^3543
        have hw : |(81253123/156250000 : ℝ)|=(81253123/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s2_1 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669460927/1250000000 : ℝ)*x 0 + (-980107689/5000000000 : ℝ)*x 1 + (650025013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669460927/1250000000 : ℝ)^4567 ≤ (44713352461069/100000000000000 : ℝ)^3543 := by
    have hnat : (669460927 : ℕ)^4567*100000000000000^3543 ≤ 44713352461069^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669460927 1250000000 44713352461069 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980107689/5000000000 : ℝ)^4567 ≤ (1529942184533/12500000000000 : ℝ)^3543 := by
    have hnat : (980107689 : ℕ)^4567*12500000000000^3543 ≤ 1529942184533^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980107689 5000000000 1529942184533 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650025013/1250000000 : ℝ)^4567 ≤ (21523555024941/50000000000000 : ℝ)^3543 := by
    have hnat : (650025013 : ℕ)^4567*50000000000000^3543 ≤ 21523555024941^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650025013 1250000000 21523555024941 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669460927/1250000000 : ℝ), (-980107689/5000000000 : ℝ), (650025013/1250000000 : ℝ)] ![(44713352461069/100000000000000 : ℝ), (1529942184533/12500000000000 : ℝ), (21523555024941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669460927/1250000000 : ℝ)|^4567 ≤ (44713352461069/100000000000000 : ℝ)^3543
        have hw : |(669460927/1250000000 : ℝ)|=(669460927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-980107689/5000000000 : ℝ)|^4567 ≤ (1529942184533/12500000000000 : ℝ)^3543
        have hw : |(-980107689/5000000000 : ℝ)|=(980107689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(650025013/1250000000 : ℝ)|^4567 ≤ (21523555024941/50000000000000 : ℝ)^3543
        have hw : |(650025013/1250000000 : ℝ)|=(650025013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s2_2 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267784357/500000000 : ℝ)*x 0 + (650025023/1250000000 : ℝ)*x 1 + (-1960215641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267784357/500000000 : ℝ)^4567 ≤ (44713349490833/100000000000000 : ℝ)^3543 := by
    have hnat : (267784357 : ℕ)^4567*100000000000000^3543 ≤ 44713349490833^3543*500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267784357 500000000 44713349490833 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650025023/1250000000 : ℝ)^4567 ≤ (269044443147/625000000000 : ℝ)^3543 := by
    have hnat : (650025023 : ℕ)^4567*625000000000^3543 ≤ 269044443147^3543*1250000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650025023 1250000000 269044443147 625000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1960215641/10000000000 : ℝ)^4567 ≤ (12239539593049/100000000000000 : ℝ)^3543 := by
    have hnat : (1960215641 : ℕ)^4567*100000000000000^3543 ≤ 12239539593049^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960215641 10000000000 12239539593049 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267784357/500000000 : ℝ), (650025023/1250000000 : ℝ), (-1960215641/10000000000 : ℝ)] ![(44713349490833/100000000000000 : ℝ), (269044443147/625000000000 : ℝ), (12239539593049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267784357/500000000 : ℝ)|^4567 ≤ (44713349490833/100000000000000 : ℝ)^3543
        have hw : |(267784357/500000000 : ℝ)|=(267784357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(650025023/1250000000 : ℝ)|^4567 ≤ (269044443147/625000000000 : ℝ)^3543
        have hw : |(650025023/1250000000 : ℝ)|=(650025023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1960215641/10000000000 : ℝ)|^4567 ≤ (12239539593049/100000000000000 : ℝ)^3543
        have hw : |(-1960215641/10000000000 : ℝ)|=(1960215641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s2_3 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2128535451/5000000000 : ℝ)*x 0 + (3976359149/10000000000 : ℝ)*x 1 + (4554099101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128535451/5000000000 : ℝ)^4567 ≤ (33259543723121/100000000000000 : ℝ)^3543 := by
    have hnat : (2128535451 : ℕ)^4567*100000000000000^3543 ≤ 33259543723121^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128535451 5000000000 33259543723121 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3976359149/10000000000 : ℝ)^4567 ≤ (15229957624471/50000000000000 : ℝ)^3543 := by
    have hnat : (3976359149 : ℕ)^4567*50000000000000^3543 ≤ 15229957624471^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3976359149 10000000000 15229957624471 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4554099101/10000000000 : ℝ)^4567 ≤ (18140270504779/50000000000000 : ℝ)^3543 := by
    have hnat : (4554099101 : ℕ)^4567*50000000000000^3543 ≤ 18140270504779^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554099101 10000000000 18140270504779 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128535451/5000000000 : ℝ), (3976359149/10000000000 : ℝ), (4554099101/10000000000 : ℝ)] ![(33259543723121/100000000000000 : ℝ), (15229957624471/50000000000000 : ℝ), (18140270504779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128535451/5000000000 : ℝ)|^4567 ≤ (33259543723121/100000000000000 : ℝ)^3543
        have hw : |(2128535451/5000000000 : ℝ)|=(2128535451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3976359149/10000000000 : ℝ)|^4567 ≤ (15229957624471/50000000000000 : ℝ)^3543
        have hw : |(3976359149/10000000000 : ℝ)|=(3976359149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4554099101/10000000000 : ℝ)|^4567 ≤ (18140270504779/50000000000000 : ℝ)^3543
        have hw : |(4554099101/10000000000 : ℝ)|=(4554099101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s2_4 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1831365213/10000000000 : ℝ)*x 0 + (2600867221/5000000000 : ℝ)*x 1 + (2724683111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1831365213/10000000000 : ℝ)^4567 ≤ (2803120341079/25000000000000 : ℝ)^3543 := by
    have hnat : (1831365213 : ℕ)^4567*25000000000000^3543 ≤ 2803120341079^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831365213 10000000000 2803120341079 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2600867221/5000000000 : ℝ)^4567 ≤ (5382935358141/12500000000000 : ℝ)^3543 := by
    have hnat : (2600867221 : ℕ)^4567*12500000000000^3543 ≤ 5382935358141^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600867221 5000000000 5382935358141 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724683111/5000000000 : ℝ)^4567 ≤ (22862017882713/50000000000000 : ℝ)^3543 := by
    have hnat : (2724683111 : ℕ)^4567*50000000000000^3543 ≤ 22862017882713^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724683111 5000000000 22862017882713 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1831365213/10000000000 : ℝ), (2600867221/5000000000 : ℝ), (2724683111/5000000000 : ℝ)] ![(2803120341079/25000000000000 : ℝ), (5382935358141/12500000000000 : ℝ), (22862017882713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1831365213/10000000000 : ℝ)|^4567 ≤ (2803120341079/25000000000000 : ℝ)^3543
        have hw : |(-1831365213/10000000000 : ℝ)|=(1831365213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2600867221/5000000000 : ℝ)|^4567 ≤ (5382935358141/12500000000000 : ℝ)^3543
        have hw : |(2600867221/5000000000 : ℝ)|=(2600867221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724683111/5000000000 : ℝ)|^4567 ≤ (22862017882713/50000000000000 : ℝ)^3543
        have hw : |(2724683111/5000000000 : ℝ)|=(2724683111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s2_5 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644820907/5000000000 : ℝ)*x 0 + (-1711049383/10000000000 : ℝ)*x 1 + (5449365937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644820907/5000000000 : ℝ)^4567 ≤ (44003858248149/100000000000000 : ℝ)^3543 := by
    have hnat : (2644820907 : ℕ)^4567*100000000000000^3543 ≤ 44003858248149^3543*5000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644820907 5000000000 44003858248149 100000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1711049383/10000000000 : ℝ)^4567 ≤ (5136054525877/50000000000000 : ℝ)^3543 := by
    have hnat : (1711049383 : ℕ)^4567*50000000000000^3543 ≤ 5136054525877^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711049383 10000000000 5136054525877 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449365937/10000000000 : ℝ)^4567 ≤ (11431008170731/25000000000000 : ℝ)^3543 := by
    have hnat : (5449365937 : ℕ)^4567*25000000000000^3543 ≤ 11431008170731^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449365937 10000000000 11431008170731 25000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644820907/5000000000 : ℝ), (-1711049383/10000000000 : ℝ), (5449365937/10000000000 : ℝ)] ![(44003858248149/100000000000000 : ℝ), (5136054525877/50000000000000 : ℝ), (11431008170731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644820907/5000000000 : ℝ)|^4567 ≤ (44003858248149/100000000000000 : ℝ)^3543
        have hw : |(2644820907/5000000000 : ℝ)|=(2644820907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1711049383/10000000000 : ℝ)|^4567 ≤ (5136054525877/50000000000000 : ℝ)^3543
        have hw : |(-1711049383/10000000000 : ℝ)|=(1711049383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449365937/10000000000 : ℝ)|^4567 ≤ (11431008170731/25000000000000 : ℝ)^3543
        have hw : |(5449365937/10000000000 : ℝ)|=(5449365937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s2_6 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289641399/10000000000 : ℝ)*x 0 + (5449366151/10000000000 : ℝ)*x 1 + (-85552483/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289641399/10000000000 : ℝ)^4567 ≤ (22001926899011/50000000000000 : ℝ)^3543 := by
    have hnat : (5289641399 : ℕ)^4567*50000000000000^3543 ≤ 22001926899011^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289641399 10000000000 22001926899011 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5449366151/10000000000 : ℝ)^4567 ≤ (178609511709/390625000000 : ℝ)^3543 := by
    have hnat : (5449366151 : ℕ)^4567*390625000000^3543 ≤ 178609511709^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449366151 10000000000 178609511709 390625000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85552483/500000000 : ℝ)^4567 ≤ (256802779883/2500000000000 : ℝ)^3543 := by
    have hnat : (85552483 : ℕ)^4567*2500000000000^3543 ≤ 256802779883^3543*500000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85552483 500000000 256802779883 2500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289641399/10000000000 : ℝ), (5449366151/10000000000 : ℝ), (-85552483/500000000 : ℝ)] ![(22001926899011/50000000000000 : ℝ), (178609511709/390625000000 : ℝ), (256802779883/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289641399/10000000000 : ℝ)|^4567 ≤ (22001926899011/50000000000000 : ℝ)^3543
        have hw : |(5289641399/10000000000 : ℝ)|=(5289641399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5449366151/10000000000 : ℝ)|^4567 ≤ (178609511709/390625000000 : ℝ)^3543
        have hw : |(5449366151/10000000000 : ℝ)|=(5449366151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85552483/500000000 : ℝ)|^4567 ≤ (256802779883/2500000000000 : ℝ)^3543
        have hw : |(-85552483/500000000 : ℝ)|=(85552483/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1535_s2_7 (p : ℝ) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (425717823/1000000000 : ℝ)*x 0 + (4550563407/10000000000 : ℝ)*x 1 + (3979925887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425717823/1000000000 : ℝ)^4567 ≤ (4157578076137/12500000000000 : ℝ)^3543 := by
    have hnat : (425717823 : ℕ)^4567*12500000000000^3543 ≤ 4157578076137^3543*1000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425717823 1000000000 4157578076137 12500000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4550563407/10000000000 : ℝ)^4567 ≤ (18122118396411/50000000000000 : ℝ)^3543 := by
    have hnat : (4550563407 : ℕ)^4567*50000000000000^3543 ≤ 18122118396411^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4550563407 10000000000 18122118396411 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3979925887/10000000000 : ℝ)^4567 ≤ (15247569290399/50000000000000 : ℝ)^3543 := by
    have hnat : (3979925887 : ℕ)^4567*50000000000000^3543 ≤ 15247569290399^3543*10000000000^4567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979925887 10000000000 15247569290399 50000000000000 4567 3543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4567/1024 : ℝ)) 4567 3543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425717823/1000000000 : ℝ), (4550563407/10000000000 : ℝ), (3979925887/10000000000 : ℝ)] ![(4157578076137/12500000000000 : ℝ), (18122118396411/50000000000000 : ℝ), (15247569290399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425717823/1000000000 : ℝ)|^4567 ≤ (4157578076137/12500000000000 : ℝ)^3543
        have hw : |(425717823/1000000000 : ℝ)|=(425717823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4550563407/10000000000 : ℝ)|^4567 ≤ (18122118396411/50000000000000 : ℝ)^3543
        have hw : |(4550563407/10000000000 : ℝ)|=(4550563407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3979925887/10000000000 : ℝ)|^4567 ≤ (15247569290399/50000000000000 : ℝ)^3543
        have hw : |(3979925887/10000000000 : ℝ)|=(3979925887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1535_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4327/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2121/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3183/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4327/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4327/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4327/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4327/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4327/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4327/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4327/50000 : ℝ) ^ (4565/1024 : ℝ) ≤ (182854055298929/10000000000000000000 : ℝ) := by
    have hpowers : (4327/50000 : ℝ)^4565 ≤ (182854055298929/10000000000000000000 : ℝ)^1024 := by
      have hnat : (4327 : ℕ)^4565*10000000000000000000^1024 ≤ 182854055298929^1024*50000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4327 50000 182854055298929 10000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4327/50000 : ℝ)) (X := (182854055298929/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4523/25000 : ℝ) ^ (4565/1024 : ℝ) ≤ (48963152102185677/100000000000000000000 : ℝ) := by
    have hpowers : (4523/25000 : ℝ)^4565 ≤ (48963152102185677/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4523 : ℕ)^4565*100000000000000000000^1024 ≤ 48963152102185677^1024*25000^4565 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4523 25000 48963152102185677 100000000000000000000 4565 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4523/25000 : ℝ)) (X := (48963152102185677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000182854055298929/5000000000000000000 : ℝ) ≤ (5000041016406767/5000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (5000182854055298929/5000000000000000000 : ℝ)^1024 ≤ (5000041016406767/5000000000000000 : ℝ)^4565 := by
      have hnat : (5000182854055298929 : ℕ)^1024*5000000000000000^4565 ≤ 5000041016406767^4565*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000182854055298929 5000000000000000000 5000041016406767 5000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000041016406767/5000000000000000 : ℝ)) (X := (5000182854055298929/5000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050791692655174967/100000000000000000000 : ℝ) ≤ (5000569555867309/5000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (100050791692655174967/100000000000000000000 : ℝ)^1024 ≤ (5000569555867309/5000000000000000 : ℝ)^4565 := by
      have hnat : (100050791692655174967 : ℕ)^1024*5000000000000000^4565 ≤ 5000569555867309^4565*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050791692655174967 100000000000000000000 5000569555867309 5000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000569555867309/5000000000000000 : ℝ)) (X := (100050791692655174967/100000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048963152102185677/50000000000000000000 : ℝ) ≤ (5001098095327851/5000000000000000 : ℝ) ^ (4565/1024 : ℝ) := by
    have hpowers : (50048963152102185677/50000000000000000000 : ℝ)^1024 ≤ (5001098095327851/5000000000000000 : ℝ)^4565 := by
      have hnat : (50048963152102185677 : ℕ)^1024*5000000000000000^4565 ≤ 5001098095327851^4565*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048963152102185677 50000000000000000000 5001098095327851 5000000000000000 1024 4565 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001098095327851/5000000000000000 : ℝ)) (X := (50048963152102185677/50000000000000000000 : ℝ)) (by norm_num) 4565 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(182854055298929/10000000000000000000 : ℝ) ≤ ((4718123915186400601/4719000000000000000 : ℝ)+2*(264269730271/235950000000000 : ℝ)*(4327/50000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (4718123915186400601/4719000000000000000 : ℝ)+2*(264269730271/235950000000000 : ℝ)*(4327/50000 : ℝ)=(5000041016406767/5000000000000000 : ℝ) by norm_num, show 1+2*(182854055298929/10000000000000000000 : ℝ)=(5000182854055298929/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48963152102185677/100000000000000000000 : ℝ)+(182854055298929/10000000000000000000 : ℝ) ≤ ((4718123915186400601/4719000000000000000 : ℝ)+(264269730271/235950000000000 : ℝ)*((4523/25000 : ℝ)+(4327/50000 : ℝ)))^(4565/1024 : ℝ) := by
    rw [show (4718123915186400601/4719000000000000000 : ℝ)+(264269730271/235950000000000 : ℝ)*((4523/25000 : ℝ)+(4327/50000 : ℝ))=(5000569555867309/5000000000000000 : ℝ) by norm_num, show 1+(48963152102185677/100000000000000000000 : ℝ)+(182854055298929/10000000000000000000 : ℝ)=(100050791692655174967/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48963152102185677/100000000000000000000 : ℝ) ≤ ((4718123915186400601/4719000000000000000 : ℝ)+2*(264269730271/235950000000000 : ℝ)*(4523/25000 : ℝ))^(4565/1024 : ℝ) := by
    rw [show (4718123915186400601/4719000000000000000 : ℝ)+2*(264269730271/235950000000000 : ℝ)*(4523/25000 : ℝ)=(5001098095327851/5000000000000000 : ℝ) by norm_num, show 1+2*(48963152102185677/100000000000000000000 : ℝ)=(50048963152102185677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4718123915186400601/4719000000000000000 : ℝ)*(X 1 0+X 2 0)+(264269730271/235950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (4327/50000 : ℝ)) (hi := (4523/25000 : ℝ)) (c := (4718123915186400601/4719000000000000000 : ℝ)) (alpha := (264269730271/235950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4718123915186400601/4719000000000000000 : ℝ)*(X 0 1+X 2 1)+(264269730271/235950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (4327/50000 : ℝ)) (hi := (4523/25000 : ℝ)) (c := (4718123915186400601/4719000000000000000 : ℝ)) (alpha := (264269730271/235950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4718123915186400601/4719000000000000000 : ℝ)*(X 0 2+X 1 2)+(264269730271/235950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4565/1024 : ℝ)) (lo := (4327/50000 : ℝ)) (hi := (4523/25000 : ℝ)) (c := (4718123915186400601/4719000000000000000 : ℝ)) (alpha := (264269730271/235950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1831318319/10000000000 : ℝ)*X 0 0+(5450914391/10000000000 : ℝ)*X 0 1+(81253123/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669460927/1250000000 : ℝ)*X 1 0+(-980107689/5000000000 : ℝ)*X 1 1+(650025013/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267784357/500000000 : ℝ)*X 2 0+(650025023/1250000000 : ℝ)*X 2 1+(-1960215641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2128535451/5000000000 : ℝ)*X 0 0+(3976359149/10000000000 : ℝ)*X 0 1+(4554099101/10000000000 : ℝ)*X 0 2+(2128535451/5000000000 : ℝ)*X 1 0+(3976359149/10000000000 : ℝ)*X 1 1+(4554099101/10000000000 : ℝ)*X 1 2+(2128535451/5000000000 : ℝ)*X 2 0+(3976359149/10000000000 : ℝ)*X 2 1+(4554099101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1831365213/10000000000 : ℝ)*X 0 0+(2600867221/5000000000 : ℝ)*X 0 1+(2724683111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644820907/5000000000 : ℝ)*X 1 0+(-1711049383/10000000000 : ℝ)*X 1 1+(5449365937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289641399/10000000000 : ℝ)*X 2 0+(5449366151/10000000000 : ℝ)*X 2 1+(-85552483/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((425717823/1000000000 : ℝ)*X 0 0+(4550563407/10000000000 : ℝ)*X 0 1+(3979925887/10000000000 : ℝ)*X 0 2+(425717823/1000000000 : ℝ)*X 1 0+(4550563407/10000000000 : ℝ)*X 1 1+(3979925887/10000000000 : ℝ)*X 1 2+(425717823/1000000000 : ℝ)*X 2 0+(4550563407/10000000000 : ℝ)*X 2 1+(3979925887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1535_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129874311965535329130146003/19662500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (611572767/50000000000000 : ℝ)*(base19) + (537977249/50000000000000 : ℝ)*(base23) + (20208407/100000000000000 : ℝ)*(lower2) + (106948283/50000000000000 : ℝ)*(upper3) + (3216503/6250000000000 : ℝ)*(lower4) + (714942330891703/25000000000000 : ℝ)*(major0) + (714942330891703/25000000000000 : ℝ)*(major1) + (714942330891703/25000000000000 : ℝ)*(major2) + (1994312862551243/50000000000000 : ℝ)*(sp0) + (498580399162461/12500000000000 : ℝ)*(sp1) + (997160835122681/25000000000000 : ℝ)*(sp2) + (865443772880479/50000000000000 : ℝ)*(sp3) + (3738268547/20000000000000 : ℝ)*(sp4) + (6464754837/100000000000000 : ℝ)*(sp7) + (346178802103159/20000000000000 : ℝ)*(f.failure) + (1994322208222611/50000000000000 : ℝ)*(f.sum) + (82771944920911/23595000000000000000000000000 : ℝ)*base66 + (101391198559400499/39325000000000000000000000000000 : ℝ)*base68 + (143399494396050499/39325000000000000000000000000000 : ℝ)*base70 + (382748332648074501/39325000000000000000000000000000 : ℝ)*base71 + (101625017659411/23595000000000000000000000000 : ℝ)*base74 + (568997790697800499/39325000000000000000000000000000 : ℝ)*base76 + (689949703304325499/39325000000000000000000000000000 : ℝ)*base78 + (101846759506599501/39325000000000000000000000000000 : ℝ)*base79 + (10104438787769/23595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3593719/400000000000000000000 : ℝ)*base89 + (3593719/400000000000000000000 : ℝ)*base91 + (3593719/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2100580888973471640488813/446875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1293361873/100000000000000 : ℝ)*(base19) + (506728837/50000000000000 : ℝ)*(base23) + (68135351/100000000000000 : ℝ)*(upper2) + (7058193/50000000000000 : ℝ)*(upper3) + (201789491/100000000000000 : ℝ)*(upper5) + (180958717410259/6250000000000 : ℝ)*(major0) + (180958717410259/6250000000000 : ℝ)*(major1) + (180958717410259/6250000000000 : ℝ)*(major2) + (9217856629/50000000000000 : ℝ)*(sp1) + (443042661/4000000000000 : ℝ)*(sp2) + (126195491310109/3125000000000 : ℝ)*(sp4) + (1009558998212089/25000000000000 : ℝ)*(sp5) + (504780454049911/12500000000000 : ℝ)*(sp6) + (438105769629527/25000000000000 : ℝ)*(sp7) + (438105769629527/25000000000000 : ℝ)*(f.failure) + (126195491310109/3125000000000 : ℝ)*(f.sum) + (899839163759/2949375000000000000000000000 : ℝ)*base66 + (12206927997076447/9831250000000000000000000000000 : ℝ)*base68 + (65258677891076447/9831250000000000000000000000000 : ℝ)*base70 + (14787240821451447/9831250000000000000000000000000 : ℝ)*base72 + (41215999341017/5898750000000000000000000000 : ℝ)*base73 + (45429106297101447/9831250000000000000000000000000 : ℝ)*base76 + (29693316202076447/9831250000000000000000000000000 : ℝ)*base78 + (24890631330323553/9831250000000000000000000000000 : ℝ)*base79 + (12108218809403/23595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (906793/500000000000000000000 : ℝ)*base90 + (906793/500000000000000000000 : ℝ)*base92 + (906793/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1535_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4327/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3183/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1535_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1535_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3183/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1535_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1535_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1535_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4565/1024 : ℝ) ≤ p) (hpb : p ≤ (4567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (33043841/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2121/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3183/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1535_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

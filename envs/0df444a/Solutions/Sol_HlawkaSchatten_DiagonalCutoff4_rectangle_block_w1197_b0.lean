-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1197_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:01:58.938595+00:00
-- url     : https://prove2.me/submissions/cbb0b88a-f0cd-4f7b-a8d6-310172ff1d62

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
theorem support_rectangle_w1197_s0_0 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-468631207/2500000000 : ℝ)*x 0 + (3020852547/5000000000 : ℝ)*x 1 + (38299111/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (468631207/2500000000 : ℝ)^4195 ≤ (5458313611511/50000000000000 : ℝ)^3171 := by
    have hnat : (468631207 : ℕ)^4195*50000000000000^3171 ≤ 5458313611511^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468631207 2500000000 5458313611511 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3020852547/5000000000 : ℝ)^4195 ≤ (51344050712691/100000000000000 : ℝ)^3171 := by
    have hnat : (3020852547 : ℕ)^4195*100000000000000^3171 ≤ 51344050712691^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020852547 5000000000 51344050712691 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38299111/80000000 : ℝ)^4195 ≤ (37739322046917/100000000000000 : ℝ)^3171 := by
    have hnat : (38299111 : ℕ)^4195*100000000000000^3171 ≤ 37739322046917^3171*80000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38299111 80000000 37739322046917 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-468631207/2500000000 : ℝ), (3020852547/5000000000 : ℝ), (38299111/80000000 : ℝ)] ![(5458313611511/50000000000000 : ℝ), (51344050712691/100000000000000 : ℝ), (37739322046917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-468631207/2500000000 : ℝ)|^4195 ≤ (5458313611511/50000000000000 : ℝ)^3171
        have hw : |(-468631207/2500000000 : ℝ)|=(468631207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3020852547/5000000000 : ℝ)|^4195 ≤ (51344050712691/100000000000000 : ℝ)^3171
        have hw : |(3020852547/5000000000 : ℝ)|=(3020852547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(38299111/80000000 : ℝ)|^4195 ≤ (37739322046917/100000000000000 : ℝ)^3171
        have hw : |(38299111/80000000 : ℝ)|=(38299111/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s0_1 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5513694597/10000000000 : ℝ)*x 0 + (-2592822477/10000000000 : ℝ)*x 1 + (2393694409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513694597/10000000000 : ℝ)^4195 ≤ (9098665420333/20000000000000 : ℝ)^3171 := by
    have hnat : (5513694597 : ℕ)^4195*20000000000000^3171 ≤ 9098665420333^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513694597 10000000000 9098665420333 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592822477/10000000000 : ℝ)^4195 ≤ (16767351427577/100000000000000 : ℝ)^3171 := by
    have hnat : (2592822477 : ℕ)^4195*100000000000000^3171 ≤ 16767351427577^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592822477 10000000000 16767351427577 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2393694409/5000000000 : ℝ)^4195 ≤ (117935379539/312500000000 : ℝ)^3171 := by
    have hnat : (2393694409 : ℕ)^4195*312500000000^3171 ≤ 117935379539^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393694409 5000000000 117935379539 312500000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513694597/10000000000 : ℝ), (-2592822477/10000000000 : ℝ), (2393694409/5000000000 : ℝ)] ![(9098665420333/20000000000000 : ℝ), (16767351427577/100000000000000 : ℝ), (117935379539/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513694597/10000000000 : ℝ)|^4195 ≤ (9098665420333/20000000000000 : ℝ)^3171
        have hw : |(5513694597/10000000000 : ℝ)|=(5513694597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2592822477/10000000000 : ℝ)|^4195 ≤ (16767351427577/100000000000000 : ℝ)^3171
        have hw : |(-2592822477/10000000000 : ℝ)|=(2592822477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2393694409/5000000000 : ℝ)|^4195 ≤ (117935379539/312500000000 : ℝ)^3171
        have hw : |(2393694409/5000000000 : ℝ)|=(2393694409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s0_2 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5513694963/10000000000 : ℝ)*x 0 + (4787388479/10000000000 : ℝ)*x 1 + (-2592822423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513694963/10000000000 : ℝ)^4195 ≤ (5686666387089/12500000000000 : ℝ)^3171 := by
    have hnat : (5513694963 : ℕ)^4195*12500000000000^3171 ≤ 5686666387089^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513694963 10000000000 5686666387089 12500000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4787388479/10000000000 : ℝ)^4195 ≤ (37739317917143/100000000000000 : ℝ)^3171 := by
    have hnat : (4787388479 : ℕ)^4195*100000000000000^3171 ≤ 37739317917143^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787388479 10000000000 37739317917143 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592822423/10000000000 : ℝ)^4195 ≤ (16767350965599/100000000000000 : ℝ)^3171 := by
    have hnat : (2592822423 : ℕ)^4195*100000000000000^3171 ≤ 16767350965599^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592822423 10000000000 16767350965599 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513694963/10000000000 : ℝ), (4787388479/10000000000 : ℝ), (-2592822423/10000000000 : ℝ)] ![(5686666387089/12500000000000 : ℝ), (37739317917143/100000000000000 : ℝ), (16767350965599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513694963/10000000000 : ℝ)|^4195 ≤ (5686666387089/12500000000000 : ℝ)^3171
        have hw : |(5513694963/10000000000 : ℝ)|=(5513694963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4787388479/10000000000 : ℝ)|^4195 ≤ (37739317917143/100000000000000 : ℝ)^3171
        have hw : |(4787388479/10000000000 : ℝ)|=(4787388479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2592822423/10000000000 : ℝ)|^4195 ≤ (16767350965599/100000000000000 : ℝ)^3171
        have hw : |(-2592822423/10000000000 : ℝ)|=(2592822423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s0_3 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2098289469/5000000000 : ℝ)*x 0 + (779666653/2500000000 : ℝ)*x 1 + (2820522841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098289469/5000000000 : ℝ)^4195 ≤ (15852155473977/50000000000000 : ℝ)^3171 := by
    have hnat : (2098289469 : ℕ)^4195*50000000000000^3171 ≤ 15852155473977^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098289469 5000000000 15852155473977 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779666653/2500000000 : ℝ)^4195 ≤ (4281422626827/20000000000000 : ℝ)^3171 := by
    have hnat : (779666653 : ℕ)^4195*20000000000000^3171 ≤ 4281422626827^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779666653 2500000000 4281422626827 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2820522841/5000000000 : ℝ)^4195 ≤ (46888575907617/100000000000000 : ℝ)^3171 := by
    have hnat : (2820522841 : ℕ)^4195*100000000000000^3171 ≤ 46888575907617^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820522841 5000000000 46888575907617 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098289469/5000000000 : ℝ), (779666653/2500000000 : ℝ), (2820522841/5000000000 : ℝ)] ![(15852155473977/50000000000000 : ℝ), (4281422626827/20000000000000 : ℝ), (46888575907617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098289469/5000000000 : ℝ)|^4195 ≤ (15852155473977/50000000000000 : ℝ)^3171
        have hw : |(2098289469/5000000000 : ℝ)|=(2098289469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779666653/2500000000 : ℝ)|^4195 ≤ (4281422626827/20000000000000 : ℝ)^3171
        have hw : |(779666653/2500000000 : ℝ)|=(779666653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2820522841/5000000000 : ℝ)|^4195 ≤ (46888575907617/100000000000000 : ℝ)^3171
        have hw : |(2820522841/5000000000 : ℝ)|=(2820522841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s0_4 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1879510489/10000000000 : ℝ)*x 0 + (38557733/80000000 : ℝ)*x 1 + (6008236947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879510489/10000000000 : ℝ)^4195 ≤ (342345460021/3125000000000 : ℝ)^3171 := by
    have hnat : (1879510489 : ℕ)^4195*3125000000000^3171 ≤ 342345460021^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879510489 10000000000 342345460021 3125000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38557733/80000000 : ℝ)^4195 ≤ (3807682620627/10000000000000 : ℝ)^3171 := by
    have hnat : (38557733 : ℕ)^4195*10000000000000^3171 ≤ 3807682620627^3171*80000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38557733 80000000 3807682620627 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6008236947/10000000000 : ℝ)^4195 ≤ (12742029765799/25000000000000 : ℝ)^3171 := by
    have hnat : (6008236947 : ℕ)^4195*25000000000000^3171 ≤ 12742029765799^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008236947 10000000000 12742029765799 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1879510489/10000000000 : ℝ), (38557733/80000000 : ℝ), (6008236947/10000000000 : ℝ)] ![(342345460021/3125000000000 : ℝ), (3807682620627/10000000000000 : ℝ), (12742029765799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1879510489/10000000000 : ℝ)|^4195 ≤ (342345460021/3125000000000 : ℝ)^3171
        have hw : |(-1879510489/10000000000 : ℝ)|=(1879510489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38557733/80000000 : ℝ)|^4195 ≤ (3807682620627/10000000000000 : ℝ)^3171
        have hw : |(38557733/80000000 : ℝ)|=(38557733/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6008236947/10000000000 : ℝ)|^4195 ≤ (12742029765799/25000000000000 : ℝ)^3171
        have hw : |(6008236947/10000000000 : ℝ)|=(6008236947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s0_5 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2586305703/5000000000 : ℝ)*x 0 + (-685987167/5000000000 : ℝ)*x 1 + (11734837/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586305703/5000000000 : ℝ)^4195 ≤ (2090398938417/5000000000000 : ℝ)^3171 := by
    have hnat : (2586305703 : ℕ)^4195*5000000000000^3171 ≤ 2090398938417^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586305703 5000000000 2090398938417 5000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685987167/5000000000 : ℝ)^4195 ≤ (722390668229/10000000000000 : ℝ)^3171 := by
    have hnat : (685987167 : ℕ)^4195*10000000000000^3171 ≤ 722390668229^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685987167 5000000000 722390668229 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11734837/19531250 : ℝ)^4195 ≤ (6371014317569/12500000000000 : ℝ)^3171 := by
    have hnat : (11734837 : ℕ)^4195*12500000000000^3171 ≤ 6371014317569^3171*19531250^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11734837 19531250 6371014317569 12500000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586305703/5000000000 : ℝ), (-685987167/5000000000 : ℝ), (11734837/19531250 : ℝ)] ![(2090398938417/5000000000000 : ℝ), (722390668229/10000000000000 : ℝ), (6371014317569/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586305703/5000000000 : ℝ)|^4195 ≤ (2090398938417/5000000000000 : ℝ)^3171
        have hw : |(2586305703/5000000000 : ℝ)|=(2586305703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-685987167/5000000000 : ℝ)|^4195 ≤ (722390668229/10000000000000 : ℝ)^3171
        have hw : |(-685987167/5000000000 : ℝ)|=(685987167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11734837/19531250 : ℝ)|^4195 ≤ (6371014317569/12500000000000 : ℝ)^3171
        have hw : |(11734837/19531250 : ℝ)|=(11734837/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s0_6 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129315283/250000000 : ℝ)*x 0 + (751029599/1250000000 : ℝ)*x 1 + (-685987033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129315283/250000000 : ℝ)^4195 ≤ (10451994462193/25000000000000 : ℝ)^3171 := by
    have hnat : (129315283 : ℕ)^4195*25000000000000^3171 ≤ 10451994462193^3171*250000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129315283 250000000 10451994462193 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (751029599/1250000000 : ℝ)^4195 ≤ (50968117323717/100000000000000 : ℝ)^3171 := by
    have hnat : (751029599 : ℕ)^4195*100000000000000^3171 ≤ 50968117323717^3171*1250000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751029599 1250000000 50968117323717 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685987033/5000000000 : ℝ)^4195 ≤ (1444780963099/20000000000000 : ℝ)^3171 := by
    have hnat : (685987033 : ℕ)^4195*20000000000000^3171 ≤ 1444780963099^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685987033 5000000000 1444780963099 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129315283/250000000 : ℝ), (751029599/1250000000 : ℝ), (-685987033/5000000000 : ℝ)] ![(10451994462193/25000000000000 : ℝ), (50968117323717/100000000000000 : ℝ), (1444780963099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129315283/250000000 : ℝ)|^4195 ≤ (10451994462193/25000000000000 : ℝ)^3171
        have hw : |(129315283/250000000 : ℝ)|=(129315283/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(751029599/1250000000 : ℝ)|^4195 ≤ (50968117323717/100000000000000 : ℝ)^3171
        have hw : |(751029599/1250000000 : ℝ)|=(751029599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-685987033/5000000000 : ℝ)|^4195 ≤ (1444780963099/20000000000000 : ℝ)^3171
        have hw : |(-685987033/5000000000 : ℝ)|=(685987033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s0_7 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206604921/10000000000 : ℝ)*x 0 + (1115207029/2000000000 : ℝ)*x 1 + (1592985231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206604921/10000000000 : ℝ)^4195 ≤ (1272182148317/4000000000000 : ℝ)^3171 := by
    have hnat : (4206604921 : ℕ)^4195*4000000000000^3171 ≤ 1272182148317^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206604921 10000000000 1272182148317 4000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115207029/2000000000 : ℝ)^4195 ≤ (23087519943673/50000000000000 : ℝ)^3171 := by
    have hnat : (1115207029 : ℕ)^4195*50000000000000^3171 ≤ 23087519943673^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115207029 2000000000 23087519943673 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592985231/5000000000 : ℝ)^4195 ≤ (22020406389117/100000000000000 : ℝ)^3171 := by
    have hnat : (1592985231 : ℕ)^4195*100000000000000^3171 ≤ 22020406389117^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592985231 5000000000 22020406389117 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206604921/10000000000 : ℝ), (1115207029/2000000000 : ℝ), (1592985231/5000000000 : ℝ)] ![(1272182148317/4000000000000 : ℝ), (23087519943673/50000000000000 : ℝ), (22020406389117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206604921/10000000000 : ℝ)|^4195 ≤ (1272182148317/4000000000000 : ℝ)^3171
        have hw : |(4206604921/10000000000 : ℝ)|=(4206604921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115207029/2000000000 : ℝ)|^4195 ≤ (23087519943673/50000000000000 : ℝ)^3171
        have hw : |(1115207029/2000000000 : ℝ)|=(1115207029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592985231/5000000000 : ℝ)|^4195 ≤ (22020406389117/100000000000000 : ℝ)^3171
        have hw : |(1592985231/5000000000 : ℝ)|=(1592985231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1197_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (319/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13803/50000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8389/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8389 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8389*1^2048 ≤ 0^2048*1^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8389/2048 : ℝ) ≤ (2344021313488572961/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8389 ≤ (2344021313488572961/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8389*100000000000000000000^2048 ≤ 2344021313488572961^2048*5^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2344021313488572961 100000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2344021313488572961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8389 := by
      have hnat : (1 : ℕ)^2048*1^8389 ≤ 1^8389*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102344021313488572961/100000000000000000000 : ℝ) ≤ (10056724308789781/10000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (102344021313488572961/100000000000000000000 : ℝ)^2048 ≤ (10056724308789781/10000000000000000 : ℝ)^8389 := by
      have hnat : (102344021313488572961 : ℕ)^2048*10000000000000000^8389 ≤ 10056724308789781^8389*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102344021313488572961 100000000000000000000 10056724308789781 10000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056724308789781/10000000000000000 : ℝ)) (X := (102344021313488572961/100000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52344021313488572961/50000000000000000000 : ℝ) ≤ (5056724308789781/5000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (52344021313488572961/50000000000000000000 : ℝ)^2048 ≤ (5056724308789781/5000000000000000 : ℝ)^8389 := by
      have hnat : (52344021313488572961 : ℕ)^2048*5000000000000000^8389 ≤ 5056724308789781^8389*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52344021313488572961 50000000000000000000 5056724308789781 5000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056724308789781/5000000000000000 : ℝ)) (X := (52344021313488572961/50000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(56724308789781/4000000000000000 : ℝ)*(0 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56724308789781/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2344021313488572961/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(56724308789781/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8389/2048 : ℝ) := by
    rw [show (1 : ℝ)+(56724308789781/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10056724308789781/10000000000000000 : ℝ) by norm_num, show 1+(2344021313488572961/100000000000000000000 : ℝ)+(0 : ℝ)=(102344021313488572961/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2344021313488572961/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(56724308789781/4000000000000000 : ℝ)*(2/5 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56724308789781/4000000000000000 : ℝ)*(2/5 : ℝ)=(5056724308789781/5000000000000000 : ℝ) by norm_num, show 1+2*(2344021313488572961/100000000000000000000 : ℝ)=(52344021313488572961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(56724308789781/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56724308789781/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(56724308789781/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56724308789781/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(56724308789781/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56724308789781/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-468631207/2500000000 : ℝ)*X 0 0+(3020852547/5000000000 : ℝ)*X 0 1+(38299111/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513694597/10000000000 : ℝ)*X 1 0+(-2592822477/10000000000 : ℝ)*X 1 1+(2393694409/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5513694963/10000000000 : ℝ)*X 2 0+(4787388479/10000000000 : ℝ)*X 2 1+(-2592822423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098289469/5000000000 : ℝ)*X 0 0+(779666653/2500000000 : ℝ)*X 0 1+(2820522841/5000000000 : ℝ)*X 0 2+(2098289469/5000000000 : ℝ)*X 1 0+(779666653/2500000000 : ℝ)*X 1 1+(2820522841/5000000000 : ℝ)*X 1 2+(2098289469/5000000000 : ℝ)*X 2 0+(779666653/2500000000 : ℝ)*X 2 1+(2820522841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1879510489/10000000000 : ℝ)*X 0 0+(38557733/80000000 : ℝ)*X 0 1+(6008236947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586305703/5000000000 : ℝ)*X 1 0+(-685987167/5000000000 : ℝ)*X 1 1+(11734837/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((129315283/250000000 : ℝ)*X 2 0+(751029599/1250000000 : ℝ)*X 2 1+(-685987033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206604921/10000000000 : ℝ)*X 0 0+(1115207029/2000000000 : ℝ)*X 0 1+(1592985231/5000000000 : ℝ)*X 0 2+(4206604921/10000000000 : ℝ)*X 1 0+(1115207029/2000000000 : ℝ)*X 1 1+(1592985231/5000000000 : ℝ)*X 1 2+(4206604921/10000000000 : ℝ)*X 2 0+(1115207029/2000000000 : ℝ)*X 2 1+(1592985231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1542002638919723964279/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6605151/25000000000000 : ℝ)*(base1) + (728861977/100000000000000 : ℝ)*(base19) + (35849011/5000000000000 : ℝ)*(base23) + (64803357/100000000000000 : ℝ)*(base24) + (185034563/100000000000000 : ℝ)*(upper3) + (5968520652253/1000000000000 : ℝ)*(major0) + (5968520652253/1000000000000 : ℝ)*(major1) + (5968520652253/1000000000000 : ℝ)*(major2) + (79724946763919/10000000000000 : ℝ)*(sp0) + (797250167901727/100000000000000 : ℝ)*(sp1) + (797250114980127/100000000000000 : ℝ)*(sp2) + (396451802563831/100000000000000 : ℝ)*(sp3) + (727772559/50000000000000 : ℝ)*(sp4) + (650951141/50000000000000 : ℝ)*(sp7) + (396453130886717/100000000000000 : ℝ)*(f.failure) + (99656362095463/12500000000000 : ℝ)*(f.sum) + (1730757329407/2000000000000000000000000000 : ℝ)*base66 + (13986547261407/4000000000000000000000000000 : ℝ)*base68 + (3594451061407/4000000000000000000000000000 : ℝ)*base70 + (10462379849407/4000000000000000000000000000 : ℝ)*base72 + (3391806339407/2000000000000000000000000000 : ℝ)*base74 + (18192861821407/4000000000000000000000000000 : ℝ)*base76 + (18854904977407/4000000000000000000000000000 : ℝ)*base78 + (11084692153407/4000000000000000000000000000 : ℝ)*base80 + (6736512416593/2000000000000000000000000000 : ℝ)*base81 + (57466867/10000000000000000000000 : ℝ)*base89 + (57466867/10000000000000000000000 : ℝ)*base91 + (57466867/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85163624997326858284557/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41322711/50000000000000 : ℝ)*(base1) + (2161028631/100000000000000 : ℝ)*(base19) + (53835029/2500000000000 : ℝ)*(base23) + (232696199/100000000000000 : ℝ)*(upper3) + (129489587/50000000000000 : ℝ)*(upper5) + (62989071752433/10000000000000 : ℝ)*(major0) + (62989071752433/10000000000000 : ℝ)*(major1) + (62989071752433/10000000000000 : ℝ)*(major2) + (2237675763/50000000000000 : ℝ)*(sp1) + (1142954209/25000000000000 : ℝ)*(sp2) + (52586406384699/6250000000000 : ℝ)*(sp4) + (168275156625921/20000000000000 : ℝ)*(sp5) + (168275138858353/20000000000000 : ℝ)*(sp6) + (418398649014719/100000000000000 : ℝ)*(sp7) + (418398731660141/100000000000000 : ℝ)*(f.failure) + (841382419509761/100000000000000 : ℝ)*(f.sum) + (24943072172827/20000000000000000000000000000 : ℝ)*base66 + (335522257912827/40000000000000000000000000000 : ℝ)*base68 + (429625464752827/40000000000000000000000000000 : ℝ)*base70 + (299801401752827/40000000000000000000000000000 : ℝ)*base72 + (27114753372827/20000000000000000000000000000 : ℝ)*base74 + (429806990352827/40000000000000000000000000000 : ℝ)*base76 + (205897290392827/40000000000000000000000000000 : ℝ)*base78 + (214142910872827/40000000000000000000000000000 : ℝ)*base80 + (80483928912827/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (55921091/10000000000000000000000 : ℝ)*base89 + (55921091/10000000000000000000000 : ℝ)*base91 + (55921091/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1197_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (319/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13803/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1197_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1197_s1_0 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075201293/10000000000 : ℝ)*x 0 + (5687066729/10000000000 : ℝ)*x 1 + (501356899/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075201293/10000000000 : ℝ)^4195 ≤ (12488804428913/100000000000000 : ℝ)^3171 := by
    have hnat : (2075201293 : ℕ)^4195*100000000000000^3171 ≤ 12488804428913^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075201293 10000000000 12488804428913 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5687066729/10000000000 : ℝ)^4195 ≤ (47395298533527/100000000000000 : ℝ)^3171 := by
    have hnat : (5687066729 : ℕ)^4195*100000000000000^3171 ≤ 47395298533527^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5687066729 10000000000 47395298533527 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501356899/1000000000 : ℝ)^4195 ≤ (4011589701801/10000000000000 : ℝ)^3171 := by
    have hnat : (501356899 : ℕ)^4195*10000000000000^3171 ≤ 4011589701801^3171*1000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501356899 1000000000 4011589701801 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075201293/10000000000 : ℝ), (5687066729/10000000000 : ℝ), (501356899/1000000000 : ℝ)] ![(12488804428913/100000000000000 : ℝ), (47395298533527/100000000000000 : ℝ), (4011589701801/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075201293/10000000000 : ℝ)|^4195 ≤ (12488804428913/100000000000000 : ℝ)^3171
        have hw : |(-2075201293/10000000000 : ℝ)|=(2075201293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5687066729/10000000000 : ℝ)|^4195 ≤ (47395298533527/100000000000000 : ℝ)^3171
        have hw : |(5687066729/10000000000 : ℝ)|=(5687066729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501356899/1000000000 : ℝ)|^4195 ≤ (4011589701801/10000000000000 : ℝ)^3171
        have hw : |(501356899/1000000000 : ℝ)|=(501356899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s1_1 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083222489/2000000000 : ℝ)*x 0 + (-609413479/2500000000 : ℝ)*x 1 + (100271387/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083222489/2000000000 : ℝ)^4195 ≤ (22215616151087/50000000000000 : ℝ)^3171 := by
    have hnat : (1083222489 : ℕ)^4195*50000000000000^3171 ≤ 22215616151087^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083222489 2000000000 22215616151087 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609413479/2500000000 : ℝ)^4195 ≤ (15452866851411/100000000000000 : ℝ)^3171 := by
    have hnat : (609413479 : ℕ)^4195*100000000000000^3171 ≤ 15452866851411^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609413479 2500000000 15452866851411 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100271387/200000000 : ℝ)^4195 ≤ (626810950449/1562500000000 : ℝ)^3171 := by
    have hnat : (100271387 : ℕ)^4195*1562500000000^3171 ≤ 626810950449^3171*200000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100271387 200000000 626810950449 1562500000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083222489/2000000000 : ℝ), (-609413479/2500000000 : ℝ), (100271387/200000000 : ℝ)] ![(22215616151087/50000000000000 : ℝ), (15452866851411/100000000000000 : ℝ), (626810950449/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083222489/2000000000 : ℝ)|^4195 ≤ (22215616151087/50000000000000 : ℝ)^3171
        have hw : |(1083222489/2000000000 : ℝ)|=(1083222489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-609413479/2500000000 : ℝ)|^4195 ≤ (15452866851411/100000000000000 : ℝ)^3171
        have hw : |(-609413479/2500000000 : ℝ)|=(609413479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100271387/200000000 : ℝ)|^4195 ≤ (626810950449/1562500000000 : ℝ)^3171
        have hw : |(100271387/200000000 : ℝ)|=(100271387/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s1_2 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1354027849/2500000000 : ℝ)*x 0 + (1253392507/2500000000 : ℝ)*x 1 + (-1218827209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354027849/2500000000 : ℝ)^4195 ≤ (44431220917729/100000000000000 : ℝ)^3171 := by
    have hnat : (1354027849 : ℕ)^4195*100000000000000^3171 ≤ 44431220917729^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354027849 2500000000 44431220917729 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1253392507/2500000000 : ℝ)^4195 ≤ (10028977001401/25000000000000 : ℝ)^3171 := by
    have hnat : (1253392507 : ℕ)^4195*25000000000000^3171 ≤ 10028977001401^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253392507 2500000000 10028977001401 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1218827209/5000000000 : ℝ)^4195 ≤ (3863217765339/25000000000000 : ℝ)^3171 := by
    have hnat : (1218827209 : ℕ)^4195*25000000000000^3171 ≤ 3863217765339^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218827209 5000000000 3863217765339 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354027849/2500000000 : ℝ), (1253392507/2500000000 : ℝ), (-1218827209/5000000000 : ℝ)] ![(44431220917729/100000000000000 : ℝ), (10028977001401/25000000000000 : ℝ), (3863217765339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354027849/2500000000 : ℝ)|^4195 ≤ (44431220917729/100000000000000 : ℝ)^3171
        have hw : |(1354027849/2500000000 : ℝ)|=(1354027849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1253392507/2500000000 : ℝ)|^4195 ≤ (10028977001401/25000000000000 : ℝ)^3171
        have hw : |(1253392507/2500000000 : ℝ)|=(1253392507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1218827209/5000000000 : ℝ)|^4195 ≤ (3863217765339/25000000000000 : ℝ)^3171
        have hw : |(-1218827209/5000000000 : ℝ)|=(1218827209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s1_3 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (431274173/1000000000 : ℝ)*x 0 + (3687244857/10000000000 : ℝ)*x 1 + (6302027/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431274173/1000000000 : ℝ)^4195 ≤ (8217612572151/25000000000000 : ℝ)^3171 := by
    have hnat : (431274173 : ℕ)^4195*25000000000000^3171 ≤ 8217612572151^3171*1000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431274173 1000000000 8217612572151 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3687244857/10000000000 : ℝ)^4195 ≤ (26716438049229/100000000000000 : ℝ)^3171 := by
    have hnat : (3687244857 : ℕ)^4195*100000000000000^3171 ≤ 26716438049229^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687244857 10000000000 26716438049229 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6302027/12500000 : ℝ)^4195 ≤ (505163895727/1250000000000 : ℝ)^3171 := by
    have hnat : (6302027 : ℕ)^4195*1250000000000^3171 ≤ 505163895727^3171*12500000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6302027 12500000 505163895727 1250000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431274173/1000000000 : ℝ), (3687244857/10000000000 : ℝ), (6302027/12500000 : ℝ)] ![(8217612572151/25000000000000 : ℝ), (26716438049229/100000000000000 : ℝ), (505163895727/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431274173/1000000000 : ℝ)|^4195 ≤ (8217612572151/25000000000000 : ℝ)^3171
        have hw : |(431274173/1000000000 : ℝ)|=(431274173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3687244857/10000000000 : ℝ)|^4195 ≤ (26716438049229/100000000000000 : ℝ)^3171
        have hw : |(3687244857/10000000000 : ℝ)|=(3687244857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6302027/12500000 : ℝ)|^4195 ≤ (505163895727/1250000000000 : ℝ)^3171
        have hw : |(6302027/12500000 : ℝ)|=(6302027/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s1_4 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-415186561/2000000000 : ℝ)*x 0 + (1004514547/2000000000 : ℝ)*x 1 + (283894447/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415186561/2000000000 : ℝ)^4195 ≤ (12494628712717/100000000000000 : ℝ)^3171 := by
    have hnat : (415186561 : ℕ)^4195*100000000000000^3171 ≤ 12494628712717^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415186561 2000000000 12494628712717 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004514547/2000000000 : ℝ)^4195 ≤ (40211232438017/100000000000000 : ℝ)^3171 := by
    have hnat : (1004514547 : ℕ)^4195*100000000000000^3171 ≤ 40211232438017^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004514547 2000000000 40211232438017 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283894447/500000000 : ℝ)^4195 ≤ (11823534709631/25000000000000 : ℝ)^3171 := by
    have hnat : (283894447 : ℕ)^4195*25000000000000^3171 ≤ 11823534709631^3171*500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283894447 500000000 11823534709631 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415186561/2000000000 : ℝ), (1004514547/2000000000 : ℝ), (283894447/500000000 : ℝ)] ![(12494628712717/100000000000000 : ℝ), (40211232438017/100000000000000 : ℝ), (11823534709631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415186561/2000000000 : ℝ)|^4195 ≤ (12494628712717/100000000000000 : ℝ)^3171
        have hw : |(-415186561/2000000000 : ℝ)|=(415186561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004514547/2000000000 : ℝ)|^4195 ≤ (40211232438017/100000000000000 : ℝ)^3171
        have hw : |(1004514547/2000000000 : ℝ)|=(1004514547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283894447/500000000 : ℝ)|^4195 ≤ (11823534709631/25000000000000 : ℝ)^3171
        have hw : |(283894447/500000000 : ℝ)|=(283894447/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s1_5 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5242971037/10000000000 : ℝ)*x 0 + (-443333743/2500000000 : ℝ)*x 1 + (5677888439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242971037/10000000000 : ℝ)^4195 ≤ (42561956423753/100000000000000 : ℝ)^3171 := by
    have hnat : (5242971037 : ℕ)^4195*100000000000000^3171 ≤ 42561956423753^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242971037 10000000000 42561956423753 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443333743/2500000000 : ℝ)^4195 ≤ (5071955125721/50000000000000 : ℝ)^3171 := by
    have hnat : (443333743 : ℕ)^4195*50000000000000^3171 ≤ 5071955125721^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443333743 2500000000 5071955125721 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5677888439/10000000000 : ℝ)^4195 ≤ (47294133317827/100000000000000 : ℝ)^3171 := by
    have hnat : (5677888439 : ℕ)^4195*100000000000000^3171 ≤ 47294133317827^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5677888439 10000000000 47294133317827 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242971037/10000000000 : ℝ), (-443333743/2500000000 : ℝ), (5677888439/10000000000 : ℝ)] ![(42561956423753/100000000000000 : ℝ), (5071955125721/50000000000000 : ℝ), (47294133317827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242971037/10000000000 : ℝ)|^4195 ≤ (42561956423753/100000000000000 : ℝ)^3171
        have hw : |(5242971037/10000000000 : ℝ)|=(5242971037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443333743/2500000000 : ℝ)|^4195 ≤ (5071955125721/50000000000000 : ℝ)^3171
        have hw : |(-443333743/2500000000 : ℝ)|=(443333743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5677888439/10000000000 : ℝ)|^4195 ≤ (47294133317827/100000000000000 : ℝ)^3171
        have hw : |(5677888439/10000000000 : ℝ)|=(5677888439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s1_6 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32768569/62500000 : ℝ)*x 0 + (5677889033/10000000000 : ℝ)*x 1 + (-886667051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32768569/62500000 : ℝ)^4195 ≤ (10640489113993/25000000000000 : ℝ)^3171 := by
    have hnat : (32768569 : ℕ)^4195*25000000000000^3171 ≤ 10640489113993^3171*62500000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32768569 62500000 10640489113993 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5677889033/10000000000 : ℝ)^4195 ≤ (11823534965831/25000000000000 : ℝ)^3171 := by
    have hnat : (5677889033 : ℕ)^4195*25000000000000^3171 ≤ 11823534965831^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5677889033 10000000000 11823534965831 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886667051/5000000000 : ℝ)^4195 ≤ (10143903667749/100000000000000 : ℝ)^3171 := by
    have hnat : (886667051 : ℕ)^4195*100000000000000^3171 ≤ 10143903667749^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886667051 5000000000 10143903667749 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32768569/62500000 : ℝ), (5677889033/10000000000 : ℝ), (-886667051/5000000000 : ℝ)] ![(10640489113993/25000000000000 : ℝ), (11823534965831/25000000000000 : ℝ), (10143903667749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32768569/62500000 : ℝ)|^4195 ≤ (10640489113993/25000000000000 : ℝ)^3171
        have hw : |(32768569/62500000 : ℝ)|=(32768569/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5677889033/10000000000 : ℝ)|^4195 ≤ (11823534965831/25000000000000 : ℝ)^3171
        have hw : |(5677889033/10000000000 : ℝ)|=(5677889033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-886667051/5000000000 : ℝ)|^4195 ≤ (10143903667749/100000000000000 : ℝ)^3171
        have hw : |(-886667051/5000000000 : ℝ)|=(886667051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s1_7 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2157106561/5000000000 : ℝ)*x 0 + (2511757541/5000000000 : ℝ)*x 1 + (1852850921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157106561/5000000000 : ℝ)^4195 ≤ (16442643544217/50000000000000 : ℝ)^3171 := by
    have hnat : (2157106561 : ℕ)^4195*50000000000000^3171 ≤ 16442643544217^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157106561 5000000000 16442643544217 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2511757541/5000000000 : ℝ)^4195 ≤ (4022121359487/10000000000000 : ℝ)^3171 := by
    have hnat : (2511757541 : ℕ)^4195*10000000000000^3171 ≤ 4022121359487^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511757541 5000000000 4022121359487 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1852850921/5000000000 : ℝ)^4195 ≤ (3361687412623/12500000000000 : ℝ)^3171 := by
    have hnat : (1852850921 : ℕ)^4195*12500000000000^3171 ≤ 3361687412623^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852850921 5000000000 3361687412623 12500000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157106561/5000000000 : ℝ), (2511757541/5000000000 : ℝ), (1852850921/5000000000 : ℝ)] ![(16442643544217/50000000000000 : ℝ), (4022121359487/10000000000000 : ℝ), (3361687412623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157106561/5000000000 : ℝ)|^4195 ≤ (16442643544217/50000000000000 : ℝ)^3171
        have hw : |(2157106561/5000000000 : ℝ)|=(2157106561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2511757541/5000000000 : ℝ)|^4195 ≤ (4022121359487/10000000000000 : ℝ)^3171
        have hw : |(2511757541/5000000000 : ℝ)|=(2511757541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1852850921/5000000000 : ℝ)|^4195 ≤ (3361687412623/12500000000000 : ℝ)^3171
        have hw : |(1852850921/5000000000 : ℝ)|=(1852850921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1197_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13803/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (186/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20193/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13803/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (319/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13803/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (319/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13803/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (319/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13803/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (319/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13803/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (319/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13803/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (319/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (319/50000 : ℝ) ^ (8389/2048 : ℝ) ≤ (25472134407/25000000000000000000 : ℝ) := by
    have hpowers : (319/50000 : ℝ)^8389 ≤ (25472134407/25000000000000000000 : ℝ)^2048 := by
      have hnat : (319 : ℕ)^8389*25000000000000000000^2048 ≤ 25472134407^2048*50000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        319 50000 25472134407 25000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (319/50000 : ℝ)) (X := (25472134407/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13803/50000 : ℝ) ^ (8389/2048 : ℝ) ≤ (256574373978348801/50000000000000000000 : ℝ) := by
    have hpowers : (13803/50000 : ℝ)^8389 ≤ (256574373978348801/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13803 : ℕ)^8389*50000000000000000000^2048 ≤ 256574373978348801^2048*50000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13803 50000 256574373978348801 50000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13803/50000 : ℝ)) (X := (256574373978348801/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000025472134407/12500000000000000000 : ℝ) ≤ (5000000002487397/5000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (12500000025472134407/12500000000000000000 : ℝ)^2048 ≤ (5000000002487397/5000000000000000 : ℝ)^8389 := by
      have hnat : (12500000025472134407 : ℕ)^2048*5000000000000000^8389 ≤ 5000000002487397^8389*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000025472134407 12500000000000000000 5000000002487397 5000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000002487397/5000000000000000 : ℝ)) (X := (12500000025472134407/12500000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10051314884984523523/10000000000000000000 : ℝ) ≤ (5006251619997933/5000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (10051314884984523523/10000000000000000000 : ℝ)^2048 ≤ (5006251619997933/5000000000000000 : ℝ)^8389 := by
      have hnat : (10051314884984523523 : ℕ)^2048*5000000000000000^8389 ≤ 5006251619997933^8389*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10051314884984523523 10000000000000000000 5006251619997933 5000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006251619997933/5000000000000000 : ℝ)) (X := (10051314884984523523/10000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25256574373978348801/25000000000000000000 : ℝ) ≤ (5012503237508469/5000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (25256574373978348801/25000000000000000000 : ℝ)^2048 ≤ (5012503237508469/5000000000000000 : ℝ)^8389 := by
      have hnat : (25256574373978348801 : ℕ)^2048*5000000000000000^8389 ≤ 5012503237508469^8389*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25256574373978348801 25000000000000000000 5012503237508469 5000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012503237508469/5000000000000000 : ℝ)) (X := (25256574373978348801/25000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25472134407/25000000000000000000 : ℝ) ≤ ((3370800575078416959/3371000000000000000 : ℝ)+2*(781452188817/168550000000000 : ℝ)*(319/50000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (3370800575078416959/3371000000000000000 : ℝ)+2*(781452188817/168550000000000 : ℝ)*(319/50000 : ℝ)=(5000000002487397/5000000000000000 : ℝ) by norm_num, show 1+2*(25472134407/25000000000000000000 : ℝ)=(12500000025472134407/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(256574373978348801/50000000000000000000 : ℝ)+(25472134407/25000000000000000000 : ℝ) ≤ ((3370800575078416959/3371000000000000000 : ℝ)+(781452188817/168550000000000 : ℝ)*((13803/50000 : ℝ)+(319/50000 : ℝ)))^(8389/2048 : ℝ) := by
    rw [show (3370800575078416959/3371000000000000000 : ℝ)+(781452188817/168550000000000 : ℝ)*((13803/50000 : ℝ)+(319/50000 : ℝ))=(5006251619997933/5000000000000000 : ℝ) by norm_num, show 1+(256574373978348801/50000000000000000000 : ℝ)+(25472134407/25000000000000000000 : ℝ)=(10051314884984523523/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(256574373978348801/50000000000000000000 : ℝ) ≤ ((3370800575078416959/3371000000000000000 : ℝ)+2*(781452188817/168550000000000 : ℝ)*(13803/50000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (3370800575078416959/3371000000000000000 : ℝ)+2*(781452188817/168550000000000 : ℝ)*(13803/50000 : ℝ)=(5012503237508469/5000000000000000 : ℝ) by norm_num, show 1+2*(256574373978348801/50000000000000000000 : ℝ)=(25256574373978348801/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3370800575078416959/3371000000000000000 : ℝ)*(X 1 0+X 2 0)+(781452188817/168550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (319/50000 : ℝ)) (hi := (13803/50000 : ℝ)) (c := (3370800575078416959/3371000000000000000 : ℝ)) (alpha := (781452188817/168550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3370800575078416959/3371000000000000000 : ℝ)*(X 0 1+X 2 1)+(781452188817/168550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (319/50000 : ℝ)) (hi := (13803/50000 : ℝ)) (c := (3370800575078416959/3371000000000000000 : ℝ)) (alpha := (781452188817/168550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3370800575078416959/3371000000000000000 : ℝ)*(X 0 2+X 1 2)+(781452188817/168550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (319/50000 : ℝ)) (hi := (13803/50000 : ℝ)) (c := (3370800575078416959/3371000000000000000 : ℝ)) (alpha := (781452188817/168550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2075201293/10000000000 : ℝ)*X 0 0+(5687066729/10000000000 : ℝ)*X 0 1+(501356899/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1083222489/2000000000 : ℝ)*X 1 0+(-609413479/2500000000 : ℝ)*X 1 1+(100271387/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1354027849/2500000000 : ℝ)*X 2 0+(1253392507/2500000000 : ℝ)*X 2 1+(-1218827209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431274173/1000000000 : ℝ)*X 0 0+(3687244857/10000000000 : ℝ)*X 0 1+(6302027/12500000 : ℝ)*X 0 2+(431274173/1000000000 : ℝ)*X 1 0+(3687244857/10000000000 : ℝ)*X 1 1+(6302027/12500000 : ℝ)*X 1 2+(431274173/1000000000 : ℝ)*X 2 0+(3687244857/10000000000 : ℝ)*X 2 1+(6302027/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-415186561/2000000000 : ℝ)*X 0 0+(1004514547/2000000000 : ℝ)*X 0 1+(283894447/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5242971037/10000000000 : ℝ)*X 1 0+(-443333743/2500000000 : ℝ)*X 1 1+(5677888439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((32768569/62500000 : ℝ)*X 2 0+(5677889033/10000000000 : ℝ)*X 2 1+(-886667051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2157106561/5000000000 : ℝ)*X 0 0+(2511757541/5000000000 : ℝ)*X 0 1+(1852850921/5000000000 : ℝ)*X 0 2+(2157106561/5000000000 : ℝ)*X 1 0+(2511757541/5000000000 : ℝ)*X 1 1+(1852850921/5000000000 : ℝ)*X 1 2+(2157106561/5000000000 : ℝ)*X 2 0+(2511757541/5000000000 : ℝ)*X 2 1+(1852850921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95584335540570589376316057/33710000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (783871/25000000000000 : ℝ)*(base16) + (161835123/20000000000000 : ℝ)*(base19) + (298956577/50000000000000 : ℝ)*(base23) + (19817383/50000000000000 : ℝ)*(upper2) + (1521773/800000000000 : ℝ)*(upper3) + (222314928030447/20000000000000 : ℝ)*(major0) + (222314928030447/20000000000000 : ℝ)*(major1) + (222314928030447/20000000000000 : ℝ)*(major2) + (1484792641203631/100000000000000 : ℝ)*(sp0) + (742397910087569/50000000000000 : ℝ)*(sp1) + (1484796034573083/100000000000000 : ℝ)*(sp2) + (369174743844101/50000000000000 : ℝ)*(sp3) + (1995641303/50000000000000 : ℝ)*(sp4) + (1532806863/50000000000000 : ℝ)*(sp7) + (92294069162741/12500000000000 : ℝ)*(f.failure) + (1484796632486237/100000000000000 : ℝ)*(f.sum) + (2604176939951/3371000000000000000000000000 : ℝ)*base66 + (406121435830969327/67420000000000000000000000000000 : ℝ)*base68 + (304970789602109327/67420000000000000000000000000000 : ℝ)*base70 + (334780382142509327/67420000000000000000000000000000 : ℝ)*base72 + (63188669719/33710000000000000000000000 : ℝ)*base74 + (158672084379509327/67420000000000000000000000000000 : ℝ)*base76 + (188462899640869327/67420000000000000000000000000000 : ℝ)*base78 + (524437866820269327/67420000000000000000000000000000 : ℝ)*base80 + (182529881633/168550000000000000000000000 : ℝ)*base82 + (5593691/1250000000000000000000 : ℝ)*base89 + (5593691/1250000000000000000000 : ℝ)*base91 + (5593691/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98781293270268006158221401/10534375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47718049/100000000000000 : ℝ)*(base1) + (1127186171/50000000000000 : ℝ)*(base19) + (231267403/10000000000000 : ℝ)*(base23) + (198750953/100000000000000 : ℝ)*(upper3) + (118629217/50000000000000 : ℝ)*(upper5) + (71400455042513/6250000000000 : ℝ)*(major0) + (71400455042513/6250000000000 : ℝ)*(major1) + (71400455042513/6250000000000 : ℝ)*(major2) + (5058325783/50000000000000 : ℝ)*(sp1) + (11855742157/100000000000000 : ℝ)*(sp2) + (381495366029787/25000000000000 : ℝ)*(sp4) + (1525969045377191/100000000000000 : ℝ)*(sp5) + (95372952999057/6250000000000 : ℝ)*(sp6) + (379416392336573/50000000000000 : ℝ)*(sp7) + (151766566478239/20000000000000 : ℝ)*(f.failure) + (1525981416401099/100000000000000 : ℝ)*(f.sum) + (4742625357961/2106875000000000000000000000 : ℝ)*base66 + (20247378365147967/21068750000000000000000000000000 : ℝ)*base67 + (3069177419522967/21068750000000000000000000000000 : ℝ)*base69 + (114448511321645783/21068750000000000000000000000000 : ℝ)*base72 + (4148049637519/2106875000000000000000000000 : ℝ)*base73 + (161875408065220783/21068750000000000000000000000000 : ℝ)*base76 + (52159040904552033/21068750000000000000000000000000 : ℝ)*base78 + (141756786698302033/21068750000000000000000000000000 : ℝ)*base80 + (11395511992381/8427500000000000000000000000 : ℝ)*base81 + (7538289/2000000000000000000000 : ℝ)*base89 + (7538289/2000000000000000000000 : ℝ)*base91 + (7538289/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1197_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13803/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (319/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (186/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20193/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1197_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1197_s2_0 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-531383643/2500000000 : ℝ)*x 0 + (5500661391/10000000000 : ℝ)*x 1 + (1291979157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531383643/2500000000 : ℝ)^4195 ≤ (6445547511631/50000000000000 : ℝ)^3171 := by
    have hnat : (531383643 : ℕ)^4195*50000000000000^3171 ≤ 6445547511631^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531383643 2500000000 6445547511631 50000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5500661391/10000000000 : ℝ)^4195 ≤ (45351118423273/100000000000000 : ℝ)^3171 := by
    have hnat : (5500661391 : ℕ)^4195*100000000000000^3171 ≤ 45351118423273^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500661391 10000000000 45351118423273 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291979157/2500000000 : ℝ)^4195 ≤ (41757786544279/100000000000000 : ℝ)^3171 := by
    have hnat : (1291979157 : ℕ)^4195*100000000000000^3171 ≤ 41757786544279^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291979157 2500000000 41757786544279 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531383643/2500000000 : ℝ), (5500661391/10000000000 : ℝ), (1291979157/2500000000 : ℝ)] ![(6445547511631/50000000000000 : ℝ), (45351118423273/100000000000000 : ℝ), (41757786544279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531383643/2500000000 : ℝ)|^4195 ≤ (6445547511631/50000000000000 : ℝ)^3171
        have hw : |(-531383643/2500000000 : ℝ)|=(531383643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5500661391/10000000000 : ℝ)|^4195 ≤ (45351118423273/100000000000000 : ℝ)^3171
        have hw : |(5500661391/10000000000 : ℝ)|=(5500661391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291979157/2500000000 : ℝ)|^4195 ≤ (41757786544279/100000000000000 : ℝ)^3171
        have hw : |(1291979157/2500000000 : ℝ)|=(1291979157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s2_1 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371538377/10000000000 : ℝ)*x 0 + (-2298167713/10000000000 : ℝ)*x 1 + (1291980241/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371538377/10000000000 : ℝ)^4195 ≤ (43948128875641/100000000000000 : ℝ)^3171 := by
    have hnat : (5371538377 : ℕ)^4195*100000000000000^3171 ≤ 43948128875641^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371538377 10000000000 43948128875641 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2298167713/10000000000 : ℝ)^4195 ≤ (11435230571/80000000000 : ℝ)^3171 := by
    have hnat : (2298167713 : ℕ)^4195*80000000000^3171 ≤ 11435230571^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298167713 10000000000 11435230571 80000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291980241/2500000000 : ℝ)^4195 ≤ (41757832893989/100000000000000 : ℝ)^3171 := by
    have hnat : (1291980241 : ℕ)^4195*100000000000000^3171 ≤ 41757832893989^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291980241 2500000000 41757832893989 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371538377/10000000000 : ℝ), (-2298167713/10000000000 : ℝ), (1291980241/2500000000 : ℝ)] ![(43948128875641/100000000000000 : ℝ), (11435230571/80000000000 : ℝ), (41757832893989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371538377/10000000000 : ℝ)|^4195 ≤ (43948128875641/100000000000000 : ℝ)^3171
        have hw : |(5371538377/10000000000 : ℝ)|=(5371538377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2298167713/10000000000 : ℝ)|^4195 ≤ (11435230571/80000000000 : ℝ)^3171
        have hw : |(-2298167713/10000000000 : ℝ)|=(2298167713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1291980241/2500000000 : ℝ)|^4195 ≤ (41757832893989/100000000000000 : ℝ)^3171
        have hw : |(1291980241/2500000000 : ℝ)|=(1291980241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s2_2 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074308043/2000000000 : ℝ)*x 0 + (5167918397/10000000000 : ℝ)*x 1 + (-229816863/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074308043/2000000000 : ℝ)^4195 ≤ (549351859621/1250000000000 : ℝ)^3171 := by
    have hnat : (1074308043 : ℕ)^4195*1250000000000^3171 ≤ 549351859621^3171*2000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074308043 2000000000 549351859621 1250000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5167918397/10000000000 : ℝ)^4195 ≤ (41757805454019/100000000000000 : ℝ)^3171 := by
    have hnat : (5167918397 : ℕ)^4195*100000000000000^3171 ≤ 41757805454019^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167918397 10000000000 41757805454019 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229816863/1000000000 : ℝ)^4195 ≤ (14294045759081/100000000000000 : ℝ)^3171 := by
    have hnat : (229816863 : ℕ)^4195*100000000000000^3171 ≤ 14294045759081^3171*1000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229816863 1000000000 14294045759081 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074308043/2000000000 : ℝ), (5167918397/10000000000 : ℝ), (-229816863/1000000000 : ℝ)] ![(549351859621/1250000000000 : ℝ), (41757805454019/100000000000000 : ℝ), (14294045759081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074308043/2000000000 : ℝ)|^4195 ≤ (549351859621/1250000000000 : ℝ)^3171
        have hw : |(1074308043/2000000000 : ℝ)|=(1074308043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5167918397/10000000000 : ℝ)|^4195 ≤ (41757805454019/100000000000000 : ℝ)^3171
        have hw : |(5167918397/10000000000 : ℝ)|=(5167918397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229816863/1000000000 : ℝ)|^4195 ≤ (14294045759081/100000000000000 : ℝ)^3171
        have hw : |(-229816863/1000000000 : ℝ)|=(229816863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s2_3 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4347405229/10000000000 : ℝ)*x 0 + (4025437089/10000000000 : ℝ)*x 1 + (1173642291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347405229/10000000000 : ℝ)^4195 ≤ (6644082725189/20000000000000 : ℝ)^3171 := by
    have hnat : (4347405229 : ℕ)^4195*20000000000000^3171 ≤ 6644082725189^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347405229 10000000000 6644082725189 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4025437089/10000000000 : ℝ)^4195 ≤ (6001042330221/20000000000000 : ℝ)^3171 := by
    have hnat : (4025437089 : ℕ)^4195*20000000000000^3171 ≤ 6001042330221^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025437089 10000000000 6001042330221 20000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1173642291/2500000000 : ℝ)^4195 ≤ (36774374714349/100000000000000 : ℝ)^3171 := by
    have hnat : (1173642291 : ℕ)^4195*100000000000000^3171 ≤ 36774374714349^3171*2500000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173642291 2500000000 36774374714349 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347405229/10000000000 : ℝ), (4025437089/10000000000 : ℝ), (1173642291/2500000000 : ℝ)] ![(6644082725189/20000000000000 : ℝ), (6001042330221/20000000000000 : ℝ), (36774374714349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347405229/10000000000 : ℝ)|^4195 ≤ (6644082725189/20000000000000 : ℝ)^3171
        have hw : |(4347405229/10000000000 : ℝ)|=(4347405229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4025437089/10000000000 : ℝ)|^4195 ≤ (6001042330221/20000000000000 : ℝ)^3171
        have hw : |(4025437089/10000000000 : ℝ)|=(4025437089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1173642291/2500000000 : ℝ)|^4195 ≤ (36774374714349/100000000000000 : ℝ)^3171
        have hw : |(1173642291/2500000000 : ℝ)|=(1173642291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s2_4 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062810957/5000000000 : ℝ)*x 0 + (323132851/625000000 : ℝ)*x 1 + (5498431923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062810957/5000000000 : ℝ)^4195 ≤ (3222948951491/25000000000000 : ℝ)^3171 := by
    have hnat : (1062810957 : ℕ)^4195*25000000000000^3171 ≤ 3222948951491^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062810957 5000000000 3222948951491 25000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323132851/625000000 : ℝ)^4195 ≤ (41781401167489/100000000000000 : ℝ)^3171 := by
    have hnat : (323132851 : ℕ)^4195*100000000000000^3171 ≤ 41781401167489^3171*625000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323132851 625000000 41781401167489 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498431923/10000000000 : ℝ)^4195 ≤ (45326803011319/100000000000000 : ℝ)^3171 := by
    have hnat : (5498431923 : ℕ)^4195*100000000000000^3171 ≤ 45326803011319^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498431923 10000000000 45326803011319 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062810957/5000000000 : ℝ), (323132851/625000000 : ℝ), (5498431923/10000000000 : ℝ)] ![(3222948951491/25000000000000 : ℝ), (41781401167489/100000000000000 : ℝ), (45326803011319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062810957/5000000000 : ℝ)|^4195 ≤ (3222948951491/25000000000000 : ℝ)^3171
        have hw : |(-1062810957/5000000000 : ℝ)|=(1062810957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323132851/625000000 : ℝ)|^4195 ≤ (41781401167489/100000000000000 : ℝ)^3171
        have hw : |(323132851/625000000 : ℝ)|=(323132851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498431923/10000000000 : ℝ)|^4195 ≤ (45326803011319/100000000000000 : ℝ)^3171
        have hw : |(5498431923/10000000000 : ℝ)|=(5498431923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s2_5 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286808049/10000000000 : ℝ)*x 0 + (-983827551/5000000000 : ℝ)*x 1 + (2749215971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286808049/10000000000 : ℝ)^4195 ≤ (43033373811859/100000000000000 : ℝ)^3171 := by
    have hnat : (5286808049 : ℕ)^4195*100000000000000^3171 ≤ 43033373811859^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286808049 10000000000 43033373811859 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983827551/5000000000 : ℝ)^4195 ≤ (4546805843/39062500000 : ℝ)^3171 := by
    have hnat : (983827551 : ℕ)^4195*39062500000^3171 ≤ 4546805843^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983827551 5000000000 4546805843 39062500000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2749215971/5000000000 : ℝ)^4195 ≤ (45326803218527/100000000000000 : ℝ)^3171 := by
    have hnat : (2749215971 : ℕ)^4195*100000000000000^3171 ≤ 45326803218527^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749215971 5000000000 45326803218527 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286808049/10000000000 : ℝ), (-983827551/5000000000 : ℝ), (2749215971/5000000000 : ℝ)] ![(43033373811859/100000000000000 : ℝ), (4546805843/39062500000 : ℝ), (45326803218527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286808049/10000000000 : ℝ)|^4195 ≤ (43033373811859/100000000000000 : ℝ)^3171
        have hw : |(5286808049/10000000000 : ℝ)|=(5286808049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983827551/5000000000 : ℝ)|^4195 ≤ (4546805843/39062500000 : ℝ)^3171
        have hw : |(-983827551/5000000000 : ℝ)|=(983827551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2749215971/5000000000 : ℝ)|^4195 ≤ (45326803218527/100000000000000 : ℝ)^3171
        have hw : |(2749215971/5000000000 : ℝ)|=(2749215971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s2_6 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643404109/5000000000 : ℝ)*x 0 + (5498431957/10000000000 : ℝ)*x 1 + (-1967654847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643404109/5000000000 : ℝ)^4195 ≤ (5379171953963/12500000000000 : ℝ)^3171 := by
    have hnat : (2643404109 : ℕ)^4195*12500000000000^3171 ≤ 5379171953963^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643404109 5000000000 5379171953963 12500000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498431957/10000000000 : ℝ)^4195 ≤ (1416462605691/3125000000000 : ℝ)^3171 := by
    have hnat : (5498431957 : ℕ)^4195*3125000000000^3171 ≤ 1416462605691^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498431957 10000000000 1416462605691 3125000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1967654847/10000000000 : ℝ)^4195 ≤ (11639820962481/100000000000000 : ℝ)^3171 := by
    have hnat : (1967654847 : ℕ)^4195*100000000000000^3171 ≤ 11639820962481^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967654847 10000000000 11639820962481 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643404109/5000000000 : ℝ), (5498431957/10000000000 : ℝ), (-1967654847/10000000000 : ℝ)] ![(5379171953963/12500000000000 : ℝ), (1416462605691/3125000000000 : ℝ), (11639820962481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643404109/5000000000 : ℝ)|^4195 ≤ (5379171953963/12500000000000 : ℝ)^3171
        have hw : |(2643404109/5000000000 : ℝ)|=(2643404109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498431957/10000000000 : ℝ)|^4195 ≤ (1416462605691/3125000000000 : ℝ)^3171
        have hw : |(5498431957/10000000000 : ℝ)|=(5498431957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1967654847/10000000000 : ℝ)|^4195 ≤ (11639820962481/100000000000000 : ℝ)^3171
        have hw : |(-1967654847/10000000000 : ℝ)|=(1967654847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1197_s2_7 (p : ℝ) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4347583173/10000000000 : ℝ)*x 0 + (2345064853/5000000000 : ℝ)*x 1 + (4029918623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347583173/10000000000 : ℝ)^4195 ≤ (33222212483831/100000000000000 : ℝ)^3171 := by
    have hnat : (4347583173 : ℕ)^4195*100000000000000^3171 ≤ 33222212483831^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347583173 10000000000 33222212483831 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2345064853/5000000000 : ℝ)^4195 ≤ (36728375660503/100000000000000 : ℝ)^3171 := by
    have hnat : (2345064853 : ℕ)^4195*100000000000000^3171 ≤ 36728375660503^3171*5000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345064853 5000000000 36728375660503 100000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029918623/10000000000 : ℝ)^4195 ≤ (3004941183851/10000000000000 : ℝ)^3171 := by
    have hnat : (4029918623 : ℕ)^4195*10000000000000^3171 ≤ 3004941183851^3171*10000000000^4195 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029918623 10000000000 3004941183851 10000000000000 4195 3171 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4195/1024 : ℝ)) 4195 3171 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347583173/10000000000 : ℝ), (2345064853/5000000000 : ℝ), (4029918623/10000000000 : ℝ)] ![(33222212483831/100000000000000 : ℝ), (36728375660503/100000000000000 : ℝ), (3004941183851/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347583173/10000000000 : ℝ)|^4195 ≤ (33222212483831/100000000000000 : ℝ)^3171
        have hw : |(4347583173/10000000000 : ℝ)|=(4347583173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2345064853/5000000000 : ℝ)|^4195 ≤ (36728375660503/100000000000000 : ℝ)^3171
        have hw : |(2345064853/5000000000 : ℝ)|=(2345064853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029918623/10000000000 : ℝ)|^4195 ≤ (3004941183851/10000000000000 : ℝ)^3171
        have hw : |(4029918623/10000000000 : ℝ)|=(4029918623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1197_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20193/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (186/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (291/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2043/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20193/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (186/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20193/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (186/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20193/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (186/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20193/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (186/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20193/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (186/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20193/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (186/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (186/3125 : ℝ) ^ (8389/2048 : ℝ) ≤ (956719869281291/100000000000000000000 : ℝ) := by
    have hpowers : (186/3125 : ℝ)^8389 ≤ (956719869281291/100000000000000000000 : ℝ)^2048 := by
      have hnat : (186 : ℕ)^8389*100000000000000000000^2048 ≤ 956719869281291^2048*3125^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        186 3125 956719869281291 100000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (186/3125 : ℝ)) (X := (956719869281291/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20193/100000 : ℝ) ^ (8389/2048 : ℝ) ≤ (2851016094686377/2000000000000000000 : ℝ) := by
    have hpowers : (20193/100000 : ℝ)^8389 ≤ (2851016094686377/2000000000000000000 : ℝ)^2048 := by
      have hnat : (20193 : ℕ)^8389*2000000000000000000^2048 ≤ 2851016094686377^2048*100000^8389 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20193 100000 2851016094686377 2000000000000000000 8389 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20193/100000 : ℝ)) (X := (2851016094686377/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000956719869281291/50000000000000000000 : ℝ) ≤ (5000023356158341/5000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (50000956719869281291/50000000000000000000 : ℝ)^2048 ≤ (5000023356158341/5000000000000000 : ℝ)^8389 := by
      have hnat : (50000956719869281291 : ℕ)^2048*5000000000000000^8389 ≤ 5000023356158341^8389*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000956719869281291 50000000000000000000 5000023356158341 5000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000023356158341/5000000000000000 : ℝ)) (X := (50000956719869281291/50000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100143507524603600141/100000000000000000000 : ℝ) ≤ (5001750769704423/5000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (100143507524603600141/100000000000000000000 : ℝ)^2048 ≤ (5001750769704423/5000000000000000 : ℝ)^8389 := by
      have hnat : (100143507524603600141 : ℕ)^2048*5000000000000000^8389 ≤ 5001750769704423^8389*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100143507524603600141 100000000000000000000 5001750769704423 5000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001750769704423/5000000000000000 : ℝ)) (X := (100143507524603600141/100000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1002851016094686377/1000000000000000000 : ℝ) ≤ (1000695636650101/1000000000000000 : ℝ) ^ (8389/2048 : ℝ) := by
    have hpowers : (1002851016094686377/1000000000000000000 : ℝ)^2048 ≤ (1000695636650101/1000000000000000 : ℝ)^8389 := by
      have hnat : (1002851016094686377 : ℕ)^2048*1000000000000000^8389 ≤ 1000695636650101^8389*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1002851016094686377 1000000000000000000 1000695636650101 1000000000000000 2048 8389 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000695636650101/1000000000000000 : ℝ)) (X := (1002851016094686377/1000000000000000000 : ℝ)) (by norm_num) 8389 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(956719869281291/100000000000000000000 : ℝ) ≤ ((23728256494732791351/23735000000000000000 : ℝ)+2*(863706773041/356025000000000 : ℝ)*(186/3125 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (23728256494732791351/23735000000000000000 : ℝ)+2*(863706773041/356025000000000 : ℝ)*(186/3125 : ℝ)=(5000023356158341/5000000000000000 : ℝ) by norm_num, show 1+2*(956719869281291/100000000000000000000 : ℝ)=(50000956719869281291/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2851016094686377/2000000000000000000 : ℝ)+(956719869281291/100000000000000000000 : ℝ) ≤ ((23728256494732791351/23735000000000000000 : ℝ)+(863706773041/356025000000000 : ℝ)*((20193/100000 : ℝ)+(186/3125 : ℝ)))^(8389/2048 : ℝ) := by
    rw [show (23728256494732791351/23735000000000000000 : ℝ)+(863706773041/356025000000000 : ℝ)*((20193/100000 : ℝ)+(186/3125 : ℝ))=(5001750769704423/5000000000000000 : ℝ) by norm_num, show 1+(2851016094686377/2000000000000000000 : ℝ)+(956719869281291/100000000000000000000 : ℝ)=(100143507524603600141/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2851016094686377/2000000000000000000 : ℝ) ≤ ((23728256494732791351/23735000000000000000 : ℝ)+2*(863706773041/356025000000000 : ℝ)*(20193/100000 : ℝ))^(8389/2048 : ℝ) := by
    rw [show (23728256494732791351/23735000000000000000 : ℝ)+2*(863706773041/356025000000000 : ℝ)*(20193/100000 : ℝ)=(1000695636650101/1000000000000000 : ℝ) by norm_num, show 1+2*(2851016094686377/2000000000000000000 : ℝ)=(1002851016094686377/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23728256494732791351/23735000000000000000 : ℝ)*(X 1 0+X 2 0)+(863706773041/356025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (186/3125 : ℝ)) (hi := (20193/100000 : ℝ)) (c := (23728256494732791351/23735000000000000000 : ℝ)) (alpha := (863706773041/356025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23728256494732791351/23735000000000000000 : ℝ)*(X 0 1+X 2 1)+(863706773041/356025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (186/3125 : ℝ)) (hi := (20193/100000 : ℝ)) (c := (23728256494732791351/23735000000000000000 : ℝ)) (alpha := (863706773041/356025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23728256494732791351/23735000000000000000 : ℝ)*(X 0 2+X 1 2)+(863706773041/356025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8389/2048 : ℝ)) (lo := (186/3125 : ℝ)) (hi := (20193/100000 : ℝ)) (c := (23728256494732791351/23735000000000000000 : ℝ)) (alpha := (863706773041/356025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-531383643/2500000000 : ℝ)*X 0 0+(5500661391/10000000000 : ℝ)*X 0 1+(1291979157/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371538377/10000000000 : ℝ)*X 1 0+(-2298167713/10000000000 : ℝ)*X 1 1+(1291980241/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074308043/2000000000 : ℝ)*X 2 0+(5167918397/10000000000 : ℝ)*X 2 1+(-229816863/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347405229/10000000000 : ℝ)*X 0 0+(4025437089/10000000000 : ℝ)*X 0 1+(1173642291/2500000000 : ℝ)*X 0 2+(4347405229/10000000000 : ℝ)*X 1 0+(4025437089/10000000000 : ℝ)*X 1 1+(1173642291/2500000000 : ℝ)*X 1 2+(4347405229/10000000000 : ℝ)*X 2 0+(4025437089/10000000000 : ℝ)*X 2 1+(1173642291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1062810957/5000000000 : ℝ)*X 0 0+(323132851/625000000 : ℝ)*X 0 1+(5498431923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5286808049/10000000000 : ℝ)*X 1 0+(-983827551/5000000000 : ℝ)*X 1 1+(2749215971/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643404109/5000000000 : ℝ)*X 2 0+(5498431957/10000000000 : ℝ)*X 2 1+(-1967654847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347583173/10000000000 : ℝ)*X 0 0+(2345064853/5000000000 : ℝ)*X 0 1+(4029918623/10000000000 : ℝ)*X 0 2+(4347583173/10000000000 : ℝ)*X 1 0+(2345064853/5000000000 : ℝ)*X 1 1+(4029918623/10000000000 : ℝ)*X 1 2+(4347583173/10000000000 : ℝ)*X 2 0+(2345064853/5000000000 : ℝ)*X 2 1+(4029918623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1197_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7780662314402836725659/2373500000000000000000000000 : ℝ) := by norm_num
    linear_combination (47979003/20000000000000 : ℝ)*(base19) + (118262177/10000000000000 : ℝ)*(base23) + (42186587/25000000000000 : ℝ)*(upper2) + (458098073/100000000000000 : ℝ)*(upper3) + (214743573/100000000000000 : ℝ)*(upper4) + (449986386580033/20000000000000 : ℝ)*(major0) + (449986386580033/20000000000000 : ℝ)*(major1) + (449986386580033/20000000000000 : ℝ)*(major2) + (300533946133701/10000000000000 : ℝ)*(sp0) + (1502684147852963/50000000000000 : ℝ)*(sp1) + (3005367352979171/100000000000000 : ℝ)*(sp2) + (298896233796121/20000000000000 : ℝ)*(sp3) + (7268565983/25000000000000 : ℝ)*(sp4) + (7025973743/50000000000000 : ℝ)*(sp7) + (373623805232023/25000000000000 : ℝ)*(f.failure) + (3005368535600941/100000000000000 : ℝ)*(f.sum) + (2938507382843/14241000000000000000000000000 : ℝ)*base66 + (4522923532135383749/1424100000000000000000000000000000 : ℝ)*base67 + (11763452241861716251/1424100000000000000000000000000000 : ℝ)*base70 + (713090204246816251/1424100000000000000000000000000000 : ℝ)*base72 + (56295655155169/14241000000000000000000000000 : ℝ)*base73 + (5856468318471483749/1424100000000000000000000000000000 : ℝ)*base75 + (2519617538325116251/1424100000000000000000000000000000 : ℝ)*base78 + (2750992995788883749/1424100000000000000000000000000000 : ℝ)*base79 + (6683498143147/1780125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (17234873/2500000000000000000000 : ℝ)*base89 + (17234873/2500000000000000000000 : ℝ)*base91 + (17234873/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (982123718065808040329172651/593375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156350459/25000000000000 : ℝ)*(base19) + (445910653/50000000000000 : ℝ)*(base23) + (3229629/6250000000000 : ℝ)*(upper2) + (49525937/50000000000000 : ℝ)*(upper3) + (18229969/50000000000000 : ℝ)*(upper5) + (1140150654630411/50000000000000 : ℝ)*(major0) + (1140150654630411/50000000000000 : ℝ)*(major1) + (1140150654630411/50000000000000 : ℝ)*(major2) + (5696158593/100000000000000 : ℝ)*(sp1) + (2029085923/20000000000000 : ℝ)*(sp2) + (1522967391006239/50000000000000 : ℝ)*(sp4) + (60918569209041/2000000000000 : ℝ)*(sp5) + (1522961872380779/50000000000000 : ℝ)*(sp6) + (23666684083399/1562500000000 : ℝ)*(sp7) + (23666684083399/1562500000000 : ℝ)*(f.failure) + (1522967391006239/50000000000000 : ℝ)*(f.sum) + (31252498340119/5933750000000000000000000000 : ℝ)*base65 + (13306070925253775261/1186750000000000000000000000000000 : ℝ)*base67 + (14909385296822275261/1186750000000000000000000000000000 : ℝ)*base69 + (9863576342347525261/1186750000000000000000000000000000 : ℝ)*base71 + (45525307504291/23735000000000000000000000000 : ℝ)*base73 + (6254073913865775261/1186750000000000000000000000000000 : ℝ)*base75 + (16019276056116025261/1186750000000000000000000000000000 : ℝ)*base77 + (6019426265851025261/1186750000000000000000000000000000 : ℝ)*base79 + (31473560101429/5933750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1809551/156250000000000000000 : ℝ)*base90 + (1809551/156250000000000000000 : ℝ)*base92 + (1809551/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1197_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20193/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (186/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (291/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1197_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1197_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (291/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1197_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1197_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1197_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8389/2048 : ℝ) ≤ p) (hpb : p ≤ (4195/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150547951/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (291/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1197_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1399_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:46.353228+00:00
-- url     : https://prove2.me/submissions/064a5812-799f-4fe7-860b-6a908e8082e3

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
theorem support_rectangle_w1399_s3_0 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-997236627/5000000000 : ℝ)*x 0 + (5420434171/10000000000 : ℝ)*x 1 + (5236357183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997236627/5000000000 : ℝ)^4359 ≤ (12157462470687/100000000000000 : ℝ)^3335 := by
    have hnat : (997236627 : ℕ)^4359*100000000000000^3335 ≤ 12157462470687^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997236627 5000000000 12157462470687 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420434171/10000000000 : ℝ)^4359 ≤ (11228201110161/25000000000000 : ℝ)^3335 := by
    have hnat : (5420434171 : ℕ)^4359*25000000000000^3335 ≤ 11228201110161^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420434171 10000000000 11228201110161 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236357183/10000000000 : ℝ)^4359 ≤ (8585946615179/20000000000000 : ℝ)^3335 := by
    have hnat : (5236357183 : ℕ)^4359*20000000000000^3335 ≤ 8585946615179^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236357183 10000000000 8585946615179 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-997236627/5000000000 : ℝ), (5420434171/10000000000 : ℝ), (5236357183/10000000000 : ℝ)] ![(12157462470687/100000000000000 : ℝ), (11228201110161/25000000000000 : ℝ), (8585946615179/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-997236627/5000000000 : ℝ)|^4359 ≤ (12157462470687/100000000000000 : ℝ)^3335
        have hw : |(-997236627/5000000000 : ℝ)|=(997236627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420434171/10000000000 : ℝ)|^4359 ≤ (11228201110161/25000000000000 : ℝ)^3335
        have hw : |(5420434171/10000000000 : ℝ)|=(5420434171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236357183/10000000000 : ℝ)|^4359 ≤ (8585946615179/20000000000000 : ℝ)^3335
        have hw : |(5236357183/10000000000 : ℝ)|=(5236357183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s3_1 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070136691/2000000000 : ℝ)*x 0 + (-2088426627/10000000000 : ℝ)*x 1 + (523635719/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070136691/2000000000 : ℝ)^4359 ≤ (44158903282001/100000000000000 : ℝ)^3335 := by
    have hnat : (1070136691 : ℕ)^4359*100000000000000^3335 ≤ 44158903282001^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070136691 2000000000 44158903282001 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088426627/10000000000 : ℝ)^4359 ≤ (258227271193/2000000000000 : ℝ)^3335 := by
    have hnat : (2088426627 : ℕ)^4359*2000000000000^3335 ≤ 258227271193^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088426627 10000000000 258227271193 2000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523635719/1000000000 : ℝ)^4359 ≤ (8585946630181/20000000000000 : ℝ)^3335 := by
    have hnat : (523635719 : ℕ)^4359*20000000000000^3335 ≤ 8585946630181^3335*1000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523635719 1000000000 8585946630181 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070136691/2000000000 : ℝ), (-2088426627/10000000000 : ℝ), (523635719/1000000000 : ℝ)] ![(44158903282001/100000000000000 : ℝ), (258227271193/2000000000000 : ℝ), (8585946630181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070136691/2000000000 : ℝ)|^4359 ≤ (44158903282001/100000000000000 : ℝ)^3335
        have hw : |(1070136691/2000000000 : ℝ)|=(1070136691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088426627/10000000000 : ℝ)|^4359 ≤ (258227271193/2000000000000 : ℝ)^3335
        have hw : |(-2088426627/10000000000 : ℝ)|=(2088426627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523635719/1000000000 : ℝ)|^4359 ≤ (8585946630181/20000000000000 : ℝ)^3335
        have hw : |(523635719/1000000000 : ℝ)|=(523635719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s3_2 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675341771/5000000000 : ℝ)*x 0 + (5236357141/10000000000 : ℝ)*x 1 + (-83537063/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675341771/5000000000 : ℝ)^4359 ≤ (44158904220469/100000000000000 : ℝ)^3335 := by
    have hnat : (2675341771 : ℕ)^4359*100000000000000^3335 ≤ 44158904220469^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675341771 5000000000 44158904220469 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236357141/10000000000 : ℝ)^4359 ≤ (42929732625837/100000000000000 : ℝ)^3335 := by
    have hnat : (5236357141 : ℕ)^4359*100000000000000^3335 ≤ 42929732625837^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236357141 10000000000 42929732625837 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83537063/400000000 : ℝ)^4359 ≤ (6455681569729/50000000000000 : ℝ)^3335 := by
    have hnat : (83537063 : ℕ)^4359*50000000000000^3335 ≤ 6455681569729^3335*400000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83537063 400000000 6455681569729 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675341771/5000000000 : ℝ), (5236357141/10000000000 : ℝ), (-83537063/400000000 : ℝ)] ![(44158904220469/100000000000000 : ℝ), (42929732625837/100000000000000 : ℝ), (6455681569729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675341771/5000000000 : ℝ)|^4359 ≤ (44158904220469/100000000000000 : ℝ)^3335
        have hw : |(2675341771/5000000000 : ℝ)|=(2675341771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236357141/10000000000 : ℝ)|^4359 ≤ (42929732625837/100000000000000 : ℝ)^3335
        have hw : |(5236357141/10000000000 : ℝ)|=(5236357141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83537063/400000000 : ℝ)|^4359 ≤ (6455681569729/50000000000000 : ℝ)^3335
        have hw : |(-83537063/400000000 : ℝ)|=(83537063/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s3_3 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538895591/1250000000 : ℝ)*x 0 + (2059168999/5000000000 : ℝ)*x 1 + (902437023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538895591/1250000000 : ℝ)^4359 ≤ (8324117286141/25000000000000 : ℝ)^3335 := by
    have hnat : (538895591 : ℕ)^4359*25000000000000^3335 ≤ 8324117286141^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538895591 1250000000 8324117286141 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2059168999/5000000000 : ℝ)^4359 ≤ (1960215178701/6250000000000 : ℝ)^3335 := by
    have hnat : (2059168999 : ℕ)^4359*6250000000000^3335 ≤ 1960215178701^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059168999 5000000000 1960215178701 6250000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902437023/2000000000 : ℝ)^4359 ≤ (88350219971/250000000000 : ℝ)^3335 := by
    have hnat : (902437023 : ℕ)^4359*250000000000^3335 ≤ 88350219971^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902437023 2000000000 88350219971 250000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538895591/1250000000 : ℝ), (2059168999/5000000000 : ℝ), (902437023/2000000000 : ℝ)] ![(8324117286141/25000000000000 : ℝ), (1960215178701/6250000000000 : ℝ), (88350219971/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538895591/1250000000 : ℝ)|^4359 ≤ (8324117286141/25000000000000 : ℝ)^3335
        have hw : |(538895591/1250000000 : ℝ)|=(538895591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2059168999/5000000000 : ℝ)|^4359 ≤ (1960215178701/6250000000000 : ℝ)^3335
        have hw : |(2059168999/5000000000 : ℝ)|=(2059168999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902437023/2000000000 : ℝ)|^4359 ≤ (88350219971/250000000000 : ℝ)^3335
        have hw : |(902437023/2000000000 : ℝ)|=(902437023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s3_4 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-24931127/125000000 : ℝ)*x 0 + (5237101807/10000000000 : ℝ)*x 1 + (1083936987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24931127/125000000 : ℝ)^4359 ≤ (2431519432871/20000000000000 : ℝ)^3335 := by
    have hnat : (24931127 : ℕ)^4359*20000000000000^3335 ≤ 2431519432871^3335*125000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24931127 125000000 2431519432871 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237101807/10000000000 : ℝ)^4359 ≤ (42937712406633/100000000000000 : ℝ)^3335 := by
    have hnat : (5237101807 : ℕ)^4359*100000000000000^3335 ≤ 42937712406633^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237101807 10000000000 42937712406633 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083936987/2000000000 : ℝ)^4359 ≤ (44904690411737/100000000000000 : ℝ)^3335 := by
    have hnat : (1083936987 : ℕ)^4359*100000000000000^3335 ≤ 44904690411737^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083936987 2000000000 44904690411737 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24931127/125000000 : ℝ), (5237101807/10000000000 : ℝ), (1083936987/2000000000 : ℝ)] ![(2431519432871/20000000000000 : ℝ), (42937712406633/100000000000000 : ℝ), (44904690411737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24931127/125000000 : ℝ)|^4359 ≤ (2431519432871/20000000000000 : ℝ)^3335
        have hw : |(-24931127/125000000 : ℝ)|=(24931127/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237101807/10000000000 : ℝ)|^4359 ≤ (42937712406633/100000000000000 : ℝ)^3335
        have hw : |(5237101807/10000000000 : ℝ)|=(5237101807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083936987/2000000000 : ℝ)|^4359 ≤ (44904690411737/100000000000000 : ℝ)^3335
        have hw : |(1083936987/2000000000 : ℝ)|=(1083936987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s3_5 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651486593/5000000000 : ℝ)*x 0 + (-1905098329/10000000000 : ℝ)*x 1 + (2709842713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651486593/5000000000 : ℝ)^4359 ≤ (21822479661781/50000000000000 : ℝ)^3335 := by
    have hnat : (2651486593 : ℕ)^4359*50000000000000^3335 ≤ 21822479661781^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651486593 5000000000 21822479661781 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1905098329/10000000000 : ℝ)^4359 ≤ (1145034493097/10000000000000 : ℝ)^3335 := by
    have hnat : (1905098329 : ℕ)^4359*10000000000000^3335 ≤ 1145034493097^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905098329 10000000000 1145034493097 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709842713/5000000000 : ℝ)^4359 ≤ (1796187829161/4000000000000 : ℝ)^3335 := by
    have hnat : (2709842713 : ℕ)^4359*4000000000000^3335 ≤ 1796187829161^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709842713 5000000000 1796187829161 4000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651486593/5000000000 : ℝ), (-1905098329/10000000000 : ℝ), (2709842713/5000000000 : ℝ)] ![(21822479661781/50000000000000 : ℝ), (1145034493097/10000000000000 : ℝ), (1796187829161/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651486593/5000000000 : ℝ)|^4359 ≤ (21822479661781/50000000000000 : ℝ)^3335
        have hw : |(2651486593/5000000000 : ℝ)|=(2651486593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1905098329/10000000000 : ℝ)|^4359 ≤ (1145034493097/10000000000000 : ℝ)^3335
        have hw : |(-1905098329/10000000000 : ℝ)|=(1905098329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709842713/5000000000 : ℝ)|^4359 ≤ (1796187829161/4000000000000 : ℝ)^3335
        have hw : |(2709842713/5000000000 : ℝ)|=(2709842713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s3_6 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651487099/5000000000 : ℝ)*x 0 + (541968467/1000000000 : ℝ)*x 1 + (-952548993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651487099/5000000000 : ℝ)^4359 ≤ (4364497021001/10000000000000 : ℝ)^3335 := by
    have hnat : (2651487099 : ℕ)^4359*10000000000000^3335 ≤ 4364497021001^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651487099 5000000000 4364497021001 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541968467/1000000000 : ℝ)^4359 ≤ (22452343770959/50000000000000 : ℝ)^3335 := by
    have hnat : (541968467 : ℕ)^4359*50000000000000^3335 ≤ 22452343770959^3335*1000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541968467 1000000000 22452343770959 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (952548993/5000000000 : ℝ)^4359 ≤ (572517111821/5000000000000 : ℝ)^3335 := by
    have hnat : (952548993 : ℕ)^4359*5000000000000^3335 ≤ 572517111821^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952548993 5000000000 572517111821 5000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651487099/5000000000 : ℝ), (541968467/1000000000 : ℝ), (-952548993/5000000000 : ℝ)] ![(4364497021001/10000000000000 : ℝ), (22452343770959/50000000000000 : ℝ), (572517111821/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651487099/5000000000 : ℝ)|^4359 ≤ (4364497021001/10000000000000 : ℝ)^3335
        have hw : |(2651487099/5000000000 : ℝ)|=(2651487099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541968467/1000000000 : ℝ)|^4359 ≤ (22452343770959/50000000000000 : ℝ)^3335
        have hw : |(541968467/1000000000 : ℝ)|=(541968467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-952548993/5000000000 : ℝ)|^4359 ≤ (572517111821/5000000000000 : ℝ)^3335
        have hw : |(-952548993/5000000000 : ℝ)|=(952548993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s3_7 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538900147/1250000000 : ℝ)*x 0 + (180423663/400000000 : ℝ)*x 1 + (411993971/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538900147/1250000000 : ℝ)^4359 ≤ (6659367415533/20000000000000 : ℝ)^3335 := by
    have hnat : (538900147 : ℕ)^4359*20000000000000^3335 ≤ 6659367415533^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538900147 1250000000 6659367415533 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180423663/400000000 : ℝ)^4359 ≤ (35323775839823/100000000000000 : ℝ)^3335 := by
    have hnat : (180423663 : ℕ)^4359*100000000000000^3335 ≤ 35323775839823^3335*400000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180423663 400000000 35323775839823 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411993971/1000000000 : ℝ)^4359 ≤ (6275877414767/20000000000000 : ℝ)^3335 := by
    have hnat : (411993971 : ℕ)^4359*20000000000000^3335 ≤ 6275877414767^3335*1000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411993971 1000000000 6275877414767 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538900147/1250000000 : ℝ), (180423663/400000000 : ℝ), (411993971/1000000000 : ℝ)] ![(6659367415533/20000000000000 : ℝ), (35323775839823/100000000000000 : ℝ), (6275877414767/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538900147/1250000000 : ℝ)|^4359 ≤ (6659367415533/20000000000000 : ℝ)^3335
        have hw : |(538900147/1250000000 : ℝ)|=(538900147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180423663/400000000 : ℝ)|^4359 ≤ (35323775839823/100000000000000 : ℝ)^3335
        have hw : |(180423663/400000000 : ℝ)|=(180423663/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(411993971/1000000000 : ℝ)|^4359 ≤ (6275877414767/20000000000000 : ℝ)^3335
        have hw : |(411993971/1000000000 : ℝ)|=(411993971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1399_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11067/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3741/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1987/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1987/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1987/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1987/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1987/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1987/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10201/100000 : ℝ) ^ (2179/512 : ℝ) ≤ (603841480445879/10000000000000000000 : ℝ) := by
    have hpowers : (10201/100000 : ℝ)^2179 ≤ (603841480445879/10000000000000000000 : ℝ)^512 := by
      have hnat : (10201 : ℕ)^2179*10000000000000000000^512 ≤ 603841480445879^512*100000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10201 100000 603841480445879 10000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10201/100000 : ℝ)) (X := (603841480445879/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1987/12500 : ℝ) ^ (2179/512 : ℝ) ≤ (1595340598298549/4000000000000000000 : ℝ) := by
    have hpowers : (1987/12500 : ℝ)^2179 ≤ (1595340598298549/4000000000000000000 : ℝ)^512 := by
      have hnat : (1987 : ℕ)^2179*4000000000000000000^512 ≤ 1595340598298549^512*12500^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1987 12500 1595340598298549 4000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1987/12500 : ℝ)) (X := (1595340598298549/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000603841480445879/5000000000000000000 : ℝ) ≤ (5000141878181199/5000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (5000603841480445879/5000000000000000000 : ℝ)^512 ≤ (5000141878181199/5000000000000000 : ℝ)^2179 := by
      have hnat : (5000603841480445879 : ℕ)^512*5000000000000000^2179 ≤ 5000141878181199^2179*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000603841480445879 5000000000000000000 5000141878181199 5000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141878181199/5000000000000000 : ℝ)) (X := (5000603841480445879/5000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009184385952384503/20000000000000000000 : ℝ) ≤ (10001078838874363/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (20009184385952384503/20000000000000000000 : ℝ)^512 ≤ (10001078838874363/10000000000000000 : ℝ)^2179 := by
      have hnat : (20009184385952384503 : ℕ)^512*10000000000000000^2179 ≤ 10001078838874363^2179*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009184385952384503 20000000000000000000 10001078838874363 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001078838874363/10000000000000000 : ℝ)) (X := (20009184385952384503/20000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001595340598298549/2000000000000000000 : ℝ) ≤ (1250234240173291/1250000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (2001595340598298549/2000000000000000000 : ℝ)^512 ≤ (1250234240173291/1250000000000000 : ℝ)^2179 := by
      have hnat : (2001595340598298549 : ℕ)^512*1250000000000000^2179 ≤ 1250234240173291^2179*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001595340598298549 2000000000000000000 1250234240173291 1250000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250234240173291/1250000000000000 : ℝ)) (X := (2001595340598298549/2000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(603841480445879/10000000000000000000 : ℝ) ≤ ((1423384867976868667/1423750000000000000 : ℝ)+2*(159016502393/113900000000000 : ℝ)*(10201/100000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (1423384867976868667/1423750000000000000 : ℝ)+2*(159016502393/113900000000000 : ℝ)*(10201/100000 : ℝ)=(5000141878181199/5000000000000000 : ℝ) by norm_num, show 1+2*(603841480445879/10000000000000000000 : ℝ)=(5000603841480445879/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1595340598298549/4000000000000000000 : ℝ)+(603841480445879/10000000000000000000 : ℝ) ≤ ((1423384867976868667/1423750000000000000 : ℝ)+(159016502393/113900000000000 : ℝ)*((1987/12500 : ℝ)+(10201/100000 : ℝ)))^(2179/512 : ℝ) := by
    rw [show (1423384867976868667/1423750000000000000 : ℝ)+(159016502393/113900000000000 : ℝ)*((1987/12500 : ℝ)+(10201/100000 : ℝ))=(10001078838874363/10000000000000000 : ℝ) by norm_num, show 1+(1595340598298549/4000000000000000000 : ℝ)+(603841480445879/10000000000000000000 : ℝ)=(20009184385952384503/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1595340598298549/4000000000000000000 : ℝ) ≤ ((1423384867976868667/1423750000000000000 : ℝ)+2*(159016502393/113900000000000 : ℝ)*(1987/12500 : ℝ))^(2179/512 : ℝ) := by
    rw [show (1423384867976868667/1423750000000000000 : ℝ)+2*(159016502393/113900000000000 : ℝ)*(1987/12500 : ℝ)=(1250234240173291/1250000000000000 : ℝ) by norm_num, show 1+2*(1595340598298549/4000000000000000000 : ℝ)=(2001595340598298549/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1423384867976868667/1423750000000000000 : ℝ)*(X 1 0+X 2 0)+(159016502393/113900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (10201/100000 : ℝ)) (hi := (1987/12500 : ℝ)) (c := (1423384867976868667/1423750000000000000 : ℝ)) (alpha := (159016502393/113900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1423384867976868667/1423750000000000000 : ℝ)*(X 0 1+X 2 1)+(159016502393/113900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (10201/100000 : ℝ)) (hi := (1987/12500 : ℝ)) (c := (1423384867976868667/1423750000000000000 : ℝ)) (alpha := (159016502393/113900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1423384867976868667/1423750000000000000 : ℝ)*(X 0 2+X 1 2)+(159016502393/113900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (10201/100000 : ℝ)) (hi := (1987/12500 : ℝ)) (c := (1423384867976868667/1423750000000000000 : ℝ)) (alpha := (159016502393/113900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-997236627/5000000000 : ℝ)*X 0 0+(5420434171/10000000000 : ℝ)*X 0 1+(5236357183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070136691/2000000000 : ℝ)*X 1 0+(-2088426627/10000000000 : ℝ)*X 1 1+(523635719/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675341771/5000000000 : ℝ)*X 2 0+(5236357141/10000000000 : ℝ)*X 2 1+(-83537063/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((538895591/1250000000 : ℝ)*X 0 0+(2059168999/5000000000 : ℝ)*X 0 1+(902437023/2000000000 : ℝ)*X 0 2+(538895591/1250000000 : ℝ)*X 1 0+(2059168999/5000000000 : ℝ)*X 1 1+(902437023/2000000000 : ℝ)*X 1 2+(538895591/1250000000 : ℝ)*X 2 0+(2059168999/5000000000 : ℝ)*X 2 1+(902437023/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-24931127/125000000 : ℝ)*X 0 0+(5237101807/10000000000 : ℝ)*X 0 1+(1083936987/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651486593/5000000000 : ℝ)*X 1 0+(-1905098329/10000000000 : ℝ)*X 1 1+(2709842713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651487099/5000000000 : ℝ)*X 2 0+(541968467/1000000000 : ℝ)*X 2 1+(-952548993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538900147/1250000000 : ℝ)*X 0 0+(180423663/400000000 : ℝ)*X 0 1+(411993971/1000000000 : ℝ)*X 0 2+(538900147/1250000000 : ℝ)*X 1 0+(180423663/400000000 : ℝ)*X 1 1+(411993971/1000000000 : ℝ)*X 1 2+(538900147/1250000000 : ℝ)*X 2 0+(180423663/400000000 : ℝ)*X 2 1+(411993971/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112116559850186847058138377/17796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113546981/10000000000000 : ℝ)*(base19) + (1155145261/100000000000000 : ℝ)*(base23) + (36735477/100000000000000 : ℝ)*(lower2) + (137959801/100000000000000 : ℝ)*(upper3) + (80191559/50000000000000 : ℝ)*(upper5) + (498226691910249/12500000000000 : ℝ)*(major0) + (498226691910249/12500000000000 : ℝ)*(major1) + (498226691910249/12500000000000 : ℝ)*(major2) + (5432529427200903/100000000000000 : ℝ)*(sp0) + (679068809779749/12500000000000 : ℝ)*(sp1) + (2716275229281271/50000000000000 : ℝ)*(sp2) + (2539065603544979/100000000000000 : ℝ)*(sp3) + (221865069/1000000000000 : ℝ)*(sp4) + (4821659109/50000000000000 : ℝ)*(sp7) + (634768811715799/25000000000000 : ℝ)*(f.failure) + (5432551613707803/100000000000000 : ℝ)*(f.sum) + (17135563661077/2847500000000000000000000000 : ℝ)*base66 + (22553714605639677/4449218750000000000000000000000 : ℝ)*base67 + (175313072043636833/17796875000000000000000000000000 : ℝ)*base69 + (91015765226230583/17796875000000000000000000000000 : ℝ)*base71 + (5130087057/44492187500000000000000000 : ℝ)*base73 + (4720851742546401/2224609375000000000000000000000 : ℝ)*base75 + (177899668198081917/17796875000000000000000000000000 : ℝ)*base78 + (139108335336050667/17796875000000000000000000000000 : ℝ)*base80 + (24391940084931/5695000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6629589/500000000000000000000 : ℝ)*base90 + (6629589/500000000000000000000 : ℝ)*base92 + (6629589/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12741006240083972865903693/17796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42184977/2500000000000 : ℝ)*(base19) + (3064965397/100000000000000 : ℝ)*(base23) + (75828927/20000000000000 : ℝ)*(upper3) + (175739/250000000000 : ℝ)*(lower4) + (97852119/50000000000000 : ℝ)*(upper5) + (2009196867366807/50000000000000 : ℝ)*(major0) + (2009196867366807/50000000000000 : ℝ)*(major1) + (2009196867366807/50000000000000 : ℝ)*(major2) + (18072934737/50000000000000 : ℝ)*(sp1) + (29177641989/50000000000000 : ℝ)*(sp2) + (5476957695993663/100000000000000 : ℝ)*(sp4) + (5476919862725109/100000000000000 : ℝ)*(sp5) + (5476896275744287/100000000000000 : ℝ)*(sp6) + (511965949921961/20000000000000 : ℝ)*(sp7) + (511965949921961/20000000000000 : ℝ)*(f.failure) + (5476957695993663/100000000000000 : ℝ)*(f.sum) + (14773744845651/2847500000000000000000000000 : ℝ)*base65 + (736122439523273769/71187500000000000000000000000000 : ℝ)*base67 + (70919278715711269/71187500000000000000000000000000 : ℝ)*base69 + (126603054622523769/71187500000000000000000000000000 : ℝ)*base71 + (11132386858091/2847500000000000000000000000 : ℝ)*base73 + (949628407536273769/71187500000000000000000000000000 : ℝ)*base75 + (15096871325101231/71187500000000000000000000000000 : ℝ)*base78 + (791697228933711269/71187500000000000000000000000000 : ℝ)*base79 + (101926498237/355937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1977771/400000000000000000000 : ℝ)*base90 + (1977771/400000000000000000000 : ℝ)*base92 + (1977771/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1399_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11067/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3741/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1399_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1399_s4_0 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-997769443/5000000000 : ℝ)*x 0 + (5411471911/10000000000 : ℝ)*x 1 + (5244618353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997769443/5000000000 : ℝ)^4359 ≤ (6082976635457/50000000000000 : ℝ)^3335 := by
    have hnat : (997769443 : ℕ)^4359*50000000000000^3335 ≤ 6082976635457^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997769443 5000000000 6082976635457 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411471911/10000000000 : ℝ)^4359 ≤ (22407884054241/50000000000000 : ℝ)^3335 := by
    have hnat : (5411471911 : ℕ)^4359*50000000000000^3335 ≤ 22407884054241^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411471911 10000000000 22407884054241 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244618353/10000000000 : ℝ)^4359 ≤ (43018278608223/100000000000000 : ℝ)^3335 := by
    have hnat : (5244618353 : ℕ)^4359*100000000000000^3335 ≤ 43018278608223^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244618353 10000000000 43018278608223 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-997769443/5000000000 : ℝ), (5411471911/10000000000 : ℝ), (5244618353/10000000000 : ℝ)] ![(6082976635457/50000000000000 : ℝ), (22407884054241/50000000000000 : ℝ), (43018278608223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-997769443/5000000000 : ℝ)|^4359 ≤ (6082976635457/50000000000000 : ℝ)^3335
        have hw : |(-997769443/5000000000 : ℝ)|=(997769443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411471911/10000000000 : ℝ)|^4359 ≤ (22407884054241/50000000000000 : ℝ)^3335
        have hw : |(5411471911/10000000000 : ℝ)|=(5411471911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244618353/10000000000 : ℝ)|^4359 ≤ (43018278608223/100000000000000 : ℝ)^3335
        have hw : |(5244618353/10000000000 : ℝ)|=(5244618353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s4_1 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348379483/10000000000 : ℝ)*x 0 + (-130033697/625000000 : ℝ)*x 1 + (5244618763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348379483/10000000000 : ℝ)^4359 ≤ (11033513003769/25000000000000 : ℝ)^3335 := by
    have hnat : (5348379483 : ℕ)^4359*25000000000000^3335 ≤ 11033513003769^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348379483 10000000000 11033513003769 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130033697/625000000 : ℝ)^4359 ≤ (12847664971087/100000000000000 : ℝ)^3335 := by
    have hnat : (130033697 : ℕ)^4359*100000000000000^3335 ≤ 12847664971087^3335*625000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130033697 625000000 12847664971087 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244618763/10000000000 : ℝ)^4359 ≤ (43018283003781/100000000000000 : ℝ)^3335 := by
    have hnat : (5244618763 : ℕ)^4359*100000000000000^3335 ≤ 43018283003781^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244618763 10000000000 43018283003781 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348379483/10000000000 : ℝ), (-130033697/625000000 : ℝ), (5244618763/10000000000 : ℝ)] ![(11033513003769/25000000000000 : ℝ), (12847664971087/100000000000000 : ℝ), (43018283003781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348379483/10000000000 : ℝ)|^4359 ≤ (11033513003769/25000000000000 : ℝ)^3335
        have hw : |(5348379483/10000000000 : ℝ)|=(5348379483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130033697/625000000 : ℝ)|^4359 ≤ (12847664971087/100000000000000 : ℝ)^3335
        have hw : |(-130033697/625000000 : ℝ)|=(130033697/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244618763/10000000000 : ℝ)|^4359 ≤ (43018283003781/100000000000000 : ℝ)^3335
        have hw : |(5244618763/10000000000 : ℝ)|=(5244618763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s4_2 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534837973/1000000000 : ℝ)*x 0 + (163894331/312500000 : ℝ)*x 1 + (-260067381/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534837973/1000000000 : ℝ)^4359 ≤ (44134054679109/100000000000000 : ℝ)^3335 := by
    have hnat : (534837973 : ℕ)^4359*100000000000000^3335 ≤ 44134054679109^3335*1000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534837973 1000000000 44134054679109 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163894331/312500000 : ℝ)^4359 ≤ (2688642573157/6250000000000 : ℝ)^3335 := by
    have hnat : (163894331 : ℕ)^4359*6250000000000^3335 ≤ 2688642573157^3335*312500000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163894331 312500000 2688642573157 6250000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260067381/1250000000 : ℝ)^4359 ≤ (80297900823/625000000000 : ℝ)^3335 := by
    have hnat : (260067381 : ℕ)^4359*625000000000^3335 ≤ 80297900823^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260067381 1250000000 80297900823 625000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534837973/1000000000 : ℝ), (163894331/312500000 : ℝ), (-260067381/1250000000 : ℝ)] ![(44134054679109/100000000000000 : ℝ), (2688642573157/6250000000000 : ℝ), (80297900823/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534837973/1000000000 : ℝ)|^4359 ≤ (44134054679109/100000000000000 : ℝ)^3335
        have hw : |(534837973/1000000000 : ℝ)|=(534837973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163894331/312500000 : ℝ)|^4359 ≤ (2688642573157/6250000000000 : ℝ)^3335
        have hw : |(163894331/312500000 : ℝ)|=(163894331/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260067381/1250000000 : ℝ)|^4359 ≤ (80297900823/625000000000 : ℝ)^3335
        have hw : |(-260067381/1250000000 : ℝ)|=(260067381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s4_3 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077953921/2500000000 : ℝ)*x 0 + (2068342139/5000000000 : ℝ)*x 1 + (4493680399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077953921/2500000000 : ℝ)^4359 ≤ (8325760130063/25000000000000 : ℝ)^3335 := by
    have hnat : (1077953921 : ℕ)^4359*25000000000000^3335 ≤ 8325760130063^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077953921 2500000000 8325760130063 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068342139/5000000000 : ℝ)^4359 ≤ (3154618445139/10000000000000 : ℝ)^3335 := by
    have hnat : (2068342139 : ℕ)^4359*10000000000000^3335 ≤ 3154618445139^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068342139 5000000000 3154618445139 10000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493680399/10000000000 : ℝ)^4359 ≤ (1406031000329/4000000000000 : ℝ)^3335 := by
    have hnat : (4493680399 : ℕ)^4359*4000000000000^3335 ≤ 1406031000329^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493680399 10000000000 1406031000329 4000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077953921/2500000000 : ℝ), (2068342139/5000000000 : ℝ), (4493680399/10000000000 : ℝ)] ![(8325760130063/25000000000000 : ℝ), (3154618445139/10000000000000 : ℝ), (1406031000329/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077953921/2500000000 : ℝ)|^4359 ≤ (8325760130063/25000000000000 : ℝ)^3335
        have hw : |(1077953921/2500000000 : ℝ)|=(1077953921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2068342139/5000000000 : ℝ)|^4359 ≤ (3154618445139/10000000000000 : ℝ)^3335
        have hw : |(2068342139/5000000000 : ℝ)|=(2068342139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493680399/10000000000 : ℝ)|^4359 ≤ (1406031000329/4000000000000 : ℝ)^3335
        have hw : |(4493680399/10000000000 : ℝ)|=(4493680399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s4_4 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-997775533/5000000000 : ℝ)*x 0 + (2622615293/5000000000 : ℝ)*x 1 + (5410856549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997775533/5000000000 : ℝ)^4359 ≤ (95047268183/781250000000 : ℝ)^3335 := by
    have hnat : (997775533 : ℕ)^4359*781250000000^3335 ≤ 95047268183^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997775533 5000000000 95047268183 781250000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622615293/5000000000 : ℝ)^4359 ≤ (43024842398347/100000000000000 : ℝ)^3335 := by
    have hnat : (2622615293 : ℕ)^4359*100000000000000^3335 ≤ 43024842398347^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622615293 5000000000 43024842398347 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410856549/10000000000 : ℝ)^4359 ≤ (2240455362997/5000000000000 : ℝ)^3335 := by
    have hnat : (5410856549 : ℕ)^4359*5000000000000^3335 ≤ 2240455362997^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410856549 10000000000 2240455362997 5000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-997775533/5000000000 : ℝ), (2622615293/5000000000 : ℝ), (5410856549/10000000000 : ℝ)] ![(95047268183/781250000000 : ℝ), (43024842398347/100000000000000 : ℝ), (2240455362997/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-997775533/5000000000 : ℝ)|^4359 ≤ (95047268183/781250000000 : ℝ)^3335
        have hw : |(-997775533/5000000000 : ℝ)|=(997775533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622615293/5000000000 : ℝ)|^4359 ≤ (43024842398347/100000000000000 : ℝ)^3335
        have hw : |(2622615293/5000000000 : ℝ)|=(2622615293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410856549/10000000000 : ℝ)|^4359 ≤ (2240455362997/5000000000000 : ℝ)^3335
        have hw : |(5410856549/10000000000 : ℝ)|=(5410856549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s4_5 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663141679/1250000000 : ℝ)*x 0 + (-47857521/250000000 : ℝ)*x 1 + (5410856691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663141679/1250000000 : ℝ)^4359 ≤ (43668199320137/100000000000000 : ℝ)^3335 := by
    have hnat : (663141679 : ℕ)^4359*100000000000000^3335 ≤ 43668199320137^3335*1250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663141679 1250000000 43668199320137 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47857521/250000000 : ℝ)^4359 ≤ (288067296661/2500000000000 : ℝ)^3335 := by
    have hnat : (47857521 : ℕ)^4359*2500000000000^3335 ≤ 288067296661^3335*250000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47857521 250000000 288067296661 2500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410856691/10000000000 : ℝ)^4359 ≤ (44809108796961/100000000000000 : ℝ)^3335 := by
    have hnat : (5410856691 : ℕ)^4359*100000000000000^3335 ≤ 44809108796961^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410856691 10000000000 44809108796961 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663141679/1250000000 : ℝ), (-47857521/250000000 : ℝ), (5410856691/10000000000 : ℝ)] ![(43668199320137/100000000000000 : ℝ), (288067296661/2500000000000 : ℝ), (44809108796961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663141679/1250000000 : ℝ)|^4359 ≤ (43668199320137/100000000000000 : ℝ)^3335
        have hw : |(663141679/1250000000 : ℝ)|=(663141679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47857521/250000000 : ℝ)|^4359 ≤ (288067296661/2500000000000 : ℝ)^3335
        have hw : |(-47857521/250000000 : ℝ)|=(47857521/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410856691/10000000000 : ℝ)|^4359 ≤ (44809108796961/100000000000000 : ℝ)^3335
        have hw : |(5410856691/10000000000 : ℝ)|=(5410856691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s4_6 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331570837/625000000 : ℝ)*x 0 + (43286853/80000000 : ℝ)*x 1 + (-957150493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331570837/625000000 : ℝ)^4359 ≤ (43668198889789/100000000000000 : ℝ)^3335 := by
    have hnat : (331570837 : ℕ)^4359*100000000000000^3335 ≤ 43668198889789^3335*625000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331570837 625000000 43668198889789 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43286853/80000000 : ℝ)^4359 ≤ (44809108082571/100000000000000 : ℝ)^3335 := by
    have hnat : (43286853 : ℕ)^4359*100000000000000^3335 ≤ 44809108082571^3335*80000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43286853 80000000 44809108082571 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957150493/5000000000 : ℝ)^4359 ≤ (11522693015089/100000000000000 : ℝ)^3335 := by
    have hnat : (957150493 : ℕ)^4359*100000000000000^3335 ≤ 11522693015089^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957150493 5000000000 11522693015089 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331570837/625000000 : ℝ), (43286853/80000000 : ℝ), (-957150493/5000000000 : ℝ)] ![(43668198889789/100000000000000 : ℝ), (44809108082571/100000000000000 : ℝ), (11522693015089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331570837/625000000 : ℝ)|^4359 ≤ (43668198889789/100000000000000 : ℝ)^3335
        have hw : |(331570837/625000000 : ℝ)|=(331570837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43286853/80000000 : ℝ)|^4359 ≤ (44809108082571/100000000000000 : ℝ)^3335
        have hw : |(43286853/80000000 : ℝ)|=(43286853/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-957150493/5000000000 : ℝ)|^4359 ≤ (11522693015089/100000000000000 : ℝ)^3335
        have hw : |(-957150493/5000000000 : ℝ)|=(957150493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s4_7 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2155920947/5000000000 : ℝ)*x 0 + (4492370649/10000000000 : ℝ)*x 1 + (165520043/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155920947/5000000000 : ℝ)^4359 ≤ (33303305115569/100000000000000 : ℝ)^3335 := by
    have hnat : (2155920947 : ℕ)^4359*100000000000000^3335 ≤ 33303305115569^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155920947 5000000000 33303305115569 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492370649/10000000000 : ℝ)^4359 ≤ (8784346158407/25000000000000 : ℝ)^3335 := by
    have hnat : (4492370649 : ℕ)^4359*25000000000000^3335 ≤ 8784346158407^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492370649 10000000000 8784346158407 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165520043/400000000 : ℝ)^4359 ≤ (3944913780521/12500000000000 : ℝ)^3335 := by
    have hnat : (165520043 : ℕ)^4359*12500000000000^3335 ≤ 3944913780521^3335*400000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165520043 400000000 3944913780521 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155920947/5000000000 : ℝ), (4492370649/10000000000 : ℝ), (165520043/400000000 : ℝ)] ![(33303305115569/100000000000000 : ℝ), (8784346158407/25000000000000 : ℝ), (3944913780521/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155920947/5000000000 : ℝ)|^4359 ≤ (33303305115569/100000000000000 : ℝ)^3335
        have hw : |(2155920947/5000000000 : ℝ)|=(2155920947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492370649/10000000000 : ℝ)|^4359 ≤ (8784346158407/25000000000000 : ℝ)^3335
        have hw : |(4492370649/10000000000 : ℝ)|=(4492370649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165520043/400000000 : ℝ)|^4359 ≤ (3944913780521/12500000000000 : ℝ)^3335
        have hw : |(165520043/400000000 : ℝ)|=(165520043/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1399_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3741/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14777/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3741/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3741/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3741/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3741/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3741/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3741/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11067/100000 : ℝ) ^ (2179/512 : ℝ) ≤ (8541334495464521/100000000000000000000 : ℝ) := by
    have hpowers : (11067/100000 : ℝ)^2179 ≤ (8541334495464521/100000000000000000000 : ℝ)^512 := by
      have hnat : (11067 : ℕ)^2179*100000000000000000000^512 ≤ 8541334495464521^512*100000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11067 100000 8541334495464521 100000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11067/100000 : ℝ)) (X := (8541334495464521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3741/25000 : ℝ) ^ (2179/512 : ℝ) ≤ (7710082528877647/25000000000000000000 : ℝ) := by
    have hpowers : (3741/25000 : ℝ)^2179 ≤ (7710082528877647/25000000000000000000 : ℝ)^512 := by
      have hnat : (3741 : ℕ)^2179*25000000000000000000^512 ≤ 7710082528877647^512*25000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3741 25000 7710082528877647 25000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3741/25000 : ℝ)) (X := (7710082528877647/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008541334495464521/50000000000000000000 : ℝ) ≤ (10000401365537539/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (50008541334495464521/50000000000000000000 : ℝ)^512 ≤ (10000401365537539/10000000000000000 : ℝ)^2179 := by
      have hnat : (50008541334495464521 : ℕ)^512*10000000000000000^2179 ≤ 10000401365537539^2179*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008541334495464521 50000000000000000000 10000401365537539 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000401365537539/10000000000000000 : ℝ)) (X := (50008541334495464521/50000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039381664610975109/100000000000000000000 : ℝ) ≤ (2500231303069677/2500000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (100039381664610975109/100000000000000000000 : ℝ)^512 ≤ (2500231303069677/2500000000000000 : ℝ)^2179 := by
      have hnat : (100039381664610975109 : ℕ)^512*2500000000000000^2179 ≤ 2500231303069677^2179*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039381664610975109 100000000000000000000 2500231303069677 2500000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500231303069677/2500000000000000 : ℝ)) (X := (100039381664610975109/100000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507710082528877647/12500000000000000000 : ℝ) ≤ (10001449059019877/10000000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (12507710082528877647/12500000000000000000 : ℝ)^512 ≤ (10001449059019877/10000000000000000 : ℝ)^2179 := by
      have hnat : (12507710082528877647 : ℕ)^512*10000000000000000^2179 ≤ 10001449059019877^2179*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507710082528877647 12500000000000000000 10001449059019877 10000000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001449059019877/10000000000000000 : ℝ)) (X := (12507710082528877647/12500000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8541334495464521/100000000000000000000 : ℝ) ≤ ((12986656432576918279/12990000000000000000 : ℝ)+2*(523846741169/389700000000000 : ℝ)*(11067/100000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (12986656432576918279/12990000000000000000 : ℝ)+2*(523846741169/389700000000000 : ℝ)*(11067/100000 : ℝ)=(10000401365537539/10000000000000000 : ℝ) by norm_num, show 1+2*(8541334495464521/100000000000000000000 : ℝ)=(50008541334495464521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7710082528877647/25000000000000000000 : ℝ)+(8541334495464521/100000000000000000000 : ℝ) ≤ ((12986656432576918279/12990000000000000000 : ℝ)+(523846741169/389700000000000 : ℝ)*((3741/25000 : ℝ)+(11067/100000 : ℝ)))^(2179/512 : ℝ) := by
    rw [show (12986656432576918279/12990000000000000000 : ℝ)+(523846741169/389700000000000 : ℝ)*((3741/25000 : ℝ)+(11067/100000 : ℝ))=(2500231303069677/2500000000000000 : ℝ) by norm_num, show 1+(7710082528877647/25000000000000000000 : ℝ)+(8541334495464521/100000000000000000000 : ℝ)=(100039381664610975109/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7710082528877647/25000000000000000000 : ℝ) ≤ ((12986656432576918279/12990000000000000000 : ℝ)+2*(523846741169/389700000000000 : ℝ)*(3741/25000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (12986656432576918279/12990000000000000000 : ℝ)+2*(523846741169/389700000000000 : ℝ)*(3741/25000 : ℝ)=(10001449059019877/10000000000000000 : ℝ) by norm_num, show 1+2*(7710082528877647/25000000000000000000 : ℝ)=(12507710082528877647/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12986656432576918279/12990000000000000000 : ℝ)*(X 1 0+X 2 0)+(523846741169/389700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (11067/100000 : ℝ)) (hi := (3741/25000 : ℝ)) (c := (12986656432576918279/12990000000000000000 : ℝ)) (alpha := (523846741169/389700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12986656432576918279/12990000000000000000 : ℝ)*(X 0 1+X 2 1)+(523846741169/389700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (11067/100000 : ℝ)) (hi := (3741/25000 : ℝ)) (c := (12986656432576918279/12990000000000000000 : ℝ)) (alpha := (523846741169/389700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12986656432576918279/12990000000000000000 : ℝ)*(X 0 2+X 1 2)+(523846741169/389700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (11067/100000 : ℝ)) (hi := (3741/25000 : ℝ)) (c := (12986656432576918279/12990000000000000000 : ℝ)) (alpha := (523846741169/389700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-997769443/5000000000 : ℝ)*X 0 0+(5411471911/10000000000 : ℝ)*X 0 1+(5244618353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348379483/10000000000 : ℝ)*X 1 0+(-130033697/625000000 : ℝ)*X 1 1+(5244618763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534837973/1000000000 : ℝ)*X 2 0+(163894331/312500000 : ℝ)*X 2 1+(-260067381/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077953921/2500000000 : ℝ)*X 0 0+(2068342139/5000000000 : ℝ)*X 0 1+(4493680399/10000000000 : ℝ)*X 0 2+(1077953921/2500000000 : ℝ)*X 1 0+(2068342139/5000000000 : ℝ)*X 1 1+(4493680399/10000000000 : ℝ)*X 1 2+(1077953921/2500000000 : ℝ)*X 2 0+(2068342139/5000000000 : ℝ)*X 2 1+(4493680399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-997775533/5000000000 : ℝ)*X 0 0+(2622615293/5000000000 : ℝ)*X 0 1+(5410856549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663141679/1250000000 : ℝ)*X 1 0+(-47857521/250000000 : ℝ)*X 1 1+(5410856691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331570837/625000000 : ℝ)*X 2 0+(43286853/80000000 : ℝ)*X 2 1+(-957150493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155920947/5000000000 : ℝ)*X 0 0+(4492370649/10000000000 : ℝ)*X 0 1+(165520043/400000000 : ℝ)*X 0 2+(2155920947/5000000000 : ℝ)*X 1 0+(4492370649/10000000000 : ℝ)*X 1 1+(165520043/400000000 : ℝ)*X 1 2+(2155920947/5000000000 : ℝ)*X 2 0+(4492370649/10000000000 : ℝ)*X 2 1+(165520043/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3542312458513867960861508441/324750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47878417/3125000000000 : ℝ)*(base19) + (69463581/4000000000000 : ℝ)*(base23) + (9994901/4000000000000 : ℝ)*(upper3) + (4834019/12500000000000 : ℝ)*(upper4) + (373834651/100000000000000 : ℝ)*(upper5) + (2198636277432631/50000000000000 : ℝ)*(major0) + (2198636277432631/50000000000000 : ℝ)*(major1) + (2198636277432631/50000000000000 : ℝ)*(major2) + (5993314961445849/100000000000000 : ℝ)*(sp0) + (2996678503631179/50000000000000 : ℝ)*(sp1) + (187292400086943/3125000000000 : ℝ)*(sp2) + (700292187153167/25000000000000 : ℝ)*(sp3) + (43577925853/100000000000000 : ℝ)*(sp4) + (8729076181/50000000000000 : ℝ)*(sp7) + (280118620676503/10000000000000 : ℝ)*(f.failure) + (2996679269685851/50000000000000 : ℝ)*(f.sum) + (58212015499651/9742500000000000000000000000 : ℝ)*base66 + (10545084270532713853/1948500000000000000000000000000000 : ℝ)*base68 + (10301458906077213853/1948500000000000000000000000000000 : ℝ)*base70 + (14661671481510213853/1948500000000000000000000000000000 : ℝ)*base72 + (11096558801917/4871250000000000000000000000 : ℝ)*base73 + (9147742625337213853/1948500000000000000000000000000000 : ℝ)*base76 + (15048042597861213853/1948500000000000000000000000000000 : ℝ)*base78 + (8925937072440213853/1948500000000000000000000000000000 : ℝ)*base80 + (4524853140803/4871250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1445867/200000000000000000000 : ℝ)*base89 + (1445867/200000000000000000000 : ℝ)*base91 + (1445867/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3164809514556954843658108463/324750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (166107657/10000000000000 : ℝ)*(base19) + (1566666337/100000000000000 : ℝ)*(base23) + (306939/6250000000000 : ℝ)*(upper2) + (199105707/100000000000000 : ℝ)*(upper3) + (254399373/100000000000000 : ℝ)*(upper5) + (4429806877080899/100000000000000 : ℝ)*(major0) + (4429806877080899/100000000000000 : ℝ)*(major1) + (4429806877080899/100000000000000 : ℝ)*(major2) + (304966461/781250000000 : ℝ)*(sp1) + (1276111817/4000000000000 : ℝ)*(sp2) + (3018850972446583/50000000000000 : ℝ)*(sp4) + (1509415312027397/25000000000000 : ℝ)*(sp5) + (1509417118857851/25000000000000 : ℝ)*(sp6) + (1410955742211447/50000000000000 : ℝ)*(sp7) + (1410955742211447/50000000000000 : ℝ)*(f.failure) + (3018850972446583/50000000000000 : ℝ)*(f.sum) + (39635271965131/19485000000000000000000000000 : ℝ)*base65 + (8811039921876341537/3897000000000000000000000000000000 : ℝ)*base68 + (45752424234570341537/3897000000000000000000000000000000 : ℝ)*base70 + (34533463682574341537/3897000000000000000000000000000000 : ℝ)*base72 + (64001249071981/19485000000000000000000000000 : ℝ)*base73 + (23996080682063658463/3897000000000000000000000000000000 : ℝ)*base75 + (59035908616560341537/3897000000000000000000000000000000 : ℝ)*base78 + (24353904182004341537/3897000000000000000000000000000000 : ℝ)*base80 + (28782116766479/19485000000000000000000000000 : ℝ)*base82 + (6603317/1000000000000000000000 : ℝ)*base90 + (6603317/1000000000000000000000 : ℝ)*base92 + (6603317/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1399_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3741/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1399_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1399_s5_0 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-498926487/2500000000 : ℝ)*x 0 + (5410004161/10000000000 : ℝ)*x 1 + (1311493999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498926487/2500000000 : ℝ)^4359 ≤ (2433456904561/20000000000000 : ℝ)^3335 := by
    have hnat : (498926487 : ℕ)^4359*20000000000000^3335 ≤ 2433456904561^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498926487 2500000000 2433456904561 20000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410004161/10000000000 : ℝ)^4359 ≤ (11199970290157/25000000000000 : ℝ)^3335 := by
    have hnat : (5410004161 : ℕ)^4359*25000000000000^3335 ≤ 11199970290157^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410004161 10000000000 11199970290157 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311493999/2500000000 : ℝ)^4359 ≤ (43032834305383/100000000000000 : ℝ)^3335 := by
    have hnat : (1311493999 : ℕ)^4359*100000000000000^3335 ≤ 43032834305383^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311493999 2500000000 43032834305383 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-498926487/2500000000 : ℝ), (5410004161/10000000000 : ℝ), (1311493999/2500000000 : ℝ)] ![(2433456904561/20000000000000 : ℝ), (11199970290157/25000000000000 : ℝ), (43032834305383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-498926487/2500000000 : ℝ)|^4359 ≤ (2433456904561/20000000000000 : ℝ)^3335
        have hw : |(-498926487/2500000000 : ℝ)|=(498926487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410004161/10000000000 : ℝ)|^4359 ≤ (11199970290157/25000000000000 : ℝ)^3335
        have hw : |(5410004161/10000000000 : ℝ)|=(5410004161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311493999/2500000000 : ℝ)|^4359 ≤ (43032834305383/100000000000000 : ℝ)^3335
        have hw : |(1311493999/2500000000 : ℝ)|=(1311493999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s5_1 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337000621/2500000000 : ℝ)*x 0 + (-2079240693/10000000000 : ℝ)*x 1 + (5245975431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337000621/2500000000 : ℝ)^4359 ≤ (44129985914493/100000000000000 : ℝ)^3335 := by
    have hnat : (1337000621 : ℕ)^4359*100000000000000^3335 ≤ 44129985914493^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337000621 2500000000 44129985914493 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079240693/10000000000 : ℝ)^4359 ≤ (3209296455841/25000000000000 : ℝ)^3335 := by
    have hnat : (2079240693 : ℕ)^4359*25000000000000^3335 ≤ 3209296455841^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079240693 10000000000 3209296455841 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245975431/10000000000 : ℝ)^4359 ≤ (5379103530951/12500000000000 : ℝ)^3335 := by
    have hnat : (5245975431 : ℕ)^4359*12500000000000^3335 ≤ 5379103530951^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245975431 10000000000 5379103530951 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337000621/2500000000 : ℝ), (-2079240693/10000000000 : ℝ), (5245975431/10000000000 : ℝ)] ![(44129985914493/100000000000000 : ℝ), (3209296455841/25000000000000 : ℝ), (5379103530951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337000621/2500000000 : ℝ)|^4359 ≤ (44129985914493/100000000000000 : ℝ)^3335
        have hw : |(1337000621/2500000000 : ℝ)|=(1337000621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079240693/10000000000 : ℝ)|^4359 ≤ (3209296455841/25000000000000 : ℝ)^3335
        have hw : |(-2079240693/10000000000 : ℝ)|=(2079240693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245975431/10000000000 : ℝ)|^4359 ≤ (5379103530951/12500000000000 : ℝ)^3335
        have hw : |(5245975431/10000000000 : ℝ)|=(5245975431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s5_2 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348001337/10000000000 : ℝ)*x 0 + (5245976147/10000000000 : ℝ)*x 1 + (-1039620637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348001337/10000000000 : ℝ)^4359 ≤ (44129973543727/100000000000000 : ℝ)^3335 := by
    have hnat : (5348001337 : ℕ)^4359*100000000000000^3335 ≤ 44129973543727^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348001337 10000000000 44129973543727 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245976147/10000000000 : ℝ)^4359 ≤ (10758208981091/25000000000000 : ℝ)^3335 := by
    have hnat : (5245976147 : ℕ)^4359*25000000000000^3335 ≤ 10758208981091^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245976147 10000000000 10758208981091 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039620637/5000000000 : ℝ)^4359 ≤ (6418595255923/50000000000000 : ℝ)^3335 := by
    have hnat : (1039620637 : ℕ)^4359*50000000000000^3335 ≤ 6418595255923^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039620637 5000000000 6418595255923 50000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348001337/10000000000 : ℝ), (5245976147/10000000000 : ℝ), (-1039620637/5000000000 : ℝ)] ![(44129973543727/100000000000000 : ℝ), (10758208981091/25000000000000 : ℝ), (6418595255923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348001337/10000000000 : ℝ)|^4359 ≤ (44129973543727/100000000000000 : ℝ)^3335
        have hw : |(5348001337/10000000000 : ℝ)|=(5348001337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245976147/10000000000 : ℝ)|^4359 ≤ (10758208981091/25000000000000 : ℝ)^3335
        have hw : |(5245976147/10000000000 : ℝ)|=(5245976147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1039620637/5000000000 : ℝ)|^4359 ≤ (6418595255923/50000000000000 : ℝ)^3335
        have hw : |(-1039620637/5000000000 : ℝ)|=(1039620637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s5_3 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311915449/10000000000 : ℝ)*x 0 + (4139694273/10000000000 : ℝ)*x 1 + (2245323397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311915449/10000000000 : ℝ)^4359 ≤ (8326011917749/25000000000000 : ℝ)^3335 := by
    have hnat : (4311915449 : ℕ)^4359*25000000000000^3335 ≤ 8326011917749^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311915449 10000000000 8326011917749 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4139694273/10000000000 : ℝ)^4359 ≤ (31576189875607/100000000000000 : ℝ)^3335 := by
    have hnat : (4139694273 : ℕ)^4359*100000000000000^3335 ≤ 31576189875607^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139694273 10000000000 31576189875607 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245323397/5000000000 : ℝ)^4359 ≤ (8779940609407/25000000000000 : ℝ)^3335 := by
    have hnat : (2245323397 : ℕ)^4359*25000000000000^3335 ≤ 8779940609407^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245323397 5000000000 8779940609407 25000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311915449/10000000000 : ℝ), (4139694273/10000000000 : ℝ), (2245323397/5000000000 : ℝ)] ![(8326011917749/25000000000000 : ℝ), (31576189875607/100000000000000 : ℝ), (8779940609407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311915449/10000000000 : ℝ)|^4359 ≤ (8326011917749/25000000000000 : ℝ)^3335
        have hw : |(4311915449/10000000000 : ℝ)|=(4311915449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4139694273/10000000000 : ℝ)|^4359 ≤ (31576189875607/100000000000000 : ℝ)^3335
        have hw : |(4139694273/10000000000 : ℝ)|=(4139694273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245323397/5000000000 : ℝ)|^4359 ≤ (8779940609407/25000000000000 : ℝ)^3335
        have hw : |(2245323397/5000000000 : ℝ)|=(2245323397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s5_4 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-498929413/2500000000 : ℝ)*x 0 + (5246567439/10000000000 : ℝ)*x 1 + (2704704823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498929413/2500000000 : ℝ)^4359 ≤ (1520922223587/12500000000000 : ℝ)^3335 := by
    have hnat : (498929413 : ℕ)^4359*12500000000000^3335 ≤ 1520922223587^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498929413 2500000000 1520922223587 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246567439/10000000000 : ℝ)^4359 ≤ (43039175704617/100000000000000 : ℝ)^3335 := by
    have hnat : (5246567439 : ℕ)^4359*100000000000000^3335 ≤ 43039175704617^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246567439 10000000000 43039175704617 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704704823/5000000000 : ℝ)^4359 ≤ (44793446497979/100000000000000 : ℝ)^3335 := by
    have hnat : (2704704823 : ℕ)^4359*100000000000000^3335 ≤ 44793446497979^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704704823 5000000000 44793446497979 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-498929413/2500000000 : ℝ), (5246567439/10000000000 : ℝ), (2704704823/5000000000 : ℝ)] ![(1520922223587/12500000000000 : ℝ), (43039175704617/100000000000000 : ℝ), (44793446497979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-498929413/2500000000 : ℝ)|^4359 ≤ (1520922223587/12500000000000 : ℝ)^3335
        have hw : |(-498929413/2500000000 : ℝ)|=(498929413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246567439/10000000000 : ℝ)|^4359 ≤ (43039175704617/100000000000000 : ℝ)^3335
        have hw : |(5246567439/10000000000 : ℝ)|=(5246567439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704704823/5000000000 : ℝ)|^4359 ≤ (44793446497979/100000000000000 : ℝ)^3335
        have hw : |(2704704823/5000000000 : ℝ)|=(2704704823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s5_5 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652743777/5000000000 : ℝ)*x 0 + (-957903603/5000000000 : ℝ)*x 1 + (1081881923/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652743777/5000000000 : ℝ)^4359 ≤ (1364750289167/3125000000000 : ℝ)^3335 := by
    have hnat : (2652743777 : ℕ)^4359*3125000000000^3335 ≤ 1364750289167^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652743777 5000000000 1364750289167 3125000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957903603/5000000000 : ℝ)^4359 ≤ (576727228943/5000000000000 : ℝ)^3335 := by
    have hnat : (957903603 : ℕ)^4359*5000000000000^3335 ≤ 576727228943^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957903603 5000000000 576727228943 5000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081881923/2000000000 : ℝ)^4359 ≤ (44793446162459/100000000000000 : ℝ)^3335 := by
    have hnat : (1081881923 : ℕ)^4359*100000000000000^3335 ≤ 44793446162459^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081881923 2000000000 44793446162459 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652743777/5000000000 : ℝ), (-957903603/5000000000 : ℝ), (1081881923/2000000000 : ℝ)] ![(1364750289167/3125000000000 : ℝ), (576727228943/5000000000000 : ℝ), (44793446162459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652743777/5000000000 : ℝ)|^4359 ≤ (1364750289167/3125000000000 : ℝ)^3335
        have hw : |(2652743777/5000000000 : ℝ)|=(2652743777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-957903603/5000000000 : ℝ)|^4359 ≤ (576727228943/5000000000000 : ℝ)^3335
        have hw : |(-957903603/5000000000 : ℝ)|=(957903603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081881923/2000000000 : ℝ)|^4359 ≤ (44793446162459/100000000000000 : ℝ)^3335
        have hw : |(1081881923/2000000000 : ℝ)|=(1081881923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s5_6 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305487579/10000000000 : ℝ)*x 0 + (2704704789/5000000000 : ℝ)*x 1 + (-1915807223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305487579/10000000000 : ℝ)^4359 ≤ (43672009522317/100000000000000 : ℝ)^3335 := by
    have hnat : (5305487579 : ℕ)^4359*100000000000000^3335 ≤ 43672009522317^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305487579 10000000000 43672009522317 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704704789/5000000000 : ℝ)^4359 ≤ (44793445762001/100000000000000 : ℝ)^3335 := by
    have hnat : (2704704789 : ℕ)^4359*100000000000000^3335 ≤ 44793445762001^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704704789 5000000000 44793445762001 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1915807223/10000000000 : ℝ)^4359 ≤ (11534544712639/100000000000000 : ℝ)^3335 := by
    have hnat : (1915807223 : ℕ)^4359*100000000000000^3335 ≤ 11534544712639^3335*10000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915807223 10000000000 11534544712639 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305487579/10000000000 : ℝ), (2704704789/5000000000 : ℝ), (-1915807223/10000000000 : ℝ)] ![(43672009522317/100000000000000 : ℝ), (44793445762001/100000000000000 : ℝ), (11534544712639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305487579/10000000000 : ℝ)|^4359 ≤ (43672009522317/100000000000000 : ℝ)^3335
        have hw : |(5305487579/10000000000 : ℝ)|=(5305487579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704704789/5000000000 : ℝ)|^4359 ≤ (44793445762001/100000000000000 : ℝ)^3335
        have hw : |(2704704789/5000000000 : ℝ)|=(2704704789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1915807223/10000000000 : ℝ)|^4359 ≤ (11534544712639/100000000000000 : ℝ)^3335
        have hw : |(-1915807223/10000000000 : ℝ)|=(1915807223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1399_s5_7 (p : ℝ) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077985323/2500000000 : ℝ)*x 0 + (2244690111/5000000000 : ℝ)*x 1 + (828193321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077985323/2500000000 : ℝ)^4359 ≤ (4163038570403/12500000000000 : ℝ)^3335 := by
    have hnat : (1077985323 : ℕ)^4359*12500000000000^3335 ≤ 4163038570403^3335*2500000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077985323 2500000000 4163038570403 12500000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244690111/5000000000 : ℝ)^4359 ≤ (35106816164093/100000000000000 : ℝ)^3335 := by
    have hnat : (2244690111 : ℕ)^4359*100000000000000^3335 ≤ 35106816164093^3335*5000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244690111 5000000000 35106816164093 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828193321/2000000000 : ℝ)^4359 ≤ (31588875254037/100000000000000 : ℝ)^3335 := by
    have hnat : (828193321 : ℕ)^4359*100000000000000^3335 ≤ 31588875254037^3335*2000000000^4359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828193321 2000000000 31588875254037 100000000000000 4359 3335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4359/1024 : ℝ)) 4359 3335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077985323/2500000000 : ℝ), (2244690111/5000000000 : ℝ), (828193321/2000000000 : ℝ)] ![(4163038570403/12500000000000 : ℝ), (35106816164093/100000000000000 : ℝ), (31588875254037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077985323/2500000000 : ℝ)|^4359 ≤ (4163038570403/12500000000000 : ℝ)^3335
        have hw : |(1077985323/2500000000 : ℝ)|=(1077985323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244690111/5000000000 : ℝ)|^4359 ≤ (35106816164093/100000000000000 : ℝ)^3335
        have hw : |(2244690111/5000000000 : ℝ)|=(2244690111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828193321/2000000000 : ℝ)|^4359 ≤ (31588875254037/100000000000000 : ℝ)^3335
        have hw : |(828193321/2000000000 : ℝ)|=(828193321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1399_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1409/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7373/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11243/100000 : ℝ) ^ (2179/512 : ℝ) ≤ (1826914210534753/20000000000000000000 : ℝ) := by
    have hpowers : (11243/100000 : ℝ)^2179 ≤ (1826914210534753/20000000000000000000 : ℝ)^512 := by
      have hnat : (11243 : ℕ)^2179*20000000000000000000^512 ≤ 1826914210534753^512*100000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11243 100000 1826914210534753 20000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11243/100000 : ℝ)) (X := (1826914210534753/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14777/100000 : ℝ) ^ (2179/512 : ℝ) ≤ (5846634593038853/20000000000000000000 : ℝ) := by
    have hpowers : (14777/100000 : ℝ)^2179 ≤ (5846634593038853/20000000000000000000 : ℝ)^512 := by
      have hnat : (14777 : ℕ)^2179*20000000000000000000^512 ≤ 5846634593038853^512*100000^2179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14777 100000 5846634593038853 20000000000000000000 2179 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14777/100000 : ℝ)) (X := (5846634593038853/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001826914210534753/10000000000000000000 : ℝ) ≤ (19532088360053/19531250000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (10001826914210534753/10000000000000000000 : ℝ)^512 ≤ (19532088360053/19531250000000 : ℝ)^2179 := by
      have hnat : (10001826914210534753 : ℕ)^512*19531250000000^2179 ≤ 19532088360053^2179*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001826914210534753 10000000000000000000 19532088360053 19531250000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19532088360053/19531250000000 : ℝ)) (X := (10001826914210534753/10000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003836774401786803/10000000000000000000 : ℝ) ≤ (1250112674406531/1250000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (10003836774401786803/10000000000000000000 : ℝ)^512 ≤ (1250112674406531/1250000000000000 : ℝ)^2179 := by
      have hnat : (10003836774401786803 : ℕ)^512*1250000000000000^2179 ≤ 1250112674406531^2179*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003836774401786803 10000000000000000000 1250112674406531 1250000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250112674406531/1250000000000000 : ℝ)) (X := (10003836774401786803/10000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005846634593038853/10000000000000000000 : ℝ) ≤ (125017169376967/125000000000000 : ℝ) ^ (2179/512 : ℝ) := by
    have hpowers : (10005846634593038853/10000000000000000000 : ℝ)^512 ≤ (125017169376967/125000000000000 : ℝ)^2179 := by
      have hnat : (10005846634593038853 : ℕ)^512*125000000000000^2179 ≤ 125017169376967^2179*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005846634593038853 10000000000000000000 125017169376967 125000000000000 512 2179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125017169376967/125000000000000 : ℝ)) (X := (10005846634593038853/10000000000000000000 : ℝ)) (by norm_num) 2179 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1826914210534753/20000000000000000000 : ℝ) ≤ ((2208181253761901887/2208750000000000000 : ℝ)+2*(59019363139/44175000000000 : ℝ)*(11243/100000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (2208181253761901887/2208750000000000000 : ℝ)+2*(59019363139/44175000000000 : ℝ)*(11243/100000 : ℝ)=(19532088360053/19531250000000 : ℝ) by norm_num, show 1+2*(1826914210534753/20000000000000000000 : ℝ)=(10001826914210534753/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5846634593038853/20000000000000000000 : ℝ)+(1826914210534753/20000000000000000000 : ℝ) ≤ ((2208181253761901887/2208750000000000000 : ℝ)+(59019363139/44175000000000 : ℝ)*((14777/100000 : ℝ)+(11243/100000 : ℝ)))^(2179/512 : ℝ) := by
    rw [show (2208181253761901887/2208750000000000000 : ℝ)+(59019363139/44175000000000 : ℝ)*((14777/100000 : ℝ)+(11243/100000 : ℝ))=(1250112674406531/1250000000000000 : ℝ) by norm_num, show 1+(5846634593038853/20000000000000000000 : ℝ)+(1826914210534753/20000000000000000000 : ℝ)=(10003836774401786803/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5846634593038853/20000000000000000000 : ℝ) ≤ ((2208181253761901887/2208750000000000000 : ℝ)+2*(59019363139/44175000000000 : ℝ)*(14777/100000 : ℝ))^(2179/512 : ℝ) := by
    rw [show (2208181253761901887/2208750000000000000 : ℝ)+2*(59019363139/44175000000000 : ℝ)*(14777/100000 : ℝ)=(125017169376967/125000000000000 : ℝ) by norm_num, show 1+2*(5846634593038853/20000000000000000000 : ℝ)=(10005846634593038853/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2208181253761901887/2208750000000000000 : ℝ)*(X 1 0+X 2 0)+(59019363139/44175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (2208181253761901887/2208750000000000000 : ℝ)) (alpha := (59019363139/44175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2208181253761901887/2208750000000000000 : ℝ)*(X 0 1+X 2 1)+(59019363139/44175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (2208181253761901887/2208750000000000000 : ℝ)) (alpha := (59019363139/44175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2208181253761901887/2208750000000000000 : ℝ)*(X 0 2+X 1 2)+(59019363139/44175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2179/512 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14777/100000 : ℝ)) (c := (2208181253761901887/2208750000000000000 : ℝ)) (alpha := (59019363139/44175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-498926487/2500000000 : ℝ)*X 0 0+(5410004161/10000000000 : ℝ)*X 0 1+(1311493999/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337000621/2500000000 : ℝ)*X 1 0+(-2079240693/10000000000 : ℝ)*X 1 1+(5245975431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348001337/10000000000 : ℝ)*X 2 0+(5245976147/10000000000 : ℝ)*X 2 1+(-1039620637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311915449/10000000000 : ℝ)*X 0 0+(4139694273/10000000000 : ℝ)*X 0 1+(2245323397/5000000000 : ℝ)*X 0 2+(4311915449/10000000000 : ℝ)*X 1 0+(4139694273/10000000000 : ℝ)*X 1 1+(2245323397/5000000000 : ℝ)*X 1 2+(4311915449/10000000000 : ℝ)*X 2 0+(4139694273/10000000000 : ℝ)*X 2 1+(2245323397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-498929413/2500000000 : ℝ)*X 0 0+(5246567439/10000000000 : ℝ)*X 0 1+(2704704823/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652743777/5000000000 : ℝ)*X 1 0+(-957903603/5000000000 : ℝ)*X 1 1+(1081881923/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305487579/10000000000 : ℝ)*X 2 0+(2704704789/5000000000 : ℝ)*X 2 1+(-1915807223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1077985323/2500000000 : ℝ)*X 0 0+(2244690111/5000000000 : ℝ)*X 0 1+(828193321/2000000000 : ℝ)*X 0 2+(1077985323/2500000000 : ℝ)*X 1 0+(2244690111/5000000000 : ℝ)*X 1 1+(828193321/2000000000 : ℝ)*X 1 2+(1077985323/2500000000 : ℝ)*X 2 0+(2244690111/5000000000 : ℝ)*X 2 1+(828193321/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1399_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31166711398105007166773/2945000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2180803961/100000000000000 : ℝ)*(base19) + (31737697/3125000000000 : ℝ)*(base23) + (7491699/5000000000000 : ℝ)*(upper2) + (7950203/4000000000000 : ℝ)*(upper3) + (8736361735511/195312500000 : ℝ)*(major0) + (8736361735511/195312500000 : ℝ)*(major1) + (8736361735511/195312500000 : ℝ)*(major2) + (6096566185741981/100000000000000 : ℝ)*(sp0) + (6096594203540911/100000000000000 : ℝ)*(sp1) + (6096578032588937/100000000000000 : ℝ)*(sp2) + (2849414525849067/100000000000000 : ℝ)*(sp3) + (30198602891/100000000000000 : ℝ)*(sp4) + (17336149631/100000000000000 : ℝ)*(sp6) + (23154205179/100000000000000 : ℝ)*(sp7) + (1424718840027123/50000000000000 : ℝ)*(f.failure) + (762074548043109/12500000000000 : ℝ)*(f.sum) + (6957426676493/8835000000000000000000000000 : ℝ)*base66 + (83000627098858941/9203125000000000000000000000000 : ℝ)*base67 + (10229207408171441/9203125000000000000000000000000 : ℝ)*base69 + (5882216868078559/9203125000000000000000000000000 : ℝ)*base72 + (14255697014441/4417500000000000000000000000 : ℝ)*base73 + (32779185160218967/4601562500000000000000000000000 : ℝ)*base76 + (60914320075359809/9203125000000000000000000000000 : ℝ)*base78 + (21085930782531033/4601562500000000000000000000000 : ℝ)*base79 + (38859642075161/4417500000000000000000000000 : ℝ)*base81 + (12014953/1000000000000000000000 : ℝ)*base90 + (12014953/1000000000000000000000 : ℝ)*base92 + (12014953/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116609700674934145839969573/18406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (570527251/50000000000000 : ℝ)*(base19) + (317043823/25000000000000 : ℝ)*(base23) + (564179/500000000000 : ℝ)*(upper3) + (50289039/100000000000000 : ℝ)*(lower4) + (9253489/6250000000000 : ℝ)*(upper5) + (2252766439065921/50000000000000 : ℝ)*(major0) + (2252766439065921/50000000000000 : ℝ)*(major1) + (2252766439065921/50000000000000 : ℝ)*(major2) + (11990721193/50000000000000 : ℝ)*(sp1) + (6101518329/25000000000000 : ℝ)*(sp2) + (1228182893929193/20000000000000 : ℝ)*(sp4) + (6140889347149077/100000000000000 : ℝ)*(sp5) + (1535222198849339/25000000000000 : ℝ)*(sp6) + (179384442214999/6250000000000 : ℝ)*(sp7) + (179384442214999/6250000000000 : ℝ)*(f.failure) + (1228182893929193/20000000000000 : ℝ)*(f.sum) + (872171542131/736250000000000000000000000 : ℝ)*base65 + (80623609828976809/36812500000000000000000000000000 : ℝ)*base67 + (233753205622539309/36812500000000000000000000000000 : ℝ)*base69 + (27979388878789309/36812500000000000000000000000000 : ℝ)*base71 + (169449058441/46015625000000000000000000 : ℝ)*base73 + (119065721249898191/36812500000000000000000000000000 : ℝ)*base76 + (179702470820914309/36812500000000000000000000000000 : ℝ)*base77 + (55756968893835691/36812500000000000000000000000000 : ℝ)*base80 + (2924658222381/736250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1260789/125000000000000000000 : ℝ)*base90 + (1260789/125000000000000000000 : ℝ)*base92 + (1260789/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1399_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1399_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1399_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1399_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1399_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1399_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2179/512 : ℝ) ≤ p) (hpb : p ≤ (4359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31395789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7373/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1399_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:39:22.942658+00:00
-- url     : https://prove2.me/submissions/91bcb255-27b0-4601-90ac-fb8dfa979294

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
theorem support_rectangle_w1311_s3_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-258618673/1250000000 : ℝ)*x 0 + (5431332913/10000000000 : ℝ)*x 1 + (5227961791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258618673/1250000000 : ℝ)^4271 ≤ (12588072854709/100000000000000 : ℝ)^3247 := by
    have hnat : (258618673 : ℕ)^4271*100000000000000^3247 ≤ 12588072854709^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258618673 1250000000 12588072854709 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431332913/10000000000 : ℝ)^4271 ≤ (44802720318657/100000000000000 : ℝ)^3247 := by
    have hnat : (5431332913 : ℕ)^4271*100000000000000^3247 ≤ 44802720318657^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431332913 10000000000 44802720318657 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227961791/10000000000 : ℝ)^4271 ≤ (10652301702177/25000000000000 : ℝ)^3247 := by
    have hnat : (5227961791 : ℕ)^4271*25000000000000^3247 ≤ 10652301702177^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227961791 10000000000 10652301702177 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258618673/1250000000 : ℝ), (5431332913/10000000000 : ℝ), (5227961791/10000000000 : ℝ)] ![(12588072854709/100000000000000 : ℝ), (44802720318657/100000000000000 : ℝ), (10652301702177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258618673/1250000000 : ℝ)|^4271 ≤ (12588072854709/100000000000000 : ℝ)^3247
        have hw : |(-258618673/1250000000 : ℝ)|=(258618673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431332913/10000000000 : ℝ)|^4271 ≤ (44802720318657/100000000000000 : ℝ)^3247
        have hw : |(5431332913/10000000000 : ℝ)|=(5431332913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227961791/10000000000 : ℝ)|^4271 ≤ (10652301702177/25000000000000 : ℝ)^3247
        have hw : |(5227961791/10000000000 : ℝ)|=(5227961791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s3_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338457399/2500000000 : ℝ)*x 0 + (-1086486977/5000000000 : ℝ)*x 1 + (653495229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338457399/2500000000 : ℝ)^4271 ≤ (10990919426487/25000000000000 : ℝ)^3247 := by
    have hnat : (1338457399 : ℕ)^4271*25000000000000^3247 ≤ 10990919426487^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338457399 2500000000 10990919426487 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086486977/5000000000 : ℝ)^4271 ≤ (2685423006539/20000000000000 : ℝ)^3247 := by
    have hnat : (1086486977 : ℕ)^4271*20000000000000^3247 ≤ 2685423006539^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086486977 5000000000 2685423006539 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653495229/1250000000 : ℝ)^4271 ≤ (10652301812063/25000000000000 : ℝ)^3247 := by
    have hnat : (653495229 : ℕ)^4271*25000000000000^3247 ≤ 10652301812063^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653495229 1250000000 10652301812063 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338457399/2500000000 : ℝ), (-1086486977/5000000000 : ℝ), (653495229/1250000000 : ℝ)] ![(10990919426487/25000000000000 : ℝ), (2685423006539/20000000000000 : ℝ), (10652301812063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338457399/2500000000 : ℝ)|^4271 ≤ (10990919426487/25000000000000 : ℝ)^3247
        have hw : |(1338457399/2500000000 : ℝ)|=(1338457399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1086486977/5000000000 : ℝ)|^4271 ≤ (2685423006539/20000000000000 : ℝ)^3247
        have hw : |(-1086486977/5000000000 : ℝ)|=(1086486977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653495229/1250000000 : ℝ)|^4271 ≤ (10652301812063/25000000000000 : ℝ)^3247
        have hw : |(653495229/1250000000 : ℝ)|=(653495229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s3_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353829641/10000000000 : ℝ)*x 0 + (130699041/250000000 : ℝ)*x 1 + (-1086487073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353829641/10000000000 : ℝ)^4271 ≤ (5495459774001/12500000000000 : ℝ)^3247 := by
    have hnat : (5353829641 : ℕ)^4271*12500000000000^3247 ≤ 5495459774001^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353829641 10000000000 5495459774001 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130699041/250000000 : ℝ)^4271 ≤ (42609205189901/100000000000000 : ℝ)^3247 := by
    have hnat : (130699041 : ℕ)^4271*100000000000000^3247 ≤ 42609205189901^3247*250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130699041 250000000 42609205189901 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086487073/5000000000 : ℝ)^4271 ≤ (6713558296621/50000000000000 : ℝ)^3247 := by
    have hnat : (1086487073 : ℕ)^4271*50000000000000^3247 ≤ 6713558296621^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086487073 5000000000 6713558296621 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353829641/10000000000 : ℝ), (130699041/250000000 : ℝ), (-1086487073/5000000000 : ℝ)] ![(5495459774001/12500000000000 : ℝ), (42609205189901/100000000000000 : ℝ), (6713558296621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353829641/10000000000 : ℝ)|^4271 ≤ (5495459774001/12500000000000 : ℝ)^3247
        have hw : |(5353829641/10000000000 : ℝ)|=(5353829641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130699041/250000000 : ℝ)|^4271 ≤ (42609205189901/100000000000000 : ℝ)^3247
        have hw : |(130699041/250000000 : ℝ)|=(130699041/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086487073/5000000000 : ℝ)|^4271 ≤ (6713558296621/50000000000000 : ℝ)^3247
        have hw : |(-1086487073/5000000000 : ℝ)|=(1086487073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s3_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34668153/80000000 : ℝ)*x 0 + (165114191/400000000 : ℝ)*x 1 + (4548867489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34668153/80000000 : ℝ)^4271 ≤ (416123173929/1250000000000 : ℝ)^3247 := by
    have hnat : (34668153 : ℕ)^4271*1250000000000^3247 ≤ 416123173929^3247*80000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34668153 80000000 416123173929 1250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165114191/400000000 : ℝ)^4271 ≤ (1951714058061/6250000000000 : ℝ)^3247 := by
    have hnat : (165114191 : ℕ)^4271*6250000000000^3247 ≤ 1951714058061^3247*400000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165114191 400000000 1951714058061 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4548867489/10000000000 : ℝ)^4271 ≤ (17741360575533/50000000000000 : ℝ)^3247 := by
    have hnat : (4548867489 : ℕ)^4271*50000000000000^3247 ≤ 17741360575533^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548867489 10000000000 17741360575533 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34668153/80000000 : ℝ), (165114191/400000000 : ℝ), (4548867489/10000000000 : ℝ)] ![(416123173929/1250000000000 : ℝ), (1951714058061/6250000000000 : ℝ), (17741360575533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34668153/80000000 : ℝ)|^4271 ≤ (416123173929/1250000000000 : ℝ)^3247
        have hw : |(34668153/80000000 : ℝ)|=(34668153/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165114191/400000000 : ℝ)|^4271 ≤ (1951714058061/6250000000000 : ℝ)^3247
        have hw : |(165114191/400000000 : ℝ)|=(165114191/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4548867489/10000000000 : ℝ)|^4271 ≤ (17741360575533/50000000000000 : ℝ)^3247
        have hw : |(4548867489/10000000000 : ℝ)|=(4548867489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s3_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2068970613/10000000000 : ℝ)*x 0 + (209153041/400000000 : ℝ)*x 1 + (1357615829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068970613/10000000000 : ℝ)^4271 ≤ (786765172011/6250000000000 : ℝ)^3247 := by
    have hnat : (2068970613 : ℕ)^4271*6250000000000^3247 ≤ 786765172011^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068970613 10000000000 786765172011 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209153041/400000000 : ℝ)^4271 ≤ (42618472140919/100000000000000 : ℝ)^3247 := by
    have hnat : (209153041 : ℕ)^4271*100000000000000^3247 ≤ 42618472140919^3247*400000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209153041 400000000 42618472140919 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357615829/2500000000 : ℝ)^4271 ≤ (44793285092569/100000000000000 : ℝ)^3247 := by
    have hnat : (1357615829 : ℕ)^4271*100000000000000^3247 ≤ 44793285092569^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357615829 2500000000 44793285092569 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2068970613/10000000000 : ℝ), (209153041/400000000 : ℝ), (1357615829/2500000000 : ℝ)] ![(786765172011/6250000000000 : ℝ), (42618472140919/100000000000000 : ℝ), (44793285092569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2068970613/10000000000 : ℝ)|^4271 ≤ (786765172011/6250000000000 : ℝ)^3247
        have hw : |(-2068970613/10000000000 : ℝ)|=(2068970613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209153041/400000000 : ℝ)|^4271 ≤ (42618472140919/100000000000000 : ℝ)^3247
        have hw : |(209153041/400000000 : ℝ)|=(209153041/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357615829/2500000000 : ℝ)|^4271 ≤ (44793285092569/100000000000000 : ℝ)^3247
        have hw : |(1357615829/2500000000 : ℝ)|=(1357615829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s3_5 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301635357/10000000000 : ℝ)*x 0 + (-1970472439/10000000000 : ℝ)*x 1 + (67880791/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301635357/10000000000 : ℝ)^4271 ≤ (43400779719051/100000000000000 : ℝ)^3247 := by
    have hnat : (5301635357 : ℕ)^4271*100000000000000^3247 ≤ 43400779719051^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301635357 10000000000 43400779719051 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1970472439/10000000000 : ℝ)^4271 ≤ (2951483893897/25000000000000 : ℝ)^3247 := by
    have hnat : (1970472439 : ℕ)^4271*25000000000000^3247 ≤ 2951483893897^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970472439 10000000000 2951483893897 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67880791/125000000 : ℝ)^4271 ≤ (22396642350987/50000000000000 : ℝ)^3247 := by
    have hnat : (67880791 : ℕ)^4271*50000000000000^3247 ≤ 22396642350987^3247*125000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67880791 125000000 22396642350987 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301635357/10000000000 : ℝ), (-1970472439/10000000000 : ℝ), (67880791/125000000 : ℝ)] ![(43400779719051/100000000000000 : ℝ), (2951483893897/25000000000000 : ℝ), (22396642350987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301635357/10000000000 : ℝ)|^4271 ≤ (43400779719051/100000000000000 : ℝ)^3247
        have hw : |(5301635357/10000000000 : ℝ)|=(5301635357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1970472439/10000000000 : ℝ)|^4271 ≤ (2951483893897/25000000000000 : ℝ)^3247
        have hw : |(-1970472439/10000000000 : ℝ)|=(1970472439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67880791/125000000 : ℝ)|^4271 ≤ (22396642350987/50000000000000 : ℝ)^3247
        have hw : |(67880791/125000000 : ℝ)|=(67880791/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s3_6 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301635489/10000000000 : ℝ)*x 0 + (1086092631/2000000000 : ℝ)*x 1 + (-197047243/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301635489/10000000000 : ℝ)^4271 ≤ (43400781140427/100000000000000 : ℝ)^3247 := by
    have hnat : (5301635489 : ℕ)^4271*100000000000000^3247 ≤ 43400781140427^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301635489 10000000000 43400781140427 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086092631/2000000000 : ℝ)^4271 ≤ (8958656669149/20000000000000 : ℝ)^3247 := by
    have hnat : (1086092631 : ℕ)^4271*20000000000000^3247 ≤ 8958656669149^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086092631 2000000000 8958656669149 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197047243/1000000000 : ℝ)^4271 ≤ (11805935504659/100000000000000 : ℝ)^3247 := by
    have hnat : (197047243 : ℕ)^4271*100000000000000^3247 ≤ 11805935504659^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197047243 1000000000 11805935504659 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301635489/10000000000 : ℝ), (1086092631/2000000000 : ℝ), (-197047243/1000000000 : ℝ)] ![(43400781140427/100000000000000 : ℝ), (8958656669149/20000000000000 : ℝ), (11805935504659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301635489/10000000000 : ℝ)|^4271 ≤ (43400781140427/100000000000000 : ℝ)^3247
        have hw : |(5301635489/10000000000 : ℝ)|=(5301635489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086092631/2000000000 : ℝ)|^4271 ≤ (8958656669149/20000000000000 : ℝ)^3247
        have hw : |(1086092631/2000000000 : ℝ)|=(1086092631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197047243/1000000000 : ℝ)|^4271 ≤ (11805935504659/100000000000000 : ℝ)^3247
        have hw : |(-197047243/1000000000 : ℝ)|=(197047243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s3_7 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67711919/156250000 : ℝ)*x 0 + (1136769551/2500000000 : ℝ)*x 1 + (2064827553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67711919/156250000 : ℝ)^4271 ≤ (33290295394417/100000000000000 : ℝ)^3247 := by
    have hnat : (67711919 : ℕ)^4271*100000000000000^3247 ≤ 33290295394417^3247*156250000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67711919 156250000 33290295394417 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136769551/2500000000 : ℝ)^4271 ≤ (2216522728299/6250000000000 : ℝ)^3247 := by
    have hnat : (1136769551 : ℕ)^4271*6250000000000^3247 ≤ 2216522728299^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136769551 2500000000 2216522728299 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064827553/5000000000 : ℝ)^4271 ≤ (31245340937871/100000000000000 : ℝ)^3247 := by
    have hnat : (2064827553 : ℕ)^4271*100000000000000^3247 ≤ 31245340937871^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064827553 5000000000 31245340937871 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67711919/156250000 : ℝ), (1136769551/2500000000 : ℝ), (2064827553/5000000000 : ℝ)] ![(33290295394417/100000000000000 : ℝ), (2216522728299/6250000000000 : ℝ), (31245340937871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67711919/156250000 : ℝ)|^4271 ≤ (33290295394417/100000000000000 : ℝ)^3247
        have hw : |(67711919/156250000 : ℝ)|=(67711919/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136769551/2500000000 : ℝ)|^4271 ≤ (2216522728299/6250000000000 : ℝ)^3247
        have hw : |(1136769551/2500000000 : ℝ)|=(1136769551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064827553/5000000000 : ℝ)|^4271 ≤ (31245340937871/100000000000000 : ℝ)^3247
        have hw : |(2064827553/5000000000 : ℝ)|=(2064827553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9641/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (537/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15043/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16233/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9641/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16233/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9641/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16233/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9641/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16233/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9641/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16233/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9641/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16233/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9641/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9641/100000 : ℝ) ^ (2135/512 : ℝ) ≤ (181433915313533/3125000000000000000 : ℝ) := by
    have hpowers : (9641/100000 : ℝ)^2135 ≤ (181433915313533/3125000000000000000 : ℝ)^512 := by
      have hnat : (9641 : ℕ)^2135*3125000000000000000^512 ≤ 181433915313533^512*100000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9641 100000 181433915313533 3125000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9641/100000 : ℝ)) (X := (181433915313533/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16233/100000 : ℝ) ^ (2135/512 : ℝ) ≤ (25491455927104249/50000000000000000000 : ℝ) := by
    have hpowers : (16233/100000 : ℝ)^2135 ≤ (25491455927104249/50000000000000000000 : ℝ)^512 := by
      have hnat : (16233 : ℕ)^2135*50000000000000000000^512 ≤ 25491455927104249^512*100000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16233 100000 25491455927104249 50000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16233/100000 : ℝ)) (X := (25491455927104249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562681433915313533/1562500000000000000 : ℝ) ≤ (2500069613163451/2500000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (1562681433915313533/1562500000000000000 : ℝ)^512 ≤ (2500069613163451/2500000000000000 : ℝ)^2135 := by
      have hnat : (1562681433915313533 : ℕ)^512*2500000000000000^2135 ≤ 2500069613163451^2135*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562681433915313533 1562500000000000000 2500069613163451 2500000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500069613163451/2500000000000000 : ℝ)) (X := (1562681433915313533/1562500000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028394398572120777/50000000000000000000 : ℝ) ≤ (5000680786655379/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50028394398572120777/50000000000000000000 : ℝ)^512 ≤ (5000680786655379/5000000000000000 : ℝ)^2135 := by
      have hnat : (50028394398572120777 : ℕ)^512*5000000000000000^2135 ≤ 5000680786655379^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028394398572120777 50000000000000000000 5000680786655379 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000680786655379/5000000000000000 : ℝ)) (X := (50028394398572120777/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25025491455927104249/25000000000000000000 : ℝ) ≤ (312576396686491/312500000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (25025491455927104249/25000000000000000000 : ℝ)^512 ≤ (312576396686491/312500000000000 : ℝ)^2135 := by
      have hnat : (25025491455927104249 : ℕ)^512*312500000000000^2135 ≤ 312576396686491^2135*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25025491455927104249 25000000000000000000 312576396686491 312500000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312576396686491/312500000000000 : ℝ)) (X := (25025491455927104249/25000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(181433915313533/3125000000000000000 : ℝ) ≤ ((3295047541369324447/3296000000000000000 : ℝ)+2*(541560328477/329600000000000 : ℝ)*(9641/100000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (3295047541369324447/3296000000000000000 : ℝ)+2*(541560328477/329600000000000 : ℝ)*(9641/100000 : ℝ)=(2500069613163451/2500000000000000 : ℝ) by norm_num, show 1+2*(181433915313533/3125000000000000000 : ℝ)=(1562681433915313533/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25491455927104249/50000000000000000000 : ℝ)+(181433915313533/3125000000000000000 : ℝ) ≤ ((3295047541369324447/3296000000000000000 : ℝ)+(541560328477/329600000000000 : ℝ)*((16233/100000 : ℝ)+(9641/100000 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (3295047541369324447/3296000000000000000 : ℝ)+(541560328477/329600000000000 : ℝ)*((16233/100000 : ℝ)+(9641/100000 : ℝ))=(5000680786655379/5000000000000000 : ℝ) by norm_num, show 1+(25491455927104249/50000000000000000000 : ℝ)+(181433915313533/3125000000000000000 : ℝ)=(50028394398572120777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25491455927104249/50000000000000000000 : ℝ) ≤ ((3295047541369324447/3296000000000000000 : ℝ)+2*(541560328477/329600000000000 : ℝ)*(16233/100000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (3295047541369324447/3296000000000000000 : ℝ)+2*(541560328477/329600000000000 : ℝ)*(16233/100000 : ℝ)=(312576396686491/312500000000000 : ℝ) by norm_num, show 1+2*(25491455927104249/50000000000000000000 : ℝ)=(25025491455927104249/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3295047541369324447/3296000000000000000 : ℝ)*(X 1 0+X 2 0)+(541560328477/329600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (9641/100000 : ℝ)) (hi := (16233/100000 : ℝ)) (c := (3295047541369324447/3296000000000000000 : ℝ)) (alpha := (541560328477/329600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3295047541369324447/3296000000000000000 : ℝ)*(X 0 1+X 2 1)+(541560328477/329600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (9641/100000 : ℝ)) (hi := (16233/100000 : ℝ)) (c := (3295047541369324447/3296000000000000000 : ℝ)) (alpha := (541560328477/329600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3295047541369324447/3296000000000000000 : ℝ)*(X 0 2+X 1 2)+(541560328477/329600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (9641/100000 : ℝ)) (hi := (16233/100000 : ℝ)) (c := (3295047541369324447/3296000000000000000 : ℝ)) (alpha := (541560328477/329600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-258618673/1250000000 : ℝ)*X 0 0+(5431332913/10000000000 : ℝ)*X 0 1+(5227961791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338457399/2500000000 : ℝ)*X 1 0+(-1086486977/5000000000 : ℝ)*X 1 1+(653495229/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353829641/10000000000 : ℝ)*X 2 0+(130699041/250000000 : ℝ)*X 2 1+(-1086487073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34668153/80000000 : ℝ)*X 0 0+(165114191/400000000 : ℝ)*X 0 1+(4548867489/10000000000 : ℝ)*X 0 2+(34668153/80000000 : ℝ)*X 1 0+(165114191/400000000 : ℝ)*X 1 1+(4548867489/10000000000 : ℝ)*X 1 2+(34668153/80000000 : ℝ)*X 2 0+(165114191/400000000 : ℝ)*X 2 1+(4548867489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2068970613/10000000000 : ℝ)*X 0 0+(209153041/400000000 : ℝ)*X 0 1+(1357615829/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301635357/10000000000 : ℝ)*X 1 0+(-1970472439/10000000000 : ℝ)*X 1 1+(67880791/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301635489/10000000000 : ℝ)*X 2 0+(1086092631/2000000000 : ℝ)*X 2 1+(-197047243/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((67711919/156250000 : ℝ)*X 0 0+(1136769551/2500000000 : ℝ)*X 0 1+(2064827553/5000000000 : ℝ)*X 0 2+(67711919/156250000 : ℝ)*X 1 0+(1136769551/2500000000 : ℝ)*X 1 1+(2064827553/5000000000 : ℝ)*X 1 2+(67711919/156250000 : ℝ)*X 2 0+(1136769551/2500000000 : ℝ)*X 2 1+(2064827553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25308077889264351443904189/5150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1042768577/100000000000000 : ℝ)*(base19) + (508542947/50000000000000 : ℝ)*(base23) + (3540059/6250000000000 : ℝ)*(lower2) + (242573273/100000000000000 : ℝ)*(upper3) + (20763691/100000000000000 : ℝ)*(lower4) + (227887371170329/6250000000000 : ℝ)*(major0) + (227887371170329/6250000000000 : ℝ)*(major1) + (227887371170329/6250000000000 : ℝ)*(major2) + (61464238967631/1250000000000 : ℝ)*(sp0) + (4917151664672723/100000000000000 : ℝ)*(sp1) + (2458575845177703/50000000000000 : ℝ)*(sp2) + (237523235508007/10000000000000 : ℝ)*(sp3) + (13590030819/100000000000000 : ℝ)*(sp4) + (10651122817/100000000000000 : ℝ)*(sp7) + (296905375775361/12500000000000 : ℝ)*(f.failure) + (4917152707441299/100000000000000 : ℝ)*(f.sum) + (3224753752283/1030000000000000000000000000 : ℝ)*base65 + (117356941149736937/20600000000000000000000000000000 : ℝ)*base68 + (29964047780463063/20600000000000000000000000000000 : ℝ)*base69 + (6003923307936937/20600000000000000000000000000000 : ℝ)*base72 + (2559257237653/1030000000000000000000000000 : ℝ)*base73 + (390762175090736937/20600000000000000000000000000000 : ℝ)*base76 + (96975157670736937/20600000000000000000000000000000 : ℝ)*base78 + (575505743524736937/20600000000000000000000000000000 : ℝ)*base80 + (10046011666253/1030000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14713537/1250000000000000000000 : ℝ)*base89 + (14713537/1250000000000000000000 : ℝ)*base91 + (14713537/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (166507741075383484716283311/16480000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2196747611/100000000000000 : ℝ)*(base19) + (2440756461/100000000000000 : ℝ)*(base23) + (47577811/20000000000000 : ℝ)*(upper3) + (26038511/50000000000000 : ℝ)*(lower4) + (122098239/50000000000000 : ℝ)*(upper5) + (735505142347171/20000000000000 : ℝ)*(major0) + (735505142347171/20000000000000 : ℝ)*(major1) + (735505142347171/20000000000000 : ℝ)*(major2) + (36941414387/100000000000000 : ℝ)*(sp1) + (9801693047/25000000000000 : ℝ)*(sp2) + (49594002268777/1000000000000 : ℝ)*(sp4) + (4959361088715701/100000000000000 : ℝ)*(sp5) + (4959358579349051/100000000000000 : ℝ)*(sp6) + (479130171961301/20000000000000 : ℝ)*(sp7) + (479130171961301/20000000000000 : ℝ)*(f.failure) + (49594002268777/1000000000000 : ℝ)*(f.sum) + (6882412906487/3296000000000000000000000000 : ℝ)*base65 + (126754990461140563/65920000000000000000000000000000 : ℝ)*base68 + (72787604335659437/65920000000000000000000000000000 : ℝ)*base69 + (32673733697620563/65920000000000000000000000000000 : ℝ)*base72 + (6189813481001/3296000000000000000000000000 : ℝ)*base74 + (250430223243220563/65920000000000000000000000000000 : ℝ)*base76 + (163555094602580563/65920000000000000000000000000000 : ℝ)*base78 + (137990508973140563/65920000000000000000000000000000 : ℝ)*base80 + (197924860657/131840000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1770517/2000000000000000000000 : ℝ)*base89 + (1770517/2000000000000000000000 : ℝ)*base91 + (1770517/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1311_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9641/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (537/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1311_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1311_s4_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2070680133/10000000000 : ℝ)*x 0 + (677187167/1250000000 : ℝ)*x 1 + (5240662201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070680133/10000000000 : ℝ)^4271 ≤ (6300962994213/50000000000000 : ℝ)^3247 := by
    have hnat : (2070680133 : ℕ)^4271*50000000000000^3247 ≤ 6300962994213^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070680133 10000000000 6300962994213 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677187167/1250000000 : ℝ)^4271 ≤ (8930531856859/20000000000000 : ℝ)^3247 := by
    have hnat : (677187167 : ℕ)^4271*20000000000000^3247 ≤ 8930531856859^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677187167 1250000000 8930531856859 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240662201/10000000000 : ℝ)^4271 ≤ (42745414712143/100000000000000 : ℝ)^3247 := by
    have hnat : (5240662201 : ℕ)^4271*100000000000000^3247 ≤ 42745414712143^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240662201 10000000000 42745414712143 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2070680133/10000000000 : ℝ), (677187167/1250000000 : ℝ), (5240662201/10000000000 : ℝ)] ![(6300962994213/50000000000000 : ℝ), (8930531856859/20000000000000 : ℝ), (42745414712143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2070680133/10000000000 : ℝ)|^4271 ≤ (6300962994213/50000000000000 : ℝ)^3247
        have hw : |(-2070680133/10000000000 : ℝ)|=(2070680133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677187167/1250000000 : ℝ)|^4271 ≤ (8930531856859/20000000000000 : ℝ)^3247
        have hw : |(677187167/1250000000 : ℝ)|=(677187167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240662201/10000000000 : ℝ)|^4271 ≤ (42745414712143/100000000000000 : ℝ)^3247
        have hw : |(5240662201/10000000000 : ℝ)|=(5240662201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s4_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350321623/10000000000 : ℝ)*x 0 + (-216086661/1000000000 : ℝ)*x 1 + (2620331073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350321623/10000000000 : ℝ)^4271 ≤ (43925790889293/100000000000000 : ℝ)^3247 := by
    have hnat : (5350321623 : ℕ)^4271*100000000000000^3247 ≤ 43925790889293^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350321623 10000000000 43925790889293 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216086661/1000000000 : ℝ)^4271 ≤ (6664397486211/50000000000000 : ℝ)^3247 := by
    have hnat : (216086661 : ℕ)^4271*50000000000000^3247 ≤ 6664397486211^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216086661 1000000000 6664397486211 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620331073/5000000000 : ℝ)^4271 ≤ (2137270706103/5000000000000 : ℝ)^3247 := by
    have hnat : (2620331073 : ℕ)^4271*5000000000000^3247 ≤ 2137270706103^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620331073 5000000000 2137270706103 5000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350321623/10000000000 : ℝ), (-216086661/1000000000 : ℝ), (2620331073/5000000000 : ℝ)] ![(43925790889293/100000000000000 : ℝ), (6664397486211/50000000000000 : ℝ), (2137270706103/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350321623/10000000000 : ℝ)|^4271 ≤ (43925790889293/100000000000000 : ℝ)^3247
        have hw : |(5350321623/10000000000 : ℝ)|=(5350321623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216086661/1000000000 : ℝ)|^4271 ≤ (6664397486211/50000000000000 : ℝ)^3247
        have hw : |(-216086661/1000000000 : ℝ)|=(216086661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620331073/5000000000 : ℝ)|^4271 ≤ (2137270706103/5000000000000 : ℝ)^3247
        have hw : |(2620331073/5000000000 : ℝ)|=(2620331073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s4_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337580421/2500000000 : ℝ)*x 0 + (131016551/250000000 : ℝ)*x 1 + (-2160866669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337580421/2500000000 : ℝ)^4271 ≤ (43925791548037/100000000000000 : ℝ)^3247 := by
    have hnat : (1337580421 : ℕ)^4271*100000000000000^3247 ≤ 43925791548037^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337580421 2500000000 43925791548037 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131016551/250000000 : ℝ)^4271 ≤ (5343176623101/12500000000000 : ℝ)^3247 := by
    have hnat : (131016551 : ℕ)^4271*12500000000000^3247 ≤ 5343176623101^3247*250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131016551 250000000 5343176623101 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160866669/10000000000 : ℝ)^4271 ≤ (13328795451121/100000000000000 : ℝ)^3247 := by
    have hnat : (2160866669 : ℕ)^4271*100000000000000^3247 ≤ 13328795451121^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160866669 10000000000 13328795451121 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337580421/2500000000 : ℝ), (131016551/250000000 : ℝ), (-2160866669/10000000000 : ℝ)] ![(43925791548037/100000000000000 : ℝ), (5343176623101/12500000000000 : ℝ), (13328795451121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337580421/2500000000 : ℝ)|^4271 ≤ (43925791548037/100000000000000 : ℝ)^3247
        have hw : |(1337580421/2500000000 : ℝ)|=(1337580421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131016551/250000000 : ℝ)|^4271 ≤ (5343176623101/12500000000000 : ℝ)^3247
        have hw : |(131016551/250000000 : ℝ)|=(131016551/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2160866669/10000000000 : ℝ)|^4271 ≤ (13328795451121/100000000000000 : ℝ)^3247
        have hw : |(-2160866669/10000000000 : ℝ)|=(2160866669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s4_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2167283859/5000000000 : ℝ)*x 0 + (129849707/312500000 : ℝ)*x 1 + (4521269411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167283859/5000000000 : ℝ)^4271 ≤ (4162556239377/12500000000000 : ℝ)^3247 := by
    have hnat : (2167283859 : ℕ)^4271*12500000000000^3247 ≤ 4162556239377^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167283859 5000000000 4162556239377 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129849707/312500000 : ℝ)^4271 ≤ (3937465346139/12500000000000 : ℝ)^3247 := by
    have hnat : (129849707 : ℕ)^4271*12500000000000^3247 ≤ 3937465346139^3247*312500000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129849707 312500000 3937465346139 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4521269411/10000000000 : ℝ)^4271 ≤ (17599913652753/50000000000000 : ℝ)^3247 := by
    have hnat : (4521269411 : ℕ)^4271*50000000000000^3247 ≤ 17599913652753^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521269411 10000000000 17599913652753 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2167283859/5000000000 : ℝ), (129849707/312500000 : ℝ), (4521269411/10000000000 : ℝ)] ![(4162556239377/12500000000000 : ℝ), (3937465346139/12500000000000 : ℝ), (17599913652753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2167283859/5000000000 : ℝ)|^4271 ≤ (4162556239377/12500000000000 : ℝ)^3247
        have hw : |(2167283859/5000000000 : ℝ)|=(2167283859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129849707/312500000 : ℝ)|^4271 ≤ (3937465346139/12500000000000 : ℝ)^3247
        have hw : |(129849707/312500000 : ℝ)|=(129849707/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4521269411/10000000000 : ℝ)|^4271 ≤ (17599913652753/50000000000000 : ℝ)^3247
        have hw : |(4521269411/10000000000 : ℝ)|=(4521269411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s4_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035346909/5000000000 : ℝ)*x 0 + (2620658231/5000000000 : ℝ)*x 1 + (5416839757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035346909/5000000000 : ℝ)^4271 ≤ (12602035539451/100000000000000 : ℝ)^3247 := by
    have hnat : (1035346909 : ℕ)^4271*100000000000000^3247 ≤ 12602035539451^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035346909 5000000000 12602035539451 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620658231/5000000000 : ℝ)^4271 ≤ (1710097371107/4000000000000 : ℝ)^3247 := by
    have hnat : (2620658231 : ℕ)^4271*4000000000000^3247 ≤ 1710097371107^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620658231 5000000000 1710097371107 4000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416839757/10000000000 : ℝ)^4271 ≤ (44645530170819/100000000000000 : ℝ)^3247 := by
    have hnat : (5416839757 : ℕ)^4271*100000000000000^3247 ≤ 44645530170819^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416839757 10000000000 44645530170819 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035346909/5000000000 : ℝ), (2620658231/5000000000 : ℝ), (5416839757/10000000000 : ℝ)] ![(12602035539451/100000000000000 : ℝ), (1710097371107/4000000000000 : ℝ), (44645530170819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035346909/5000000000 : ℝ)|^4271 ≤ (12602035539451/100000000000000 : ℝ)^3247
        have hw : |(-1035346909/5000000000 : ℝ)|=(1035346909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620658231/5000000000 : ℝ)|^4271 ≤ (1710097371107/4000000000000 : ℝ)^3247
        have hw : |(2620658231/5000000000 : ℝ)|=(2620658231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416839757/10000000000 : ℝ)|^4271 ≤ (44645530170819/100000000000000 : ℝ)^3247
        have hw : |(5416839757/10000000000 : ℝ)|=(5416839757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s4_5 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326235067/2500000000 : ℝ)*x 0 + (-198468889/1000000000 : ℝ)*x 1 + (5416839543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326235067/2500000000 : ℝ)^4271 ≤ (2714773155703/6250000000000 : ℝ)^3247 := by
    have hnat : (1326235067 : ℕ)^4271*6250000000000^3247 ≤ 2714773155703^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326235067 2500000000 2714773155703 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198468889/1000000000 : ℝ)^4271 ≤ (11918101645553/100000000000000 : ℝ)^3247 := by
    have hnat : (198468889 : ℕ)^4271*100000000000000^3247 ≤ 11918101645553^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198468889 1000000000 11918101645553 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416839543/10000000000 : ℝ)^4271 ≤ (5580690981349/12500000000000 : ℝ)^3247 := by
    have hnat : (5416839543 : ℕ)^4271*12500000000000^3247 ≤ 5580690981349^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416839543 10000000000 5580690981349 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326235067/2500000000 : ℝ), (-198468889/1000000000 : ℝ), (5416839543/10000000000 : ℝ)] ![(2714773155703/6250000000000 : ℝ), (11918101645553/100000000000000 : ℝ), (5580690981349/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326235067/2500000000 : ℝ)|^4271 ≤ (2714773155703/6250000000000 : ℝ)^3247
        have hw : |(1326235067/2500000000 : ℝ)|=(1326235067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198468889/1000000000 : ℝ)|^4271 ≤ (11918101645553/100000000000000 : ℝ)^3247
        have hw : |(-198468889/1000000000 : ℝ)|=(198468889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416839543/10000000000 : ℝ)|^4271 ≤ (5580690981349/12500000000000 : ℝ)^3247
        have hw : |(5416839543/10000000000 : ℝ)|=(5416839543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s4_6 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304939797/10000000000 : ℝ)*x 0 + (2708420047/5000000000 : ℝ)*x 1 + (-1984688777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304939797/10000000000 : ℝ)^4271 ≤ (10859091354631/25000000000000 : ℝ)^3247 := by
    have hnat : (5304939797 : ℕ)^4271*25000000000000^3247 ≤ 10859091354631^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304939797 10000000000 10859091354631 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708420047/5000000000 : ℝ)^4271 ≤ (139517293201/312500000000 : ℝ)^3247 := by
    have hnat : (2708420047 : ℕ)^4271*312500000000^3247 ≤ 139517293201^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708420047 5000000000 139517293201 312500000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984688777/10000000000 : ℝ)^4271 ≤ (11918100752987/100000000000000 : ℝ)^3247 := by
    have hnat : (1984688777 : ℕ)^4271*100000000000000^3247 ≤ 11918100752987^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984688777 10000000000 11918100752987 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304939797/10000000000 : ℝ), (2708420047/5000000000 : ℝ), (-1984688777/10000000000 : ℝ)] ![(10859091354631/25000000000000 : ℝ), (139517293201/312500000000 : ℝ), (11918100752987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304939797/10000000000 : ℝ)|^4271 ≤ (10859091354631/25000000000000 : ℝ)^3247
        have hw : |(5304939797/10000000000 : ℝ)|=(5304939797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708420047/5000000000 : ℝ)|^4271 ≤ (139517293201/312500000000 : ℝ)^3247
        have hw : |(2708420047/5000000000 : ℝ)|=(2708420047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984688777/10000000000 : ℝ)|^4271 ≤ (11918100752987/100000000000000 : ℝ)^3247
        have hw : |(-1984688777/10000000000 : ℝ)|=(1984688777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s4_7 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4334596561/10000000000 : ℝ)*x 0 + (4519915361/10000000000 : ℝ)*x 1 + (4156551847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334596561/10000000000 : ℝ)^4271 ≤ (33300741384087/100000000000000 : ℝ)^3247 := by
    have hnat : (4334596561 : ℕ)^4271*100000000000000^3247 ≤ 33300741384087^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334596561 10000000000 33300741384087 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519915361/10000000000 : ℝ)^4271 ≤ (35185961611243/100000000000000 : ℝ)^3247 := by
    have hnat : (4519915361 : ℕ)^4271*100000000000000^3247 ≤ 35185961611243^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519915361 10000000000 35185961611243 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156551847/10000000000 : ℝ)^4271 ≤ (787832424641/2500000000000 : ℝ)^3247 := by
    have hnat : (4156551847 : ℕ)^4271*2500000000000^3247 ≤ 787832424641^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156551847 10000000000 787832424641 2500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334596561/10000000000 : ℝ), (4519915361/10000000000 : ℝ), (4156551847/10000000000 : ℝ)] ![(33300741384087/100000000000000 : ℝ), (35185961611243/100000000000000 : ℝ), (787832424641/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334596561/10000000000 : ℝ)|^4271 ≤ (33300741384087/100000000000000 : ℝ)^3247
        have hw : |(4334596561/10000000000 : ℝ)|=(4334596561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519915361/10000000000 : ℝ)|^4271 ≤ (35185961611243/100000000000000 : ℝ)^3247
        have hw : |(4519915361/10000000000 : ℝ)|=(4519915361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4156551847/10000000000 : ℝ)|^4271 ≤ (787832424641/2500000000000 : ℝ)^3247
        have hw : |(4156551847/10000000000 : ℝ)|=(4156551847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (537/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11011/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (537/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (537/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (537/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (537/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (537/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (537/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (537/5000 : ℝ) ^ (2135/512 : ℝ) ≤ (9106752970490723/100000000000000000000 : ℝ) := by
    have hpowers : (537/5000 : ℝ)^2135 ≤ (9106752970490723/100000000000000000000 : ℝ)^512 := by
      have hnat : (537 : ℕ)^2135*100000000000000000000^512 ≤ 9106752970490723^512*5000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        537 5000 9106752970490723 100000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (537/5000 : ℝ)) (X := (9106752970490723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15043/100000 : ℝ) ^ (2135/512 : ℝ) ≤ (37114956014878907/100000000000000000000 : ℝ) := by
    have hpowers : (15043/100000 : ℝ)^2135 ≤ (37114956014878907/100000000000000000000 : ℝ)^512 := by
      have hnat : (15043 : ℕ)^2135*100000000000000000000^512 ≤ 37114956014878907^512*100000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15043 100000 37114956014878907 100000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15043/100000 : ℝ)) (X := (37114956014878907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009106752970490723/50000000000000000000 : ℝ) ≤ (2000087350534279/2000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50009106752970490723/50000000000000000000 : ℝ)^512 ≤ (2000087350534279/2000000000000000 : ℝ)^2135 := by
      have hnat : (50009106752970490723 : ℕ)^512*2000000000000000^2135 ≤ 2000087350534279^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009106752970490723 50000000000000000000 2000087350534279 2000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000087350534279/2000000000000000 : ℝ)) (X := (50009106752970490723/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004622170898536963/10000000000000000000 : ℝ) ≤ (10001108260348147/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (10004622170898536963/10000000000000000000 : ℝ)^512 ≤ (10001108260348147/10000000000000000 : ℝ)^2135 := by
      have hnat : (10004622170898536963 : ℕ)^512*10000000000000000^2135 ≤ 10001108260348147^2135*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004622170898536963 10000000000000000000 10001108260348147 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001108260348147/10000000000000000 : ℝ)) (X := (10004622170898536963/10000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037114956014878907/50000000000000000000 : ℝ) ≤ (10001779768024899/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50037114956014878907/50000000000000000000 : ℝ)^512 ≤ (10001779768024899/10000000000000000 : ℝ)^2135 := by
      have hnat : (50037114956014878907 : ℕ)^512*10000000000000000^2135 ≤ 10001779768024899^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037114956014878907 50000000000000000000 10001779768024899 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001779768024899/10000000000000000 : ℝ)) (X := (50037114956014878907/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9106752970490723/100000000000000000000 : ℝ) ≤ ((1720698214473935189/1721200000000000000 : ℝ)+2*(41969229797/26893750000000 : ℝ)*(537/5000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (1720698214473935189/1721200000000000000 : ℝ)+2*(41969229797/26893750000000 : ℝ)*(537/5000 : ℝ)=(2000087350534279/2000000000000000 : ℝ) by norm_num, show 1+2*(9106752970490723/100000000000000000000 : ℝ)=(50009106752970490723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37114956014878907/100000000000000000000 : ℝ)+(9106752970490723/100000000000000000000 : ℝ) ≤ ((1720698214473935189/1721200000000000000 : ℝ)+(41969229797/26893750000000 : ℝ)*((15043/100000 : ℝ)+(537/5000 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (1720698214473935189/1721200000000000000 : ℝ)+(41969229797/26893750000000 : ℝ)*((15043/100000 : ℝ)+(537/5000 : ℝ))=(10001108260348147/10000000000000000 : ℝ) by norm_num, show 1+(37114956014878907/100000000000000000000 : ℝ)+(9106752970490723/100000000000000000000 : ℝ)=(10004622170898536963/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37114956014878907/100000000000000000000 : ℝ) ≤ ((1720698214473935189/1721200000000000000 : ℝ)+2*(41969229797/26893750000000 : ℝ)*(15043/100000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (1720698214473935189/1721200000000000000 : ℝ)+2*(41969229797/26893750000000 : ℝ)*(15043/100000 : ℝ)=(10001779768024899/10000000000000000 : ℝ) by norm_num, show 1+2*(37114956014878907/100000000000000000000 : ℝ)=(50037114956014878907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1720698214473935189/1721200000000000000 : ℝ)*(X 1 0+X 2 0)+(41969229797/26893750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (537/5000 : ℝ)) (hi := (15043/100000 : ℝ)) (c := (1720698214473935189/1721200000000000000 : ℝ)) (alpha := (41969229797/26893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1720698214473935189/1721200000000000000 : ℝ)*(X 0 1+X 2 1)+(41969229797/26893750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (537/5000 : ℝ)) (hi := (15043/100000 : ℝ)) (c := (1720698214473935189/1721200000000000000 : ℝ)) (alpha := (41969229797/26893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1720698214473935189/1721200000000000000 : ℝ)*(X 0 2+X 1 2)+(41969229797/26893750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (537/5000 : ℝ)) (hi := (15043/100000 : ℝ)) (c := (1720698214473935189/1721200000000000000 : ℝ)) (alpha := (41969229797/26893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2070680133/10000000000 : ℝ)*X 0 0+(677187167/1250000000 : ℝ)*X 0 1+(5240662201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350321623/10000000000 : ℝ)*X 1 0+(-216086661/1000000000 : ℝ)*X 1 1+(2620331073/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337580421/2500000000 : ℝ)*X 2 0+(131016551/250000000 : ℝ)*X 2 1+(-2160866669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2167283859/5000000000 : ℝ)*X 0 0+(129849707/312500000 : ℝ)*X 0 1+(4521269411/10000000000 : ℝ)*X 0 2+(2167283859/5000000000 : ℝ)*X 1 0+(129849707/312500000 : ℝ)*X 1 1+(4521269411/10000000000 : ℝ)*X 1 2+(2167283859/5000000000 : ℝ)*X 2 0+(129849707/312500000 : ℝ)*X 2 1+(4521269411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1035346909/5000000000 : ℝ)*X 0 0+(2620658231/5000000000 : ℝ)*X 0 1+(5416839757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326235067/2500000000 : ℝ)*X 1 0+(-198468889/1000000000 : ℝ)*X 1 1+(5416839543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304939797/10000000000 : ℝ)*X 2 0+(2708420047/5000000000 : ℝ)*X 2 1+(-1984688777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334596561/10000000000 : ℝ)*X 0 0+(4519915361/10000000000 : ℝ)*X 0 1+(4156551847/10000000000 : ℝ)*X 0 2+(4334596561/10000000000 : ℝ)*X 1 0+(4519915361/10000000000 : ℝ)*X 1 1+(4156551847/10000000000 : ℝ)*X 1 2+(4334596561/10000000000 : ℝ)*X 2 0+(4519915361/10000000000 : ℝ)*X 2 1+(4156551847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (121786217330676610990043991/17212000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1631638269/100000000000000 : ℝ)*(base19) + (1551266991/100000000000000 : ℝ)*(base23) + (255049287/100000000000000 : ℝ)*(upper3) + (38748489/50000000000000 : ℝ)*(upper4) + (9347473/10000000000000 : ℝ)*(upper5) + (838672728444873/20000000000000 : ℝ)*(major0) + (838672728444873/20000000000000 : ℝ)*(major1) + (838672728444873/20000000000000 : ℝ)*(major2) + (2827508005077193/50000000000000 : ℝ)*(sp0) + (5655042214056711/100000000000000 : ℝ)*(sp1) + (5655042294427989/100000000000000 : ℝ)*(sp2) + (273166622854451/10000000000000 : ℝ)*(sp3) + (5567108119/20000000000000 : ℝ)*(sp4) + (2121794247/12500000000000 : ℝ)*(sp7) + (1365841601449243/50000000000000 : ℝ)*(f.failure) + (5655043845694981/100000000000000 : ℝ)*(f.sum) + (776102607227/1075750000000000000000000000 : ℝ)*base66 + (23665777508105231/2648000000000000000000000000000 : ℝ)*base68 + (6740519156513231/2648000000000000000000000000000 : ℝ)*base70 + (18224340098641231/2648000000000000000000000000000 : ℝ)*base72 + (2015488135451/2151500000000000000000000000 : ℝ)*base74 + (48954963335846769/2648000000000000000000000000000 : ℝ)*base75 + (17492806668454769/2648000000000000000000000000000 : ℝ)*base77 + (149808295257231/2648000000000000000000000000000 : ℝ)*base80 + (21818871200273/4303000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (51221669/5000000000000000000000 : ℝ)*base90 + (51221669/5000000000000000000000 : ℝ)*base92 + (51221669/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81162075221758033824394461/8606000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2039275657/100000000000000 : ℝ)*(base19) + (882219533/50000000000000 : ℝ)*(base23) + (250451689/100000000000000 : ℝ)*(upper3) + (39458653/50000000000000 : ℝ)*(lower4) + (14924409/20000000000000 : ℝ)*(upper5) + (422465206695761/10000000000000 : ℝ)*(major0) + (422465206695761/10000000000000 : ℝ)*(major1) + (422465206695761/10000000000000 : ℝ)*(major2) + (797860813/2500000000000 : ℝ)*(sp1) + (41526565081/100000000000000 : ℝ)*(sp2) + (5697238395702109/100000000000000 : ℝ)*(sp4) + (5697204441993931/100000000000000 : ℝ)*(sp5) + (2848597552348981/50000000000000 : ℝ)*(sp6) + (137603271192537/5000000000000 : ℝ)*(sp7) + (137603271192537/5000000000000 : ℝ)*(f.failure) + (5697238395702109/100000000000000 : ℝ)*(f.sum) + (212347216221/430300000000000000000000000 : ℝ)*base65 + (11389866341804167/1324000000000000000000000000000 : ℝ)*base68 + (16454734066384167/1324000000000000000000000000000 : ℝ)*base70 + (2917409099444167/1324000000000000000000000000000 : ℝ)*base72 + (2213901954253/2151500000000000000000000000 : ℝ)*base74 + (5706838282944167/1324000000000000000000000000000 : ℝ)*base76 + (6738759944044167/1324000000000000000000000000000 : ℝ)*base78 + (6038384532244167/1324000000000000000000000000000 : ℝ)*base80 + (16575283783907/4303000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7083929/500000000000000000000 : ℝ)*base89 + (7083929/500000000000000000000 : ℝ)*base91 + (7083929/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1311_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (537/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11011/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1311_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1311_s5_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2070994259/10000000000 : ℝ)*x 0 + (1082963817/2000000000 : ℝ)*x 1 + (5243133847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2070994259/10000000000 : ℝ)^4271 ≤ (2520888136853/20000000000000 : ℝ)^3247 := by
    have hnat : (2070994259 : ℕ)^4271*20000000000000^3247 ≤ 2520888136853^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070994259 10000000000 2520888136853 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082963817/2000000000 : ℝ)^4271 ≤ (22311812426621/50000000000000 : ℝ)^3247 := by
    have hnat : (1082963817 : ℕ)^4271*50000000000000^3247 ≤ 22311812426621^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082963817 2000000000 22311812426621 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243133847/10000000000 : ℝ)^4271 ≤ (83538934471/195312500000 : ℝ)^3247 := by
    have hnat : (5243133847 : ℕ)^4271*195312500000^3247 ≤ 83538934471^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243133847 10000000000 83538934471 195312500000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2070994259/10000000000 : ℝ), (1082963817/2000000000 : ℝ), (5243133847/10000000000 : ℝ)] ![(2520888136853/20000000000000 : ℝ), (22311812426621/50000000000000 : ℝ), (83538934471/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2070994259/10000000000 : ℝ)|^4271 ≤ (2520888136853/20000000000000 : ℝ)^3247
        have hw : |(-2070994259/10000000000 : ℝ)|=(2070994259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082963817/2000000000 : ℝ)|^4271 ≤ (22311812426621/50000000000000 : ℝ)^3247
        have hw : |(1082963817/2000000000 : ℝ)|=(1082963817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243133847/10000000000 : ℝ)|^4271 ≤ (83538934471/195312500000 : ℝ)^3247
        have hw : |(5243133847/10000000000 : ℝ)|=(5243133847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s5_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349640331/10000000000 : ℝ)*x 0 + (-2158504273/10000000000 : ℝ)*x 1 + (524313389/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349640331/10000000000 : ℝ)^4271 ≤ (5489804213301/12500000000000 : ℝ)^3247 := by
    have hnat : (5349640331 : ℕ)^4271*12500000000000^3247 ≤ 5489804213301^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349640331 10000000000 5489804213301 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2158504273/10000000000 : ℝ)^4271 ≤ (1330963136911/10000000000000 : ℝ)^3247 := by
    have hnat : (2158504273 : ℕ)^4271*10000000000000^3247 ≤ 1330963136911^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158504273 10000000000 1330963136911 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524313389/1000000000 : ℝ)^4271 ≤ (21385967455279/50000000000000 : ℝ)^3247 := by
    have hnat : (524313389 : ℕ)^4271*50000000000000^3247 ≤ 21385967455279^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524313389 1000000000 21385967455279 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349640331/10000000000 : ℝ), (-2158504273/10000000000 : ℝ), (524313389/1000000000 : ℝ)] ![(5489804213301/12500000000000 : ℝ), (1330963136911/10000000000000 : ℝ), (21385967455279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349640331/10000000000 : ℝ)|^4271 ≤ (5489804213301/12500000000000 : ℝ)^3247
        have hw : |(5349640331/10000000000 : ℝ)|=(5349640331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2158504273/10000000000 : ℝ)|^4271 ≤ (1330963136911/10000000000000 : ℝ)^3247
        have hw : |(-2158504273/10000000000 : ℝ)|=(2158504273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524313389/1000000000 : ℝ)|^4271 ≤ (21385967455279/50000000000000 : ℝ)^3247
        have hw : |(524313389/1000000000 : ℝ)|=(524313389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s5_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213985599/400000000 : ℝ)*x 0 + (1048626777/2000000000 : ℝ)*x 1 + (-2158504753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213985599/400000000 : ℝ)^4271 ≤ (5489803732761/12500000000000 : ℝ)^3247 := by
    have hnat : (213985599 : ℕ)^4271*12500000000000^3247 ≤ 5489803732761^3247*400000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213985599 400000000 5489803732761 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048626777/2000000000 : ℝ)^4271 ≤ (42771934856907/100000000000000 : ℝ)^3247 := by
    have hnat : (1048626777 : ℕ)^4271*100000000000000^3247 ≤ 42771934856907^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048626777 2000000000 42771934856907 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158504753/10000000000 : ℝ)^4271 ≤ (2661927052453/20000000000000 : ℝ)^3247 := by
    have hnat : (2158504753 : ℕ)^4271*20000000000000^3247 ≤ 2661927052453^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158504753 10000000000 2661927052453 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213985599/400000000 : ℝ), (1048626777/2000000000 : ℝ), (-2158504753/10000000000 : ℝ)] ![(5489803732761/12500000000000 : ℝ), (42771934856907/100000000000000 : ℝ), (2661927052453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213985599/400000000 : ℝ)|^4271 ≤ (5489803732761/12500000000000 : ℝ)^3247
        have hw : |(213985599/400000000 : ℝ)|=(213985599/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048626777/2000000000 : ℝ)|^4271 ≤ (42771934856907/100000000000000 : ℝ)^3247
        have hw : |(1048626777/2000000000 : ℝ)|=(1048626777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2158504753/10000000000 : ℝ)|^4271 ≤ (2661927052453/20000000000000 : ℝ)^3247
        have hw : |(-2158504753/10000000000 : ℝ)|=(2158504753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s5_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135461059/312500000 : ℝ)*x 0 + (4160498379/10000000000 : ℝ)*x 1 + (1128978843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135461059/312500000 : ℝ)^4271 ≤ (33302331241771/100000000000000 : ℝ)^3247 := by
    have hnat : (135461059 : ℕ)^4271*100000000000000^3247 ≤ 33302331241771^3247*312500000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135461059 312500000 33302331241771 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4160498379/10000000000 : ℝ)^4271 ≤ (7888165004649/25000000000000 : ℝ)^3247 := by
    have hnat : (4160498379 : ℕ)^4271*25000000000000^3247 ≤ 7888165004649^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160498379 10000000000 7888165004649 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128978843/2500000000 : ℝ)^4271 ≤ (54914076123/156250000000 : ℝ)^3247 := by
    have hnat : (1128978843 : ℕ)^4271*156250000000^3247 ≤ 54914076123^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128978843 2500000000 54914076123 156250000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135461059/312500000 : ℝ), (4160498379/10000000000 : ℝ), (1128978843/2500000000 : ℝ)] ![(33302331241771/100000000000000 : ℝ), (7888165004649/25000000000000 : ℝ), (54914076123/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135461059/312500000 : ℝ)|^4271 ≤ (33302331241771/100000000000000 : ℝ)^3247
        have hw : |(135461059/312500000 : ℝ)|=(135461059/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4160498379/10000000000 : ℝ)|^4271 ≤ (7888165004649/25000000000000 : ℝ)^3247
        have hw : |(4160498379/10000000000 : ℝ)|=(4160498379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128978843/2500000000 : ℝ)|^4271 ≤ (54914076123/156250000000 : ℝ)^3247
        have hw : |(1128978843/2500000000 : ℝ)|=(1128978843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s5_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-258875903/1250000000 : ℝ)*x 0 + (5243750259/10000000000 : ℝ)*x 1 + (1353549827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258875903/1250000000 : ℝ)^4271 ≤ (12604544476513/100000000000000 : ℝ)^3247 := by
    have hnat : (258875903 : ℕ)^4271*100000000000000^3247 ≤ 12604544476513^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258875903 1250000000 12604544476513 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243750259/10000000000 : ℝ)^4271 ≤ (42778548908723/100000000000000 : ℝ)^3247 := by
    have hnat : (5243750259 : ℕ)^4271*100000000000000^3247 ≤ 42778548908723^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243750259 10000000000 42778548908723 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353549827/2500000000 : ℝ)^4271 ≤ (44616906608907/100000000000000 : ℝ)^3247 := by
    have hnat : (1353549827 : ℕ)^4271*100000000000000^3247 ≤ 44616906608907^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353549827 2500000000 44616906608907 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258875903/1250000000 : ℝ), (5243750259/10000000000 : ℝ), (1353549827/2500000000 : ℝ)] ![(12604544476513/100000000000000 : ℝ), (42778548908723/100000000000000 : ℝ), (44616906608907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258875903/1250000000 : ℝ)|^4271 ≤ (12604544476513/100000000000000 : ℝ)^3247
        have hw : |(-258875903/1250000000 : ℝ)|=(258875903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243750259/10000000000 : ℝ)|^4271 ≤ (42778548908723/100000000000000 : ℝ)^3247
        have hw : |(5243750259/10000000000 : ℝ)|=(5243750259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353549827/2500000000 : ℝ)|^4271 ≤ (44616906608907/100000000000000 : ℝ)^3247
        have hw : |(1353549827/2500000000 : ℝ)|=(1353549827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s5_5 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165799379/312500000 : ℝ)*x 0 + (-496859813/2500000000 : ℝ)*x 1 + (338387459/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165799379/312500000 : ℝ)^4271 ≤ (2715203874229/6250000000000 : ℝ)^3247 := by
    have hnat : (165799379 : ℕ)^4271*6250000000000^3247 ≤ 2715203874229^3247*312500000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165799379 312500000 2715203874229 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496859813/2500000000 : ℝ)^4271 ≤ (5969915495609/50000000000000 : ℝ)^3247 := by
    have hnat : (496859813 : ℕ)^4271*50000000000000^3247 ≤ 5969915495609^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496859813 2500000000 5969915495609 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338387459/625000000 : ℝ)^4271 ≤ (11154226749783/25000000000000 : ℝ)^3247 := by
    have hnat : (338387459 : ℕ)^4271*25000000000000^3247 ≤ 11154226749783^3247*625000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338387459 625000000 11154226749783 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165799379/312500000 : ℝ), (-496859813/2500000000 : ℝ), (338387459/625000000 : ℝ)] ![(2715203874229/6250000000000 : ℝ), (5969915495609/50000000000000 : ℝ), (11154226749783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165799379/312500000 : ℝ)|^4271 ≤ (2715203874229/6250000000000 : ℝ)^3247
        have hw : |(165799379/312500000 : ℝ)|=(165799379/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496859813/2500000000 : ℝ)|^4271 ≤ (5969915495609/50000000000000 : ℝ)^3247
        have hw : |(-496859813/2500000000 : ℝ)|=(496859813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338387459/625000000 : ℝ)|^4271 ≤ (11154226749783/25000000000000 : ℝ)^3247
        have hw : |(338387459/625000000 : ℝ)|=(338387459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s5_6 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061116037/2000000000 : ℝ)*x 0 + (676774859/1250000000 : ℝ)*x 1 + (-1987439823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061116037/2000000000 : ℝ)^4271 ≤ (2715203912599/6250000000000 : ℝ)^3247 := by
    have hnat : (1061116037 : ℕ)^4271*6250000000000^3247 ≤ 2715203912599^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061116037 2000000000 2715203912599 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676774859/1250000000 : ℝ)^4271 ≤ (892338037657/2000000000000 : ℝ)^3247 := by
    have hnat : (676774859 : ℕ)^4271*2000000000000^3247 ≤ 892338037657^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676774859 1250000000 892338037657 2000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987439823/10000000000 : ℝ)^4271 ≤ (2984958875853/25000000000000 : ℝ)^3247 := by
    have hnat : (1987439823 : ℕ)^4271*25000000000000^3247 ≤ 2984958875853^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987439823 10000000000 2984958875853 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061116037/2000000000 : ℝ), (676774859/1250000000 : ℝ), (-1987439823/10000000000 : ℝ)] ![(2715203912599/6250000000000 : ℝ), (892338037657/2000000000000 : ℝ), (2984958875853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061116037/2000000000 : ℝ)|^4271 ≤ (2715203912599/6250000000000 : ℝ)^3247
        have hw : |(1061116037/2000000000 : ℝ)|=(1061116037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676774859/1250000000 : ℝ)|^4271 ≤ (892338037657/2000000000000 : ℝ)^3247
        have hw : |(676774859/1250000000 : ℝ)|=(676774859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1987439823/10000000000 : ℝ)|^4271 ≤ (2984958875853/25000000000000 : ℝ)^3247
        have hw : |(-1987439823/10000000000 : ℝ)|=(1987439823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s5_7 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2167390389/5000000000 : ℝ)*x 0 + (2257319143/5000000000 : ℝ)*x 1 + (83235631/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167390389/5000000000 : ℝ)^4271 ≤ (8325650744681/25000000000000 : ℝ)^3247 := by
    have hnat : (2167390389 : ℕ)^4271*25000000000000^3247 ≤ 8325650744681^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167390389 5000000000 8325650744681 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257319143/5000000000 : ℝ)^4271 ≤ (8782983999979/25000000000000 : ℝ)^3247 := by
    have hnat : (2257319143 : ℕ)^4271*25000000000000^3247 ≤ 8782983999979^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257319143 5000000000 8782983999979 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83235631/200000000 : ℝ)^4271 ≤ (7891365252149/25000000000000 : ℝ)^3247 := by
    have hnat : (83235631 : ℕ)^4271*25000000000000^3247 ≤ 7891365252149^3247*200000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83235631 200000000 7891365252149 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2167390389/5000000000 : ℝ), (2257319143/5000000000 : ℝ), (83235631/200000000 : ℝ)] ![(8325650744681/25000000000000 : ℝ), (8782983999979/25000000000000 : ℝ), (7891365252149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2167390389/5000000000 : ℝ)|^4271 ≤ (8325650744681/25000000000000 : ℝ)^3247
        have hw : |(2167390389/5000000000 : ℝ)|=(2167390389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257319143/5000000000 : ℝ)|^4271 ≤ (8782983999979/25000000000000 : ℝ)^3247
        have hw : |(2257319143/5000000000 : ℝ)|=(2257319143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83235631/200000000 : ℝ)|^4271 ≤ (7891365252149/25000000000000 : ℝ)^3247
        have hw : |(83235631/200000000 : ℝ)|=(83235631/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1383/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7349/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11011/100000 : ℝ) ^ (2135/512 : ℝ) ≤ (2020795905007521/20000000000000000000 : ℝ) := by
    have hpowers : (11011/100000 : ℝ)^2135 ≤ (2020795905007521/20000000000000000000 : ℝ)^512 := by
      have hnat : (11011 : ℕ)^2135*20000000000000000000^512 ≤ 2020795905007521^512*100000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11011 100000 2020795905007521 20000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11011/100000 : ℝ)) (X := (2020795905007521/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7377/50000 : ℝ) ^ (2135/512 : ℝ) ≤ (85577326866901/250000000000000000 : ℝ) := by
    have hpowers : (7377/50000 : ℝ)^2135 ≤ (85577326866901/250000000000000000 : ℝ)^512 := by
      have hnat : (7377 : ℕ)^2135*250000000000000000^512 ≤ 85577326866901^512*50000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7377 50000 85577326866901 250000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7377/50000 : ℝ)) (X := (85577326866901/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002020795905007521/10000000000000000000 : ℝ) ≤ (10000484575195487/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (10002020795905007521/10000000000000000000 : ℝ)^512 ≤ (10000484575195487/10000000000000000 : ℝ)^2135 := by
      have hnat : (10002020795905007521 : ℕ)^512*10000000000000000^2135 ≤ 10000484575195487^2135*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002020795905007521 10000000000000000000 10000484575195487 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000484575195487/10000000000000000 : ℝ)) (X := (10002020795905007521/10000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008866982054359601/20000000000000000000 : ℝ) ≤ (5000531514048487/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (20008866982054359601/20000000000000000000 : ℝ)^512 ≤ (5000531514048487/5000000000000000 : ℝ)^2135 := by
      have hnat : (20008866982054359601 : ℕ)^512*5000000000000000^2135 ≤ 5000531514048487^2135*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008866982054359601 20000000000000000000 5000531514048487 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000531514048487/5000000000000000 : ℝ)) (X := (20008866982054359601/20000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (125085577326866901/125000000000000000 : ℝ) ≤ (10001641480998461/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (125085577326866901/125000000000000000 : ℝ)^512 ≤ (10001641480998461/10000000000000000 : ℝ)^2135 := by
      have hnat : (125085577326866901 : ℕ)^512*10000000000000000^2135 ≤ 10001641480998461^2135*125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125085577326866901 125000000000000000 10001641480998461 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001641480998461/10000000000000000 : ℝ)) (X := (125085577326866901/125000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2020795905007521/20000000000000000000 : ℝ) ≤ ((37419075075160161127/37430000000000000000 : ℝ)+2*(578452901487/374300000000000 : ℝ)*(11011/100000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (37419075075160161127/37430000000000000000 : ℝ)+2*(578452901487/374300000000000 : ℝ)*(11011/100000 : ℝ)=(10000484575195487/10000000000000000 : ℝ) by norm_num, show 1+2*(2020795905007521/20000000000000000000 : ℝ)=(10002020795905007521/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(85577326866901/250000000000000000 : ℝ)+(2020795905007521/20000000000000000000 : ℝ) ≤ ((37419075075160161127/37430000000000000000 : ℝ)+(578452901487/374300000000000 : ℝ)*((7377/50000 : ℝ)+(11011/100000 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (37419075075160161127/37430000000000000000 : ℝ)+(578452901487/374300000000000 : ℝ)*((7377/50000 : ℝ)+(11011/100000 : ℝ))=(5000531514048487/5000000000000000 : ℝ) by norm_num, show 1+(85577326866901/250000000000000000 : ℝ)+(2020795905007521/20000000000000000000 : ℝ)=(20008866982054359601/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(85577326866901/250000000000000000 : ℝ) ≤ ((37419075075160161127/37430000000000000000 : ℝ)+2*(578452901487/374300000000000 : ℝ)*(7377/50000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (37419075075160161127/37430000000000000000 : ℝ)+2*(578452901487/374300000000000 : ℝ)*(7377/50000 : ℝ)=(10001641480998461/10000000000000000 : ℝ) by norm_num, show 1+2*(85577326866901/250000000000000000 : ℝ)=(125085577326866901/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37419075075160161127/37430000000000000000 : ℝ)*(X 1 0+X 2 0)+(578452901487/374300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (11011/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (37419075075160161127/37430000000000000000 : ℝ)) (alpha := (578452901487/374300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37419075075160161127/37430000000000000000 : ℝ)*(X 0 1+X 2 1)+(578452901487/374300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (11011/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (37419075075160161127/37430000000000000000 : ℝ)) (alpha := (578452901487/374300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37419075075160161127/37430000000000000000 : ℝ)*(X 0 2+X 1 2)+(578452901487/374300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (11011/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (37419075075160161127/37430000000000000000 : ℝ)) (alpha := (578452901487/374300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2070994259/10000000000 : ℝ)*X 0 0+(1082963817/2000000000 : ℝ)*X 0 1+(5243133847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349640331/10000000000 : ℝ)*X 1 0+(-2158504273/10000000000 : ℝ)*X 1 1+(524313389/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213985599/400000000 : ℝ)*X 2 0+(1048626777/2000000000 : ℝ)*X 2 1+(-2158504753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135461059/312500000 : ℝ)*X 0 0+(4160498379/10000000000 : ℝ)*X 0 1+(1128978843/2500000000 : ℝ)*X 0 2+(135461059/312500000 : ℝ)*X 1 0+(4160498379/10000000000 : ℝ)*X 1 1+(1128978843/2500000000 : ℝ)*X 1 2+(135461059/312500000 : ℝ)*X 2 0+(4160498379/10000000000 : ℝ)*X 2 1+(1128978843/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-258875903/1250000000 : ℝ)*X 0 0+(5243750259/10000000000 : ℝ)*X 0 1+(1353549827/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165799379/312500000 : ℝ)*X 1 0+(-496859813/2500000000 : ℝ)*X 1 1+(338387459/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061116037/2000000000 : ℝ)*X 2 0+(676774859/1250000000 : ℝ)*X 2 1+(-1987439823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2167390389/5000000000 : ℝ)*X 0 0+(2257319143/5000000000 : ℝ)*X 0 1+(83235631/200000000 : ℝ)*X 0 2+(2167390389/5000000000 : ℝ)*X 1 0+(2257319143/5000000000 : ℝ)*X 1 1+(83235631/200000000 : ℝ)*X 1 2+(2167390389/5000000000 : ℝ)*X 2 0+(2257319143/5000000000 : ℝ)*X 2 1+(83235631/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (637997629927287716674423233/93575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (859619111/100000000000000 : ℝ)*(base19) + (407321589/100000000000000 : ℝ)*(base23) + (9308229/25000000000000 : ℝ)*(lower4) + (46689399/100000000000000 : ℝ)*(lower5) + (215957272381631/5000000000000 : ℝ)*(major0) + (215957272381631/5000000000000 : ℝ)*(major1) + (215957272381631/5000000000000 : ℝ)*(major2) + (291232202302173/5000000000000 : ℝ)*(sp0) + (1164933710844171/20000000000000 : ℝ)*(sp1) + (2912326350972671/50000000000000 : ℝ)*(sp2) + (351701193793473/12500000000000 : ℝ)*(sp3) + (12683898253/50000000000000 : ℝ)*(sp4) + (3260914607/20000000000000 : ℝ)*(sp6) + (731488103/6250000000000 : ℝ)*(sp7) + (351702656769679/12500000000000 : ℝ)*(f.failure) + (2912334706919983/50000000000000 : ℝ)*(f.sum) + (1455200046269/467875000000000000000000000 : ℝ)*base65 + (1192362980233941863/187150000000000000000000000000000 : ℝ)*base68 + (2439939296744641863/187150000000000000000000000000000 : ℝ)*base70 + (2778904408243391863/187150000000000000000000000000000 : ℝ)*base72 + (2121175558219/3743000000000000000000000000 : ℝ)*base74 + (1984466256000941863/187150000000000000000000000000000 : ℝ)*base76 + (1846945116521391863/187150000000000000000000000000000 : ℝ)*base78 + (827888549121341863/187150000000000000000000000000000 : ℝ)*base80 + (4564066979457/3743000000000000000000000000 : ℝ)*base81 + (6888143/1250000000000000000000 : ℝ)*base89 + (6888143/1250000000000000000000 : ℝ)*base91 + (6888143/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25208142479624801620737/2339375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1443391417/100000000000000 : ℝ)*(base19) + (89040467/6250000000000 : ℝ)*(base23) + (629547/4000000000000 : ℝ)*(upper3) + (39364813/50000000000000 : ℝ)*(lower4) + (96410691/25000000000000 : ℝ)*(upper5) + (4350435781515077/100000000000000 : ℝ)*(major0) + (4350435781515077/100000000000000 : ℝ)*(major1) + (4350435781515077/100000000000000 : ℝ)*(major2) + (9752006647/25000000000000 : ℝ)*(sp1) + (11292529999/100000000000000 : ℝ)*(sp2) + (1466716621264239/25000000000000 : ℝ)*(sp4) + (5866826033638951/100000000000000 : ℝ)*(sp5) + (2933426883939743/50000000000000 : ℝ)*(sp6) + (354250589848363/12500000000000 : ℝ)*(sp7) + (354250589848363/12500000000000 : ℝ)*(f.failure) + (1466716621264239/25000000000000 : ℝ)*(f.sum) + (108538439839621/18715000000000000000000000000 : ℝ)*base66 + (5538745170514288221/3743000000000000000000000000000000 : ℝ)*base68 + (15743767550985711779/3743000000000000000000000000000000 : ℝ)*base69 + (9061879553874288221/3743000000000000000000000000000000 : ℝ)*base72 + (148865712732621/18715000000000000000000000000 : ℝ)*base74 + (118731929644097711779/3743000000000000000000000000000000 : ℝ)*base75 + (31853787265071288221/3743000000000000000000000000000000 : ℝ)*base78 + (11625513823356711779/3743000000000000000000000000000000 : ℝ)*base79 + (30512247393813/9357500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11671371/1250000000000000000000 : ℝ)*base89 + (11671371/1250000000000000000000 : ℝ)*base91 + (11671371/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1311_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1311_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1311_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9641/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1311_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1311_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1311_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9641/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

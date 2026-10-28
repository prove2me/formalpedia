-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1159_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:39:24.637068+00:00
-- url     : https://prove2.me/submissions/3312fe84-b751-49d2-b020-5bcbd9cdb392

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
theorem support_rectangle_w1159_s3_0 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155161491/10000000000 : ℝ)*x 0 + (678432521/1250000000 : ℝ)*x 1 + (1046729469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155161491/10000000000 : ℝ)^261 ≤ (13090171700039/100000000000000 : ℝ)^197 := by
    have hnat : (2155161491 : ℕ)^261*100000000000000^197 ≤ 13090171700039^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155161491 10000000000 13090171700039 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678432521/1250000000 : ℝ)^261 ≤ (4450145749569/10000000000000 : ℝ)^197 := by
    have hnat : (678432521 : ℕ)^261*10000000000000^197 ≤ 4450145749569^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678432521 1250000000 4450145749569 10000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046729469/2000000000 : ℝ)^261 ≤ (42408370780207/100000000000000 : ℝ)^197 := by
    have hnat : (1046729469 : ℕ)^261*100000000000000^197 ≤ 42408370780207^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046729469 2000000000 42408370780207 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155161491/10000000000 : ℝ), (678432521/1250000000 : ℝ), (1046729469/2000000000 : ℝ)] ![(13090171700039/100000000000000 : ℝ), (4450145749569/10000000000000 : ℝ), (42408370780207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155161491/10000000000 : ℝ)|^261 ≤ (13090171700039/100000000000000 : ℝ)^197
        have hw : |(-2155161491/10000000000 : ℝ)|=(2155161491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678432521/1250000000 : ℝ)|^261 ≤ (4450145749569/10000000000000 : ℝ)^197
        have hw : |(678432521/1250000000 : ℝ)|=(678432521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046729469/2000000000 : ℝ)|^261 ≤ (42408370780207/100000000000000 : ℝ)^197
        have hw : |(1046729469/2000000000 : ℝ)|=(1046729469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s3_1 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1338347789/2500000000 : ℝ)*x 0 + (-450839171/2000000000 : ℝ)*x 1 + (1046729431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338347789/2500000000 : ℝ)^261 ≤ (10924657778071/25000000000000 : ℝ)^197 := by
    have hnat : (1338347789 : ℕ)^261*25000000000000^197 ≤ 10924657778071^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338347789 2500000000 10924657778071 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450839171/2000000000 : ℝ)^261 ≤ (13893000129503/100000000000000 : ℝ)^197 := by
    have hnat : (450839171 : ℕ)^261*100000000000000^197 ≤ 13893000129503^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450839171 2000000000 13893000129503 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046729431/2000000000 : ℝ)^261 ≤ (42408368740467/100000000000000 : ℝ)^197 := by
    have hnat : (1046729431 : ℕ)^261*100000000000000^197 ≤ 42408368740467^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046729431 2000000000 42408368740467 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338347789/2500000000 : ℝ), (-450839171/2000000000 : ℝ), (1046729431/2000000000 : ℝ)] ![(10924657778071/25000000000000 : ℝ), (13893000129503/100000000000000 : ℝ), (42408368740467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338347789/2500000000 : ℝ)|^261 ≤ (10924657778071/25000000000000 : ℝ)^197
        have hw : |(1338347789/2500000000 : ℝ)|=(1338347789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450839171/2000000000 : ℝ)|^261 ≤ (13893000129503/100000000000000 : ℝ)^197
        have hw : |(-450839171/2000000000 : ℝ)|=(450839171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046729431/2000000000 : ℝ)|^261 ≤ (42408368740467/100000000000000 : ℝ)^197
        have hw : |(1046729431/2000000000 : ℝ)|=(1046729431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s3_2 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1338347809/2500000000 : ℝ)*x 0 + (5233647189/10000000000 : ℝ)*x 1 + (-281774463/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338347809/2500000000 : ℝ)^261 ≤ (21849315988729/50000000000000 : ℝ)^197 := by
    have hnat : (1338347809 : ℕ)^261*50000000000000^197 ≤ 21849315988729^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338347809 2500000000 21849315988729 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233647189/10000000000 : ℝ)^261 ≤ (42408369105473/100000000000000 : ℝ)^197 := by
    have hnat : (5233647189 : ℕ)^261*100000000000000^197 ≤ 42408369105473^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233647189 10000000000 42408369105473 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281774463/1250000000 : ℝ)^261 ≤ (555719955861/4000000000000 : ℝ)^197 := by
    have hnat : (281774463 : ℕ)^261*4000000000000^197 ≤ 555719955861^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281774463 1250000000 555719955861 4000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338347809/2500000000 : ℝ), (5233647189/10000000000 : ℝ), (-281774463/1250000000 : ℝ)] ![(21849315988729/50000000000000 : ℝ), (42408369105473/100000000000000 : ℝ), (555719955861/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338347809/2500000000 : ℝ)|^261 ≤ (21849315988729/50000000000000 : ℝ)^197
        have hw : |(1338347809/2500000000 : ℝ)|=(1338347809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233647189/10000000000 : ℝ)|^261 ≤ (42408369105473/100000000000000 : ℝ)^197
        have hw : |(5233647189/10000000000 : ℝ)|=(5233647189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281774463/1250000000 : ℝ)|^261 ≤ (555719955861/4000000000000 : ℝ)^197
        have hw : |(-281774463/1250000000 : ℝ)|=(281774463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s3_3 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4360131731/10000000000 : ℝ)*x 0 + (521367889/1250000000 : ℝ)*x 1 + (2278907393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360131731/10000000000 : ℝ)^261 ≤ (33295284706651/100000000000000 : ℝ)^197 := by
    have hnat : (4360131731 : ℕ)^261*100000000000000^197 ≤ 33295284706651^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360131731 10000000000 33295284706651 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521367889/1250000000 : ℝ)^261 ≤ (1962178957763/6250000000000 : ℝ)^197 := by
    have hnat : (521367889 : ℕ)^261*6250000000000^197 ≤ 1962178957763^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521367889 1250000000 1962178957763 6250000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278907393/5000000000 : ℝ)^261 ≤ (35309851953423/100000000000000 : ℝ)^197 := by
    have hnat : (2278907393 : ℕ)^261*100000000000000^197 ≤ 35309851953423^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278907393 5000000000 35309851953423 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360131731/10000000000 : ℝ), (521367889/1250000000 : ℝ), (2278907393/5000000000 : ℝ)] ![(33295284706651/100000000000000 : ℝ), (1962178957763/6250000000000 : ℝ), (35309851953423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360131731/10000000000 : ℝ)|^261 ≤ (33295284706651/100000000000000 : ℝ)^197
        have hw : |(4360131731/10000000000 : ℝ)|=(4360131731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521367889/1250000000 : ℝ)|^261 ≤ (1962178957763/6250000000000 : ℝ)^197
        have hw : |(521367889/1250000000 : ℝ)|=(521367889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2278907393/5000000000 : ℝ)|^261 ≤ (35309851953423/100000000000000 : ℝ)^197
        have hw : |(2278907393/5000000000 : ℝ)|=(2278907393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s3_4 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077589371/5000000000 : ℝ)*x 0 + (5234390527/10000000000 : ℝ)*x 1 + (5426712901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077589371/5000000000 : ℝ)^261 ≤ (1636288815109/12500000000000 : ℝ)^197 := by
    have hnat : (1077589371 : ℕ)^261*12500000000000^197 ≤ 1636288815109^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077589371 5000000000 1636288815109 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234390527/10000000000 : ℝ)^261 ≤ (662755459043/1562500000000 : ℝ)^197 := by
    have hnat : (5234390527 : ℕ)^261*1562500000000^197 ≤ 662755459043^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234390527 10000000000 662755459043 1562500000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426712901/10000000000 : ℝ)^261 ≤ (44493340076723/100000000000000 : ℝ)^197 := by
    have hnat : (5426712901 : ℕ)^261*100000000000000^197 ≤ 44493340076723^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426712901 10000000000 44493340076723 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077589371/5000000000 : ℝ), (5234390527/10000000000 : ℝ), (5426712901/10000000000 : ℝ)] ![(1636288815109/12500000000000 : ℝ), (662755459043/1562500000000 : ℝ), (44493340076723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077589371/5000000000 : ℝ)|^261 ≤ (1636288815109/12500000000000 : ℝ)^197
        have hw : |(-1077589371/5000000000 : ℝ)|=(1077589371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234390527/10000000000 : ℝ)|^261 ≤ (662755459043/1562500000000 : ℝ)^197
        have hw : |(5234390527/10000000000 : ℝ)|=(5234390527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426712901/10000000000 : ℝ)|^261 ≤ (44493340076723/100000000000000 : ℝ)^197
        have hw : |(5426712901/10000000000 : ℝ)|=(5426712901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s3_5 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (663028591/1250000000 : ℝ)*x 0 + (-2061130597/10000000000 : ℝ)*x 1 + (2713356357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663028591/1250000000 : ℝ)^261 ≤ (43167750600053/100000000000000 : ℝ)^197 := by
    have hnat : (663028591 : ℕ)^261*100000000000000^197 ≤ 43167750600053^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663028591 1250000000 43167750600053 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061130597/10000000000 : ℝ)^261 ≤ (49355645359/400000000000 : ℝ)^197 := by
    have hnat : (2061130597 : ℕ)^261*400000000000^197 ≤ 49355645359^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061130597 10000000000 49355645359 400000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713356357/5000000000 : ℝ)^261 ≤ (44493338045423/100000000000000 : ℝ)^197 := by
    have hnat : (2713356357 : ℕ)^261*100000000000000^197 ≤ 44493338045423^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713356357 5000000000 44493338045423 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663028591/1250000000 : ℝ), (-2061130597/10000000000 : ℝ), (2713356357/5000000000 : ℝ)] ![(43167750600053/100000000000000 : ℝ), (49355645359/400000000000 : ℝ), (44493338045423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663028591/1250000000 : ℝ)|^261 ≤ (43167750600053/100000000000000 : ℝ)^197
        have hw : |(663028591/1250000000 : ℝ)|=(663028591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061130597/10000000000 : ℝ)|^261 ≤ (49355645359/400000000000 : ℝ)^197
        have hw : |(-2061130597/10000000000 : ℝ)|=(2061130597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713356357/5000000000 : ℝ)|^261 ≤ (44493338045423/100000000000000 : ℝ)^197
        have hw : |(2713356357/5000000000 : ℝ)|=(2713356357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s3_6 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (212169181/400000000 : ℝ)*x 0 + (1356678021/2500000000 : ℝ)*x 1 + (-257641297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212169181/400000000 : ℝ)^261 ≤ (43167759193547/100000000000000 : ℝ)^197 := by
    have hnat : (212169181 : ℕ)^261*100000000000000^197 ≤ 43167759193547^197*400000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212169181 400000000 43167759193547 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356678021/2500000000 : ℝ)^261 ≤ (22246665601003/50000000000000 : ℝ)^197 := by
    have hnat : (1356678021 : ℕ)^261*50000000000000^197 ≤ 22246665601003^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356678021 2500000000 22246665601003 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257641297/1250000000 : ℝ)^261 ≤ (771181849183/6250000000000 : ℝ)^197 := by
    have hnat : (257641297 : ℕ)^261*6250000000000^197 ≤ 771181849183^197*1250000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257641297 1250000000 771181849183 6250000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212169181/400000000 : ℝ), (1356678021/2500000000 : ℝ), (-257641297/1250000000 : ℝ)] ![(43167759193547/100000000000000 : ℝ), (22246665601003/50000000000000 : ℝ), (771181849183/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212169181/400000000 : ℝ)|^261 ≤ (43167759193547/100000000000000 : ℝ)^197
        have hw : |(212169181/400000000 : ℝ)|=(212169181/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356678021/2500000000 : ℝ)|^261 ≤ (22246665601003/50000000000000 : ℝ)^197
        have hw : |(1356678021/2500000000 : ℝ)|=(1356678021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257641297/1250000000 : ℝ)|^261 ≤ (771181849183/6250000000000 : ℝ)^197
        have hw : |(-257641297/1250000000 : ℝ)|=(257641297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s3_7 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (872033193/2000000000 : ℝ)*x 0 + (2278165709/5000000000 : ℝ)*x 1 + (4172434949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872033193/2000000000 : ℝ)^261 ≤ (1664781552849/5000000000000 : ℝ)^197 := by
    have hnat : (872033193 : ℕ)^261*5000000000000^197 ≤ 1664781552849^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872033193 2000000000 1664781552849 5000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2278165709/5000000000 : ℝ)^261 ≤ (35294627579251/100000000000000 : ℝ)^197 := by
    have hnat : (2278165709 : ℕ)^261*100000000000000^197 ≤ 35294627579251^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278165709 5000000000 35294627579251 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172434949/10000000000 : ℝ)^261 ≤ (785243533671/2500000000000 : ℝ)^197 := by
    have hnat : (4172434949 : ℕ)^261*2500000000000^197 ≤ 785243533671^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172434949 10000000000 785243533671 2500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872033193/2000000000 : ℝ), (2278165709/5000000000 : ℝ), (4172434949/10000000000 : ℝ)] ![(1664781552849/5000000000000 : ℝ), (35294627579251/100000000000000 : ℝ), (785243533671/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872033193/2000000000 : ℝ)|^261 ≤ (1664781552849/5000000000000 : ℝ)^197
        have hw : |(872033193/2000000000 : ℝ)|=(872033193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2278165709/5000000000 : ℝ)|^261 ≤ (35294627579251/100000000000000 : ℝ)^197
        have hw : |(2278165709/5000000000 : ℝ)|=(2278165709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172434949/10000000000 : ℝ)|^261 ≤ (785243533671/2500000000000 : ℝ)^197
        have hw : |(4172434949/10000000000 : ℝ)|=(4172434949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1159_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2137/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7393/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16453/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16453/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16453/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16453/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16453/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16453/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4573/50000 : ℝ) ^ (8351/2048 : ℝ) ≤ (1162273089198851/20000000000000000000 : ℝ) := by
    have hpowers : (4573/50000 : ℝ)^8351 ≤ (1162273089198851/20000000000000000000 : ℝ)^2048 := by
      have hnat : (4573 : ℕ)^8351*20000000000000000000^2048 ≤ 1162273089198851^2048*50000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4573 50000 1162273089198851 20000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4573/50000 : ℝ)) (X := (1162273089198851/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16453/100000 : ℝ) ^ (8351/2048 : ℝ) ≤ (63698943887997979/100000000000000000000 : ℝ) := by
    have hpowers : (16453/100000 : ℝ)^8351 ≤ (63698943887997979/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16453 : ℕ)^8351*100000000000000000000^2048 ≤ 63698943887997979^2048*100000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16453 100000 63698943887997979 100000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16453/100000 : ℝ)) (X := (63698943887997979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001162273089198851/10000000000000000000 : ℝ) ≤ (5000142511728407/5000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (10001162273089198851/10000000000000000000 : ℝ)^2048 ≤ (5000142511728407/5000000000000000 : ℝ)^8351 := by
      have hnat : (10001162273089198851 : ℕ)^2048*5000000000000000^8351 ≤ 5000142511728407^8351*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001162273089198851 10000000000000000000 5000142511728407 5000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000142511728407/5000000000000000 : ℝ)) (X := (10001162273089198851/10000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50034755154666996117/50000000000000000000 : ℝ) ≤ (10001704224474459/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (50034755154666996117/50000000000000000000 : ℝ)^2048 ≤ (10001704224474459/10000000000000000 : ℝ)^8351 := by
      have hnat : (50034755154666996117 : ℕ)^2048*10000000000000000^8351 ≤ 10001704224474459^8351*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034755154666996117 50000000000000000000 10001704224474459 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001704224474459/10000000000000000 : ℝ)) (X := (50034755154666996117/50000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50063698943887997979/50000000000000000000 : ℝ) ≤ (1250390428186513/1250000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (50063698943887997979/50000000000000000000 : ℝ)^2048 ≤ (1250390428186513/1250000000000000 : ℝ)^8351 := by
      have hnat : (50063698943887997979 : ℕ)^2048*1250000000000000^8351 ≤ 1250390428186513^8351*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50063698943887997979 50000000000000000000 1250390428186513 1250000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250390428186513/1250000000000000 : ℝ)) (X := (50063698943887997979/50000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1162273089198851/20000000000000000000 : ℝ) ≤ ((36523061320692088779/36535000000000000000 : ℝ)+2*(283840203529/146140000000000 : ℝ)*(4573/50000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (36523061320692088779/36535000000000000000 : ℝ)+2*(283840203529/146140000000000 : ℝ)*(4573/50000 : ℝ)=(5000142511728407/5000000000000000 : ℝ) by norm_num, show 1+2*(1162273089198851/20000000000000000000 : ℝ)=(10001162273089198851/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63698943887997979/100000000000000000000 : ℝ)+(1162273089198851/20000000000000000000 : ℝ) ≤ ((36523061320692088779/36535000000000000000 : ℝ)+(283840203529/146140000000000 : ℝ)*((16453/100000 : ℝ)+(4573/50000 : ℝ)))^(8351/2048 : ℝ) := by
    rw [show (36523061320692088779/36535000000000000000 : ℝ)+(283840203529/146140000000000 : ℝ)*((16453/100000 : ℝ)+(4573/50000 : ℝ))=(10001704224474459/10000000000000000 : ℝ) by norm_num, show 1+(63698943887997979/100000000000000000000 : ℝ)+(1162273089198851/20000000000000000000 : ℝ)=(50034755154666996117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63698943887997979/100000000000000000000 : ℝ) ≤ ((36523061320692088779/36535000000000000000 : ℝ)+2*(283840203529/146140000000000 : ℝ)*(16453/100000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (36523061320692088779/36535000000000000000 : ℝ)+2*(283840203529/146140000000000 : ℝ)*(16453/100000 : ℝ)=(1250390428186513/1250000000000000 : ℝ) by norm_num, show 1+2*(63698943887997979/100000000000000000000 : ℝ)=(50063698943887997979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36523061320692088779/36535000000000000000 : ℝ)*(X 1 0+X 2 0)+(283840203529/146140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (4573/50000 : ℝ)) (hi := (16453/100000 : ℝ)) (c := (36523061320692088779/36535000000000000000 : ℝ)) (alpha := (283840203529/146140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36523061320692088779/36535000000000000000 : ℝ)*(X 0 1+X 2 1)+(283840203529/146140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (4573/50000 : ℝ)) (hi := (16453/100000 : ℝ)) (c := (36523061320692088779/36535000000000000000 : ℝ)) (alpha := (283840203529/146140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36523061320692088779/36535000000000000000 : ℝ)*(X 0 2+X 1 2)+(283840203529/146140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (4573/50000 : ℝ)) (hi := (16453/100000 : ℝ)) (c := (36523061320692088779/36535000000000000000 : ℝ)) (alpha := (283840203529/146140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2155161491/10000000000 : ℝ)*X 0 0+(678432521/1250000000 : ℝ)*X 0 1+(1046729469/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338347789/2500000000 : ℝ)*X 1 0+(-450839171/2000000000 : ℝ)*X 1 1+(1046729431/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338347809/2500000000 : ℝ)*X 2 0+(5233647189/10000000000 : ℝ)*X 2 1+(-281774463/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360131731/10000000000 : ℝ)*X 0 0+(521367889/1250000000 : ℝ)*X 0 1+(2278907393/5000000000 : ℝ)*X 0 2+(4360131731/10000000000 : ℝ)*X 1 0+(521367889/1250000000 : ℝ)*X 1 1+(2278907393/5000000000 : ℝ)*X 1 2+(4360131731/10000000000 : ℝ)*X 2 0+(521367889/1250000000 : ℝ)*X 2 1+(2278907393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1077589371/5000000000 : ℝ)*X 0 0+(5234390527/10000000000 : ℝ)*X 0 1+(5426712901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663028591/1250000000 : ℝ)*X 1 0+(-2061130597/10000000000 : ℝ)*X 1 1+(2713356357/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212169181/400000000 : ℝ)*X 2 0+(1356678021/2500000000 : ℝ)*X 2 1+(-257641297/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872033193/2000000000 : ℝ)*X 0 0+(2278165709/5000000000 : ℝ)*X 0 1+(4172434949/10000000000 : ℝ)*X 0 2+(872033193/2000000000 : ℝ)*X 1 0+(2278165709/5000000000 : ℝ)*X 1 1+(4172434949/10000000000 : ℝ)*X 1 2+(872033193/2000000000 : ℝ)*X 2 0+(2278165709/5000000000 : ℝ)*X 2 1+(4172434949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1836454749520832377247721579/913375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (711739003/100000000000000 : ℝ)*(base19) + (704733073/100000000000000 : ℝ)*(base23) + (45361999/100000000000000 : ℝ)*(lower2) + (11018641/10000000000000 : ℝ)*(upper5) + (3872241723578933/100000000000000 : ℝ)*(major0) + (3872241723578933/100000000000000 : ℝ)*(major1) + (3872241723578933/100000000000000 : ℝ)*(major2) + (5159624773142303/100000000000000 : ℝ)*(sp0) + (644954569365247/12500000000000 : ℝ)*(sp1) + (2579818314969259/50000000000000 : ℝ)*(sp2) + (2584841679743617/100000000000000 : ℝ)*(sp3) + (1570191161/12500000000000 : ℝ)*(sp4) + (17002653/25000000000000 : ℝ)*(sp5) + (4365721809/100000000000000 : ℝ)*(sp7) + (2584846045465427/100000000000000 : ℝ)*(f.failure) + (5159637334671591/100000000000000 : ℝ)*(f.sum) + (3117073816261/1826750000000000000000000000 : ℝ)*base66 + (51355270134678342807/3653500000000000000000000000000000 : ℝ)*base67 + (41697788059948342807/3653500000000000000000000000000000 : ℝ)*base69 + (5835137582974657193/3653500000000000000000000000000000 : ℝ)*base72 + (55521044029003/7307000000000000000000000000 : ℝ)*base73 + (45772831721410842807/3653500000000000000000000000000000 : ℝ)*base75 + (27366692324029342807/3653500000000000000000000000000000 : ℝ)*base77 + (78738310279601342807/3653500000000000000000000000000000 : ℝ)*base79 + (302176033113/91337500000000000000000000 : ℝ)*base81 + (42706489/10000000000000000000000 : ℝ)*base89 + (42706489/10000000000000000000000 : ℝ)*base91 + (42706489/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68541949883357056252860723/11417187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (966162721/100000000000000 : ℝ)*(base19) + (468646741/25000000000000 : ℝ)*(base23) + (73881431/100000000000000 : ℝ)*(upper3) + (4392281/20000000000000 : ℝ)*(lower4) + (27687631/25000000000000 : ℝ)*(upper5) + (12194501719501/312500000000 : ℝ)*(major0) + (12194501719501/312500000000 : ℝ)*(major1) + (12194501719501/312500000000 : ℝ)*(major2) + (2804641491/20000000000000 : ℝ)*(sp1) + (23274279863/100000000000000 : ℝ)*(sp2) + (5199609672075039/100000000000000 : ℝ)*(sp4) + (5199594682704863/100000000000000 : ℝ)*(sp5) + (1299896130802053/25000000000000 : ℝ)*(sp6) + (1302435614146121/50000000000000 : ℝ)*(sp7) + (1302435614146121/50000000000000 : ℝ)*(f.failure) + (5199609672075039/100000000000000 : ℝ)*(f.sum) + (365418278423/228343750000000000000000000 : ℝ)*base65 + (262904707223663317/22834375000000000000000000000000 : ℝ)*base68 + (278953370179963317/22834375000000000000000000000000 : ℝ)*base70 + (72584487416818173/5708593750000000000000000000000 : ℝ)*base72 + (213082110121/182675000000000000000000000 : ℝ)*base73 + (104529622381361683/22834375000000000000000000000000 : ℝ)*base75 + (11140658379998149/2854296875000000000000000000000 : ℝ)*base78 + (329648063711582067/22834375000000000000000000000000 : ℝ)*base80 + (2368974023661/3653500000000000000000000000 : ℝ)*base81 + (28488347/5000000000000000000000 : ℝ)*base89 + (28488347/5000000000000000000000 : ℝ)*base91 + (28488347/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1159_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2137/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1159_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1159_s4_0 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-539507519/2500000000 : ℝ)*x 0 + (84392043/156250000 : ℝ)*x 1 + (2629069869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539507519/2500000000 : ℝ)^261 ≤ (1311326050147/10000000000000 : ℝ)^197 := by
    have hnat : (539507519 : ℕ)^261*10000000000000^197 ≤ 1311326050147^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539507519 2500000000 1311326050147 10000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84392043/156250000 : ℝ)^261 ≤ (44215231466097/100000000000000 : ℝ)^197 := by
    have hnat : (84392043 : ℕ)^261*100000000000000^197 ≤ 44215231466097^197*156250000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84392043 156250000 44215231466097 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629069869/5000000000 : ℝ)^261 ≤ (10667877002559/25000000000000 : ℝ)^197 := by
    have hnat : (2629069869 : ℕ)^261*25000000000000^197 ≤ 10667877002559^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629069869 5000000000 10667877002559 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539507519/2500000000 : ℝ), (84392043/156250000 : ℝ), (2629069869/5000000000 : ℝ)] ![(1311326050147/10000000000000 : ℝ), (44215231466097/100000000000000 : ℝ), (10667877002559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539507519/2500000000 : ℝ)|^261 ≤ (1311326050147/10000000000000 : ℝ)^197
        have hw : |(-539507519/2500000000 : ℝ)|=(539507519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84392043/156250000 : ℝ)|^261 ≤ (44215231466097/100000000000000 : ℝ)^197
        have hw : |(84392043/156250000 : ℝ)|=(84392043/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629069869/5000000000 : ℝ)|^261 ≤ (10667877002559/25000000000000 : ℝ)^197
        have hw : |(2629069869/5000000000 : ℝ)|=(2629069869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s4_1 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5346795229/10000000000 : ℝ)*x 0 + (-1115331869/5000000000 : ℝ)*x 1 + (5258139951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346795229/10000000000 : ℝ)^261 ≤ (10906828160257/25000000000000 : ℝ)^197 := by
    have hnat : (5346795229 : ℕ)^261*25000000000000^197 ≤ 10906828160257^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346795229 10000000000 10906828160257 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115331869/5000000000 : ℝ)^261 ≤ (6850588523143/50000000000000 : ℝ)^197 := by
    have hnat : (1115331869 : ℕ)^261*50000000000000^197 ≤ 6850588523143^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115331869 5000000000 6850588523143 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258139951/10000000000 : ℝ)^261 ≤ (10667877575091/25000000000000 : ℝ)^197 := by
    have hnat : (5258139951 : ℕ)^261*25000000000000^197 ≤ 10667877575091^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258139951 10000000000 10667877575091 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346795229/10000000000 : ℝ), (-1115331869/5000000000 : ℝ), (5258139951/10000000000 : ℝ)] ![(10906828160257/25000000000000 : ℝ), (6850588523143/50000000000000 : ℝ), (10667877575091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346795229/10000000000 : ℝ)|^261 ≤ (10906828160257/25000000000000 : ℝ)^197
        have hw : |(5346795229/10000000000 : ℝ)|=(5346795229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115331869/5000000000 : ℝ)|^261 ≤ (6850588523143/50000000000000 : ℝ)^197
        have hw : |(-1115331869/5000000000 : ℝ)|=(1115331869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258139951/10000000000 : ℝ)|^261 ≤ (10667877575091/25000000000000 : ℝ)^197
        have hw : |(5258139951/10000000000 : ℝ)|=(5258139951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s4_2 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1336698811/2500000000 : ℝ)*x 0 + (5258140029/10000000000 : ℝ)*x 1 + (-1115331807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336698811/2500000000 : ℝ)^261 ≤ (43627312803183/100000000000000 : ℝ)^197 := by
    have hnat : (1336698811 : ℕ)^261*100000000000000^197 ≤ 43627312803183^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336698811 2500000000 43627312803183 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258140029/10000000000 : ℝ)^261 ≤ (21335755569501/50000000000000 : ℝ)^197 := by
    have hnat : (5258140029 : ℕ)^261*50000000000000^197 ≤ 21335755569501^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258140029 10000000000 21335755569501 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115331807/5000000000 : ℝ)^261 ≤ (685058801861/5000000000000 : ℝ)^197 := by
    have hnat : (1115331807 : ℕ)^261*5000000000000^197 ≤ 685058801861^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115331807 5000000000 685058801861 5000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336698811/2500000000 : ℝ), (5258140029/10000000000 : ℝ), (-1115331807/5000000000 : ℝ)] ![(43627312803183/100000000000000 : ℝ), (21335755569501/50000000000000 : ℝ), (685058801861/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336698811/2500000000 : ℝ)|^261 ≤ (43627312803183/100000000000000 : ℝ)^197
        have hw : |(1336698811/2500000000 : ℝ)|=(1336698811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258140029/10000000000 : ℝ)|^261 ≤ (21335755569501/50000000000000 : ℝ)^197
        have hw : |(5258140029/10000000000 : ℝ)|=(5258140029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115331807/5000000000 : ℝ)|^261 ≤ (685058801861/5000000000000 : ℝ)^197
        have hw : |(-1115331807/5000000000 : ℝ)|=(1115331807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s4_3 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2180922871/5000000000 : ℝ)*x 0 + (4221484477/10000000000 : ℝ)*x 1 + (4506830193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180922871/5000000000 : ℝ)^261 ≤ (16656313344441/50000000000000 : ℝ)^197 := by
    have hnat : (2180922871 : ℕ)^261*50000000000000^197 ≤ 16656313344441^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180922871 5000000000 16656313344441 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221484477/10000000000 : ℝ)^261 ≤ (31899870158399/100000000000000 : ℝ)^197 := by
    have hnat : (4221484477 : ℕ)^261*100000000000000^197 ≤ 31899870158399^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221484477 10000000000 31899870158399 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4506830193/10000000000 : ℝ)^261 ≤ (17393751570877/50000000000000 : ℝ)^197 := by
    have hnat : (4506830193 : ℕ)^261*50000000000000^197 ≤ 17393751570877^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506830193 10000000000 17393751570877 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180922871/5000000000 : ℝ), (4221484477/10000000000 : ℝ), (4506830193/10000000000 : ℝ)] ![(16656313344441/50000000000000 : ℝ), (31899870158399/100000000000000 : ℝ), (17393751570877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180922871/5000000000 : ℝ)|^261 ≤ (16656313344441/50000000000000 : ℝ)^197
        have hw : |(2180922871/5000000000 : ℝ)|=(2180922871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4221484477/10000000000 : ℝ)|^261 ≤ (31899870158399/100000000000000 : ℝ)^197
        have hw : |(4221484477/10000000000 : ℝ)|=(4221484477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4506830193/10000000000 : ℝ)|^261 ≤ (17393751570877/50000000000000 : ℝ)^197
        have hw : |(4506830193/10000000000 : ℝ)|=(4506830193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s4_4 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079018597/5000000000 : ℝ)*x 0 + (5258544869/10000000000 : ℝ)*x 1 + (5400683843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079018597/5000000000 : ℝ)^261 ≤ (1311331780557/10000000000000 : ℝ)^197 := by
    have hnat : (1079018597 : ℕ)^261*10000000000000^197 ≤ 1311331780557^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079018597 5000000000 1311331780557 10000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258544869/10000000000 : ℝ)^261 ≤ (266724149637/625000000000 : ℝ)^197 := by
    have hnat : (5258544869 : ℕ)^261*625000000000^197 ≤ 266724149637^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258544869 10000000000 266724149637 625000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400683843/10000000000 : ℝ)^261 ≤ (44210818234791/100000000000000 : ℝ)^197 := by
    have hnat : (5400683843 : ℕ)^261*100000000000000^197 ≤ 44210818234791^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400683843 10000000000 44210818234791 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079018597/5000000000 : ℝ), (5258544869/10000000000 : ℝ), (5400683843/10000000000 : ℝ)] ![(1311331780557/10000000000000 : ℝ), (266724149637/625000000000 : ℝ), (44210818234791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079018597/5000000000 : ℝ)|^261 ≤ (1311331780557/10000000000000 : ℝ)^197
        have hw : |(-1079018597/5000000000 : ℝ)|=(1079018597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258544869/10000000000 : ℝ)|^261 ≤ (266724149637/625000000000 : ℝ)^197
        have hw : |(5258544869/10000000000 : ℝ)|=(5258544869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400683843/10000000000 : ℝ)|^261 ≤ (44210818234791/100000000000000 : ℝ)^197
        have hw : |(5400683843/10000000000 : ℝ)|=(5400683843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s4_5 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5310535021/10000000000 : ℝ)*x 0 + (-2088119449/10000000000 : ℝ)*x 1 + (2700341879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310535021/10000000000 : ℝ)^261 ≤ (21617880039193/50000000000000 : ℝ)^197 := by
    have hnat : (5310535021 : ℕ)^261*50000000000000^197 ≤ 21617880039193^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310535021 10000000000 21617880039193 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088119449/10000000000 : ℝ)^261 ≤ (12553422591863/100000000000000 : ℝ)^197 := by
    have hnat : (2088119449 : ℕ)^261*100000000000000^197 ≤ 12553422591863^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088119449 10000000000 12553422591863 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700341879/5000000000 : ℝ)^261 ≤ (44210817312913/100000000000000 : ℝ)^197 := by
    have hnat : (2700341879 : ℕ)^261*100000000000000^197 ≤ 44210817312913^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700341879 5000000000 44210817312913 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310535021/10000000000 : ℝ), (-2088119449/10000000000 : ℝ), (2700341879/5000000000 : ℝ)] ![(21617880039193/50000000000000 : ℝ), (12553422591863/100000000000000 : ℝ), (44210817312913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310535021/10000000000 : ℝ)|^261 ≤ (21617880039193/50000000000000 : ℝ)^197
        have hw : |(5310535021/10000000000 : ℝ)|=(5310535021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088119449/10000000000 : ℝ)|^261 ≤ (12553422591863/100000000000000 : ℝ)^197
        have hw : |(-2088119449/10000000000 : ℝ)|=(2088119449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700341879/5000000000 : ℝ)|^261 ≤ (44210817312913/100000000000000 : ℝ)^197
        have hw : |(2700341879/5000000000 : ℝ)|=(2700341879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s4_6 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5310534827/10000000000 : ℝ)*x 0 + (21096421/39062500 : ℝ)*x 1 + (-2088119687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310534827/10000000000 : ℝ)^261 ≤ (10808939496453/25000000000000 : ℝ)^197 := by
    have hnat : (5310534827 : ℕ)^261*25000000000000^197 ≤ 10808939496453^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310534827 10000000000 10808939496453 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21096421/39062500 : ℝ)^261 ≤ (8842163501627/20000000000000 : ℝ)^197 := by
    have hnat : (21096421 : ℕ)^261*20000000000000^197 ≤ 8842163501627^197*39062500^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21096421 39062500 8842163501627 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088119687/10000000000 : ℝ)^261 ≤ (12553424487513/100000000000000 : ℝ)^197 := by
    have hnat : (2088119687 : ℕ)^261*100000000000000^197 ≤ 12553424487513^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088119687 10000000000 12553424487513 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310534827/10000000000 : ℝ), (21096421/39062500 : ℝ), (-2088119687/10000000000 : ℝ)] ![(10808939496453/25000000000000 : ℝ), (8842163501627/20000000000000 : ℝ), (12553424487513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310534827/10000000000 : ℝ)|^261 ≤ (10808939496453/25000000000000 : ℝ)^197
        have hw : |(5310534827/10000000000 : ℝ)|=(5310534827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21096421/39062500 : ℝ)|^261 ≤ (8842163501627/20000000000000 : ℝ)^197
        have hw : |(21096421/39062500 : ℝ)|=(21096421/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088119687/10000000000 : ℝ)|^261 ≤ (12553424487513/100000000000000 : ℝ)^197
        have hw : |(-2088119687/10000000000 : ℝ)|=(2088119687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s4_7 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2180929631/5000000000 : ℝ)*x 0 + (901204279/2000000000 : ℝ)*x 1 + (4222296931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180929631/5000000000 : ℝ)^261 ≤ (16656381745019/50000000000000 : ℝ)^197 := by
    have hnat : (2180929631 : ℕ)^261*50000000000000^197 ≤ 16656381745019^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180929631 5000000000 16656381745019 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901204279/2000000000 : ℝ)^261 ≤ (8694808055761/25000000000000 : ℝ)^197 := by
    have hnat : (901204279 : ℕ)^261*25000000000000^197 ≤ 8694808055761^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901204279 2000000000 8694808055761 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222296931/10000000000 : ℝ)^261 ≤ (15954002137159/50000000000000 : ℝ)^197 := by
    have hnat : (4222296931 : ℕ)^261*50000000000000^197 ≤ 15954002137159^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222296931 10000000000 15954002137159 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180929631/5000000000 : ℝ), (901204279/2000000000 : ℝ), (4222296931/10000000000 : ℝ)] ![(16656381745019/50000000000000 : ℝ), (8694808055761/25000000000000 : ℝ), (15954002137159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180929631/5000000000 : ℝ)|^261 ≤ (16656381745019/50000000000000 : ℝ)^197
        have hw : |(2180929631/5000000000 : ℝ)|=(2180929631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901204279/2000000000 : ℝ)|^261 ≤ (8694808055761/25000000000000 : ℝ)^197
        have hw : |(901204279/2000000000 : ℝ)|=(901204279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222296931/10000000000 : ℝ)|^261 ≤ (15954002137159/50000000000000 : ℝ)^197
        have hw : |(4222296931/10000000000 : ℝ)|=(4222296931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1159_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2137/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2137/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2137/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2137/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2137/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2137/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2137/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2137/20000 : ℝ) ^ (8351/2048 : ℝ) ≤ (2739273245370379/25000000000000000000 : ℝ) := by
    have hpowers : (2137/20000 : ℝ)^8351 ≤ (2739273245370379/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2137 : ℕ)^8351*25000000000000000000^2048 ≤ 2739273245370379^2048*20000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2137 20000 2739273245370379 25000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2137/20000 : ℝ)) (X := (2739273245370379/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7393/50000 : ℝ) ^ (8351/2048 : ℝ) ≤ (41205267688730827/100000000000000000000 : ℝ) := by
    have hpowers : (7393/50000 : ℝ)^8351 ≤ (41205267688730827/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7393 : ℕ)^8351*100000000000000000000^2048 ≤ 41205267688730827^2048*50000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7393 50000 41205267688730827 100000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7393/50000 : ℝ)) (X := (41205267688730827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502739273245370379/12500000000000000000 : ℝ) ≤ (2500134344814221/2500000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (12502739273245370379/12500000000000000000 : ℝ)^2048 ≤ (2500134344814221/2500000000000000 : ℝ)^8351 := by
      have hnat : (12502739273245370379 : ℕ)^2048*2500000000000000^8351 ≤ 2500134344814221^8351*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502739273245370379 12500000000000000000 2500134344814221 2500000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134344814221/2500000000000000 : ℝ)) (X := (12502739273245370379/12500000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052162360670212343/100000000000000000000 : ℝ) ≤ (5000639489233877/5000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (100052162360670212343/100000000000000000000 : ℝ)^2048 ≤ (5000639489233877/5000000000000000 : ℝ)^8351 := by
      have hnat : (100052162360670212343 : ℕ)^2048*5000000000000000^8351 ≤ 5000639489233877^8351*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052162360670212343 100000000000000000000 5000639489233877 5000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000639489233877/5000000000000000 : ℝ)) (X := (100052162360670212343/100000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50041205267688730827/50000000000000000000 : ℝ) ≤ (312563143052457/312500000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (50041205267688730827/50000000000000000000 : ℝ)^2048 ≤ (312563143052457/312500000000000 : ℝ)^8351 := by
      have hnat : (50041205267688730827 : ℕ)^2048*312500000000000^8351 ≤ 312563143052457^8351*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041205267688730827 50000000000000000000 312563143052457 312500000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312563143052457/312500000000000 : ℝ)) (X := (50041205267688730827/50000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2739273245370379/25000000000000000000 : ℝ) ≤ ((5124544477149523673/5126250000000000000 : ℝ)+2*(74159921087/41010000000000 : ℝ)*(2137/20000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (5124544477149523673/5126250000000000000 : ℝ)+2*(74159921087/41010000000000 : ℝ)*(2137/20000 : ℝ)=(2500134344814221/2500000000000000 : ℝ) by norm_num, show 1+2*(2739273245370379/25000000000000000000 : ℝ)=(12502739273245370379/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41205267688730827/100000000000000000000 : ℝ)+(2739273245370379/25000000000000000000 : ℝ) ≤ ((5124544477149523673/5126250000000000000 : ℝ)+(74159921087/41010000000000 : ℝ)*((7393/50000 : ℝ)+(2137/20000 : ℝ)))^(8351/2048 : ℝ) := by
    rw [show (5124544477149523673/5126250000000000000 : ℝ)+(74159921087/41010000000000 : ℝ)*((7393/50000 : ℝ)+(2137/20000 : ℝ))=(5000639489233877/5000000000000000 : ℝ) by norm_num, show 1+(41205267688730827/100000000000000000000 : ℝ)+(2739273245370379/25000000000000000000 : ℝ)=(100052162360670212343/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41205267688730827/100000000000000000000 : ℝ) ≤ ((5124544477149523673/5126250000000000000 : ℝ)+2*(74159921087/41010000000000 : ℝ)*(7393/50000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (5124544477149523673/5126250000000000000 : ℝ)+2*(74159921087/41010000000000 : ℝ)*(7393/50000 : ℝ)=(312563143052457/312500000000000 : ℝ) by norm_num, show 1+2*(41205267688730827/100000000000000000000 : ℝ)=(50041205267688730827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5124544477149523673/5126250000000000000 : ℝ)*(X 1 0+X 2 0)+(74159921087/41010000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (2137/20000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (5124544477149523673/5126250000000000000 : ℝ)) (alpha := (74159921087/41010000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5124544477149523673/5126250000000000000 : ℝ)*(X 0 1+X 2 1)+(74159921087/41010000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (2137/20000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (5124544477149523673/5126250000000000000 : ℝ)) (alpha := (74159921087/41010000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5124544477149523673/5126250000000000000 : ℝ)*(X 0 2+X 1 2)+(74159921087/41010000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (2137/20000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (5124544477149523673/5126250000000000000 : ℝ)) (alpha := (74159921087/41010000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-539507519/2500000000 : ℝ)*X 0 0+(84392043/156250000 : ℝ)*X 0 1+(2629069869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346795229/10000000000 : ℝ)*X 1 0+(-1115331869/5000000000 : ℝ)*X 1 1+(5258139951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336698811/2500000000 : ℝ)*X 2 0+(5258140029/10000000000 : ℝ)*X 2 1+(-1115331807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180922871/5000000000 : ℝ)*X 0 0+(4221484477/10000000000 : ℝ)*X 0 1+(4506830193/10000000000 : ℝ)*X 0 2+(2180922871/5000000000 : ℝ)*X 1 0+(4221484477/10000000000 : ℝ)*X 1 1+(4506830193/10000000000 : ℝ)*X 1 2+(2180922871/5000000000 : ℝ)*X 2 0+(4221484477/10000000000 : ℝ)*X 2 1+(4506830193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079018597/5000000000 : ℝ)*X 0 0+(5258544869/10000000000 : ℝ)*X 0 1+(5400683843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310535021/10000000000 : ℝ)*X 1 0+(-2088119449/10000000000 : ℝ)*X 1 1+(2700341879/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310534827/10000000000 : ℝ)*X 2 0+(21096421/39062500 : ℝ)*X 2 1+(-2088119687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180929631/5000000000 : ℝ)*X 0 0+(901204279/2000000000 : ℝ)*X 0 1+(4222296931/10000000000 : ℝ)*X 0 2+(2180929631/5000000000 : ℝ)*X 1 0+(901204279/2000000000 : ℝ)*X 1 1+(4222296931/10000000000 : ℝ)*X 1 2+(2180929631/5000000000 : ℝ)*X 2 0+(901204279/2000000000 : ℝ)*X 2 1+(4222296931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (765982381856379344836055007/85437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (881892739/50000000000000 : ℝ)*(base19) + (1504498329/100000000000000 : ℝ)*(base23) + (74564391/50000000000000 : ℝ)*(lower2) + (248009483/100000000000000 : ℝ)*(upper3) + (110189507/50000000000000 : ℝ)*(upper5) + (5250036028720341/100000000000000 : ℝ)*(major0) + (5250036028720341/100000000000000 : ℝ)*(major1) + (5250036028720341/100000000000000 : ℝ)*(major2) + (874431489748879/12500000000000 : ℝ)*(sp0) + (6995501882555527/100000000000000 : ℝ)*(sp1) + (6995502141842677/100000000000000 : ℝ)*(sp2) + (1752271700333911/50000000000000 : ℝ)*(sp3) + (25864174987/50000000000000 : ℝ)*(sp4) + (24711584781/100000000000000 : ℝ)*(sp7) + (876142028063151/25000000000000 : ℝ)*(f.failure) + (1399100729268201/20000000000000 : ℝ)*(f.sum) + (444551508737/85437500000000000000000000 : ℝ)*base65 + (394300609488210831/170875000000000000000000000000000 : ℝ)*base67 + (2171105297678289169/170875000000000000000000000000000 : ℝ)*base70 + (1996889702189460831/170875000000000000000000000000000 : ℝ)*base71 + (1558623488543/1367000000000000000000000000 : ℝ)*base74 + (498567188847585831/170875000000000000000000000000000 : ℝ)*base75 + (512217059772585831/170875000000000000000000000000000 : ℝ)*base77 + (81773914114414169/170875000000000000000000000000000 : ℝ)*base80 + (399511637643/273400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (38572557/2500000000000000000000 : ℝ)*base89 + (38572557/2500000000000000000000 : ℝ)*base91 + (38572557/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (389922727499176419700490517/42718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2726505207/100000000000000 : ℝ)*(base19) + (1266428699/50000000000000 : ℝ)*(base23) + (45908183/50000000000000 : ℝ)*(upper2) + (139523863/100000000000000 : ℝ)*(upper3) + (163342349/50000000000000 : ℝ)*(upper5) + (2639977809141779/50000000000000 : ℝ)*(major0) + (2639977809141779/50000000000000 : ℝ)*(major1) + (2639977809141779/50000000000000 : ℝ)*(major2) + (73989987941/100000000000000 : ℝ)*(sp1) + (57947943891/100000000000000 : ℝ)*(sp2) + (1758842632636653/25000000000000 : ℝ)*(sp4) + (1407058762810693/20000000000000 : ℝ)*(sp5) + (7035310049745323/100000000000000 : ℝ)*(sp6) + (140981616070591/4000000000000 : ℝ)*(sp7) + (140981616070591/4000000000000 : ℝ)*(f.failure) + (1758842632636653/25000000000000 : ℝ)*(f.sum) + (2162532854557/410100000000000000000000000 : ℝ)*base65 + (354230215381784411/85437500000000000000000000000000 : ℝ)*base68 + (176806524174715589/85437500000000000000000000000000 : ℝ)*base69 + (860740654370346911/85437500000000000000000000000000 : ℝ)*base72 + (548121892201/410100000000000000000000000 : ℝ)*base73 + (26209051530028089/85437500000000000000000000000000 : ℝ)*base75 + (151121323086409411/85437500000000000000000000000000 : ℝ)*base78 + (18730708310096911/85437500000000000000000000000000 : ℝ)*base80 + (8199834685271/2050500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (544637/400000000000000000000 : ℝ)*base89 + (544637/400000000000000000000 : ℝ)*base91 + (544637/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1159_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2137/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1159_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1159_s5_0 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-215863081/1000000000 : ℝ)*x 0 + (1348619013/2500000000 : ℝ)*x 1 + (5264359979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215863081/1000000000 : ℝ)^261 ≤ (3279524245171/25000000000000 : ℝ)^197 := by
    have hnat : (215863081 : ℕ)^261*25000000000000^197 ≤ 3279524245171^197*1000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215863081 1000000000 3279524245171 25000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348619013/2500000000 : ℝ)^261 ≤ (44143503513813/100000000000000 : ℝ)^197 := by
    have hnat : (1348619013 : ℕ)^261*100000000000000^197 ≤ 44143503513813^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348619013 2500000000 44143503513813 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264359979/10000000000 : ℝ)^261 ≤ (42738399486889/100000000000000 : ℝ)^197 := by
    have hnat : (5264359979 : ℕ)^261*100000000000000^197 ≤ 42738399486889^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264359979 10000000000 42738399486889 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215863081/1000000000 : ℝ), (1348619013/2500000000 : ℝ), (5264359979/10000000000 : ℝ)] ![(3279524245171/25000000000000 : ℝ), (44143503513813/100000000000000 : ℝ), (42738399486889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215863081/1000000000 : ℝ)|^261 ≤ (3279524245171/25000000000000 : ℝ)^197
        have hw : |(-215863081/1000000000 : ℝ)|=(215863081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348619013/2500000000 : ℝ)|^261 ≤ (44143503513813/100000000000000 : ℝ)^197
        have hw : |(1348619013/2500000000 : ℝ)|=(1348619013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264359979/10000000000 : ℝ)|^261 ≤ (42738399486889/100000000000000 : ℝ)^197
        have hw : |(5264359979/10000000000 : ℝ)|=(5264359979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s5_1 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5345133559/10000000000 : ℝ)*x 0 + (-88985953/400000000 : ℝ)*x 1 + (1316089967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345133559/10000000000 : ℝ)^261 ≤ (5451168792117/12500000000000 : ℝ)^197 := by
    have hnat : (5345133559 : ℕ)^261*12500000000000^197 ≤ 5451168792117^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345133559 10000000000 5451168792117 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88985953/400000000 : ℝ)^261 ≤ (6826125674621/50000000000000 : ℝ)^197 := by
    have hnat : (88985953 : ℕ)^261*50000000000000^197 ≤ 6826125674621^197*400000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88985953 400000000 6826125674621 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316089967/2500000000 : ℝ)^261 ≤ (5342299786623/12500000000000 : ℝ)^197 := by
    have hnat : (1316089967 : ℕ)^261*12500000000000^197 ≤ 5342299786623^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316089967 2500000000 5342299786623 12500000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345133559/10000000000 : ℝ), (-88985953/400000000 : ℝ), (1316089967/2500000000 : ℝ)] ![(5451168792117/12500000000000 : ℝ), (6826125674621/50000000000000 : ℝ), (5342299786623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345133559/10000000000 : ℝ)|^261 ≤ (5451168792117/12500000000000 : ℝ)^197
        have hw : |(5345133559/10000000000 : ℝ)|=(5345133559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88985953/400000000 : ℝ)|^261 ≤ (6826125674621/50000000000000 : ℝ)^197
        have hw : |(-88985953/400000000 : ℝ)|=(88985953/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316089967/2500000000 : ℝ)|^261 ≤ (5342299786623/12500000000000 : ℝ)^197
        have hw : |(1316089967/2500000000 : ℝ)|=(1316089967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s5_2 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1336283369/2500000000 : ℝ)*x 0 + (65804499/125000000 : ℝ)*x 1 + (-556162217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336283369/2500000000 : ℝ)^261 ≤ (43609349439769/100000000000000 : ℝ)^197 := by
    have hnat : (1336283369 : ℕ)^261*100000000000000^197 ≤ 43609349439769^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336283369 2500000000 43609349439769 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65804499/125000000 : ℝ)^261 ≤ (42738398852291/100000000000000 : ℝ)^197 := by
    have hnat : (65804499 : ℕ)^261*100000000000000^197 ≤ 42738398852291^197*125000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65804499 125000000 42738398852291 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556162217/2500000000 : ℝ)^261 ≤ (6826125849427/50000000000000 : ℝ)^197 := by
    have hnat : (556162217 : ℕ)^261*50000000000000^197 ≤ 6826125849427^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556162217 2500000000 6826125849427 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336283369/2500000000 : ℝ), (65804499/125000000 : ℝ), (-556162217/2500000000 : ℝ)] ![(43609349439769/100000000000000 : ℝ), (42738398852291/100000000000000 : ℝ), (6826125849427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336283369/2500000000 : ℝ)|^261 ≤ (43609349439769/100000000000000 : ℝ)^197
        have hw : |(1336283369/2500000000 : ℝ)|=(1336283369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65804499/125000000 : ℝ)|^261 ≤ (42738398852291/100000000000000 : ℝ)^197
        have hw : |(65804499/125000000 : ℝ)|=(65804499/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556162217/2500000000 : ℝ)|^261 ≤ (6826125849427/50000000000000 : ℝ)^197
        have hw : |(-556162217/2500000000 : ℝ)|=(556162217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s5_3 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4362196031/10000000000 : ℝ)*x 0 + (4234249101/10000000000 : ℝ)*x 1 + (2246987629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362196031/10000000000 : ℝ)^261 ≤ (83290427769/250000000000 : ℝ)^197 := by
    have hnat : (4362196031 : ℕ)^261*250000000000^197 ≤ 83290427769^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362196031 10000000000 83290427769 250000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234249101/10000000000 : ℝ)^261 ≤ (32027725577171/100000000000000 : ℝ)^197 := by
    have hnat : (4234249101 : ℕ)^261*100000000000000^197 ≤ 32027725577171^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234249101 10000000000 32027725577171 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246987629/5000000000 : ℝ)^261 ≤ (34656103301991/100000000000000 : ℝ)^197 := by
    have hnat : (2246987629 : ℕ)^261*100000000000000^197 ≤ 34656103301991^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246987629 5000000000 34656103301991 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362196031/10000000000 : ℝ), (4234249101/10000000000 : ℝ), (2246987629/5000000000 : ℝ)] ![(83290427769/250000000000 : ℝ), (32027725577171/100000000000000 : ℝ), (34656103301991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362196031/10000000000 : ℝ)|^261 ≤ (83290427769/250000000000 : ℝ)^197
        have hw : |(4362196031/10000000000 : ℝ)|=(4362196031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234249101/10000000000 : ℝ)|^261 ≤ (32027725577171/100000000000000 : ℝ)^197
        have hw : |(4234249101/10000000000 : ℝ)|=(4234249101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246987629/5000000000 : ℝ)|^261 ≤ (34656103301991/100000000000000 : ℝ)^197
        have hw : |(2246987629/5000000000 : ℝ)|=(2246987629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s5_4 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158635699/10000000000 : ℝ)*x 0 + (5264696221/10000000000 : ℝ)*x 1 + (5394138829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158635699/10000000000 : ℝ)^261 ≤ (13118136343571/100000000000000 : ℝ)^197 := by
    have hnat : (2158635699 : ℕ)^261*100000000000000^197 ≤ 13118136343571^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158635699 10000000000 13118136343571 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264696221/10000000000 : ℝ)^261 ≤ (4274201611141/10000000000000 : ℝ)^197 := by
    have hnat : (5264696221 : ℕ)^261*10000000000000^197 ≤ 4274201611141^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264696221 10000000000 4274201611141 10000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394138829/10000000000 : ℝ)^261 ≤ (1765593901091/4000000000000 : ℝ)^197 := by
    have hnat : (5394138829 : ℕ)^261*4000000000000^197 ≤ 1765593901091^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394138829 10000000000 1765593901091 4000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158635699/10000000000 : ℝ), (5264696221/10000000000 : ℝ), (5394138829/10000000000 : ℝ)] ![(13118136343571/100000000000000 : ℝ), (4274201611141/10000000000000 : ℝ), (1765593901091/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158635699/10000000000 : ℝ)|^261 ≤ (13118136343571/100000000000000 : ℝ)^197
        have hw : |(-2158635699/10000000000 : ℝ)|=(2158635699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264696221/10000000000 : ℝ)|^261 ≤ (4274201611141/10000000000000 : ℝ)^197
        have hw : |(5264696221/10000000000 : ℝ)|=(5264696221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394138829/10000000000 : ℝ)|^261 ≤ (1765593901091/4000000000000 : ℝ)^197
        have hw : |(5394138829/10000000000 : ℝ)|=(5394138829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s5_5 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1328031877/2500000000 : ℝ)*x 0 + (-2094869203/10000000000 : ℝ)*x 1 + (1078827807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328031877/2500000000 : ℝ)^261 ≤ (43252938218891/100000000000000 : ℝ)^197 := by
    have hnat : (1328031877 : ℕ)^261*100000000000000^197 ≤ 43252938218891^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328031877 2500000000 43252938218891 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094869203/10000000000 : ℝ)^261 ≤ (39397537531/312500000000 : ℝ)^197 := by
    have hnat : (2094869203 : ℕ)^261*312500000000^197 ≤ 39397537531^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094869203 10000000000 39397537531 312500000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078827807/2000000000 : ℝ)^261 ≤ (44139849760591/100000000000000 : ℝ)^197 := by
    have hnat : (1078827807 : ℕ)^261*100000000000000^197 ≤ 44139849760591^197*2000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078827807 2000000000 44139849760591 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328031877/2500000000 : ℝ), (-2094869203/10000000000 : ℝ), (1078827807/2000000000 : ℝ)] ![(43252938218891/100000000000000 : ℝ), (39397537531/312500000000 : ℝ), (44139849760591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328031877/2500000000 : ℝ)|^261 ≤ (43252938218891/100000000000000 : ℝ)^197
        have hw : |(1328031877/2500000000 : ℝ)|=(1328031877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094869203/10000000000 : ℝ)|^261 ≤ (39397537531/312500000000 : ℝ)^197
        have hw : |(-2094869203/10000000000 : ℝ)|=(2094869203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078827807/2000000000 : ℝ)|^261 ≤ (44139849760591/100000000000000 : ℝ)^197
        have hw : |(1078827807/2000000000 : ℝ)|=(1078827807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s5_6 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2656063543/5000000000 : ℝ)*x 0 + (5394139371/10000000000 : ℝ)*x 1 + (-523717329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656063543/5000000000 : ℝ)^261 ≤ (43252933666559/100000000000000 : ℝ)^197 := by
    have hnat : (2656063543 : ℕ)^261*100000000000000^197 ≤ 43252933666559^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656063543 5000000000 43252933666559 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394139371/10000000000 : ℝ)^261 ≤ (22069926701641/50000000000000 : ℝ)^197 := by
    have hnat : (5394139371 : ℕ)^261*50000000000000^197 ≤ 22069926701641^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394139371 10000000000 22069926701641 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523717329/2500000000 : ℝ)^261 ≤ (12607212910899/100000000000000 : ℝ)^197 := by
    have hnat : (523717329 : ℕ)^261*100000000000000^197 ≤ 12607212910899^197*2500000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523717329 2500000000 12607212910899 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656063543/5000000000 : ℝ), (5394139371/10000000000 : ℝ), (-523717329/2500000000 : ℝ)] ![(43252933666559/100000000000000 : ℝ), (22069926701641/50000000000000 : ℝ), (12607212910899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656063543/5000000000 : ℝ)|^261 ≤ (43252933666559/100000000000000 : ℝ)^197
        have hw : |(2656063543/5000000000 : ℝ)|=(2656063543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394139371/10000000000 : ℝ)|^261 ≤ (22069926701641/50000000000000 : ℝ)^197
        have hw : |(5394139371/10000000000 : ℝ)|=(5394139371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-523717329/2500000000 : ℝ)|^261 ≤ (12607212910899/100000000000000 : ℝ)^197
        have hw : |(-523717329/2500000000 : ℝ)|=(523717329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1159_s5_7 (p : ℝ) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2181103471/5000000000 : ℝ)*x 0 + (4493304607/10000000000 : ℝ)*x 1 + (4234921797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181103471/5000000000 : ℝ)^261 ≤ (6663256302529/20000000000000 : ℝ)^197 := by
    have hnat : (2181103471 : ℕ)^261*20000000000000^197 ≤ 6663256302529^197*5000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181103471 5000000000 6663256302529 20000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493304607/10000000000 : ℝ)^261 ≤ (34649251427773/100000000000000 : ℝ)^197 := by
    have hnat : (4493304607 : ℕ)^261*100000000000000^197 ≤ 34649251427773^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493304607 10000000000 34649251427773 100000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234921797/10000000000 : ℝ)^261 ≤ (16017233519099/50000000000000 : ℝ)^197 := by
    have hnat : (4234921797 : ℕ)^261*50000000000000^197 ≤ 16017233519099^197*10000000000^261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234921797 10000000000 16017233519099 50000000000000 261 197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (261/64 : ℝ)) 261 197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181103471/5000000000 : ℝ), (4493304607/10000000000 : ℝ), (4234921797/10000000000 : ℝ)] ![(6663256302529/20000000000000 : ℝ), (34649251427773/100000000000000 : ℝ), (16017233519099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181103471/5000000000 : ℝ)|^261 ≤ (6663256302529/20000000000000 : ℝ)^197
        have hw : |(2181103471/5000000000 : ℝ)|=(2181103471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493304607/10000000000 : ℝ)|^261 ≤ (34649251427773/100000000000000 : ℝ)^197
        have hw : |(4493304607/10000000000 : ℝ)|=(4493304607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234921797/10000000000 : ℝ)|^261 ≤ (16017233519099/50000000000000 : ℝ)^197
        have hw : |(4234921797/10000000000 : ℝ)|=(4234921797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1159_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (567/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (881/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11207/100000 : ℝ) ^ (8351/2048 : ℝ) ≤ (13309537414826449/100000000000000000000 : ℝ) := by
    have hpowers : (11207/100000 : ℝ)^8351 ≤ (13309537414826449/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11207 : ℕ)^8351*100000000000000000000^2048 ≤ 13309537414826449^2048*100000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11207 100000 13309537414826449 100000000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11207/100000 : ℝ)) (X := (13309537414826449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8351/2048 : ℝ) ≤ (1102933580653513/3125000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8351 ≤ (1102933580653513/3125000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8351*3125000000000000000^2048 ≤ 1102933580653513^2048*20000^8351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 1102933580653513 3125000000000000000 8351 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (1102933580653513/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013309537414826449/50000000000000000000 : ℝ) ≤ (10000652740865879/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (50013309537414826449/50000000000000000000 : ℝ)^2048 ≤ (10000652740865879/10000000000000000 : ℝ)^8351 := by
      have hnat : (50013309537414826449 : ℕ)^2048*10000000000000000^8351 ≤ 10000652740865879^8351*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013309537414826449 50000000000000000000 10000652740865879 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000652740865879/10000000000000000 : ℝ)) (X := (50013309537414826449/50000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009720682399147773/20000000000000000000 : ℝ) ≤ (5000595865976617/5000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (20009720682399147773/20000000000000000000 : ℝ)^2048 ≤ (5000595865976617/5000000000000000 : ℝ)^8351 := by
      have hnat : (20009720682399147773 : ℕ)^2048*5000000000000000^8351 ≤ 5000595865976617^8351*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009720682399147773 20000000000000000000 5000595865976617 5000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000595865976617/5000000000000000 : ℝ)) (X := (20009720682399147773/20000000000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563602933580653513/1562500000000000000 : ℝ) ≤ (10001730723040589/10000000000000000 : ℝ) ^ (8351/2048 : ℝ) := by
    have hpowers : (1563602933580653513/1562500000000000000 : ℝ)^2048 ≤ (10001730723040589/10000000000000000 : ℝ)^8351 := by
      have hnat : (1563602933580653513 : ℕ)^2048*10000000000000000^8351 ≤ 10001730723040589^8351*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563602933580653513 1562500000000000000 10001730723040589 10000000000000000 2048 8351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001730723040589/10000000000000000 : ℝ)) (X := (1563602933580653513/1562500000000000000 : ℝ)) (by norm_num) 8351 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13309537414826449/100000000000000000000 : ℝ) ≤ ((15134947776554953321/15140000000000000000 : ℝ)+2*(107798217471/60560000000000 : ℝ)*(11207/100000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (15134947776554953321/15140000000000000000 : ℝ)+2*(107798217471/60560000000000 : ℝ)*(11207/100000 : ℝ)=(10000652740865879/10000000000000000 : ℝ) by norm_num, show 1+2*(13309537414826449/100000000000000000000 : ℝ)=(50013309537414826449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1102933580653513/3125000000000000000 : ℝ)+(13309537414826449/100000000000000000000 : ℝ) ≤ ((15134947776554953321/15140000000000000000 : ℝ)+(107798217471/60560000000000 : ℝ)*((2847/20000 : ℝ)+(11207/100000 : ℝ)))^(8351/2048 : ℝ) := by
    rw [show (15134947776554953321/15140000000000000000 : ℝ)+(107798217471/60560000000000 : ℝ)*((2847/20000 : ℝ)+(11207/100000 : ℝ))=(5000595865976617/5000000000000000 : ℝ) by norm_num, show 1+(1102933580653513/3125000000000000000 : ℝ)+(13309537414826449/100000000000000000000 : ℝ)=(20009720682399147773/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1102933580653513/3125000000000000000 : ℝ) ≤ ((15134947776554953321/15140000000000000000 : ℝ)+2*(107798217471/60560000000000 : ℝ)*(2847/20000 : ℝ))^(8351/2048 : ℝ) := by
    rw [show (15134947776554953321/15140000000000000000 : ℝ)+2*(107798217471/60560000000000 : ℝ)*(2847/20000 : ℝ)=(10001730723040589/10000000000000000 : ℝ) by norm_num, show 1+2*(1102933580653513/3125000000000000000 : ℝ)=(1563602933580653513/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15134947776554953321/15140000000000000000 : ℝ)*(X 1 0+X 2 0)+(107798217471/60560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15134947776554953321/15140000000000000000 : ℝ)) (alpha := (107798217471/60560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15134947776554953321/15140000000000000000 : ℝ)*(X 0 1+X 2 1)+(107798217471/60560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15134947776554953321/15140000000000000000 : ℝ)) (alpha := (107798217471/60560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15134947776554953321/15140000000000000000 : ℝ)*(X 0 2+X 1 2)+(107798217471/60560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8351/2048 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15134947776554953321/15140000000000000000 : ℝ)) (alpha := (107798217471/60560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215863081/1000000000 : ℝ)*X 0 0+(1348619013/2500000000 : ℝ)*X 0 1+(5264359979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345133559/10000000000 : ℝ)*X 1 0+(-88985953/400000000 : ℝ)*X 1 1+(1316089967/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336283369/2500000000 : ℝ)*X 2 0+(65804499/125000000 : ℝ)*X 2 1+(-556162217/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362196031/10000000000 : ℝ)*X 0 0+(4234249101/10000000000 : ℝ)*X 0 1+(2246987629/5000000000 : ℝ)*X 0 2+(4362196031/10000000000 : ℝ)*X 1 0+(4234249101/10000000000 : ℝ)*X 1 1+(2246987629/5000000000 : ℝ)*X 1 2+(4362196031/10000000000 : ℝ)*X 2 0+(4234249101/10000000000 : ℝ)*X 2 1+(2246987629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2158635699/10000000000 : ℝ)*X 0 0+(5264696221/10000000000 : ℝ)*X 0 1+(5394138829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328031877/2500000000 : ℝ)*X 1 0+(-2094869203/10000000000 : ℝ)*X 1 1+(1078827807/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656063543/5000000000 : ℝ)*X 2 0+(5394139371/10000000000 : ℝ)*X 2 1+(-523717329/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2181103471/5000000000 : ℝ)*X 0 0+(4493304607/10000000000 : ℝ)*X 0 1+(4234921797/10000000000 : ℝ)*X 0 2+(2181103471/5000000000 : ℝ)*X 1 0+(4493304607/10000000000 : ℝ)*X 1 1+(4234921797/10000000000 : ℝ)*X 1 2+(2181103471/5000000000 : ℝ)*X 2 0+(4493304607/10000000000 : ℝ)*X 2 1+(4234921797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1159_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4772107264280012024368552977/757000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (657203231/100000000000000 : ℝ)*(base19) + (421677457/100000000000000 : ℝ)*(base23) + (175060379/100000000000000 : ℝ)*(upper3) + (62102347/100000000000000 : ℝ)*(upper4) + (1145557/50000000000000 : ℝ)*(upper5) + (5767840252929379/100000000000000 : ℝ)*(major0) + (5767840252929379/100000000000000 : ℝ)*(major1) + (5767840252929379/100000000000000 : ℝ)*(major2) + (1921364317615103/25000000000000 : ℝ)*(sp0) + (3842730266069561/50000000000000 : ℝ)*(sp1) + (1537092153532979/20000000000000 : ℝ)*(sp2) + (3850212379295637/100000000000000 : ℝ)*(sp3) + (195944097/5000000000000 : ℝ)*(sp4) + (420443021/6250000000000 : ℝ)*(sp7) + (962554776595993/25000000000000 : ℝ)*(f.failure) + (480341324333897/6250000000000 : ℝ)*(f.sum) + (822487569903/3028000000000000000000000000 : ℝ)*base66 + (15814893329860232341/1514000000000000000000000000000000 : ℝ)*base68 + (6140842553462232341/1514000000000000000000000000000000 : ℝ)*base70 + (17231938636083767659/1514000000000000000000000000000000 : ℝ)*base71 + (7989246266383/3028000000000000000000000000 : ℝ)*base74 + (47612415773494232341/1514000000000000000000000000000000 : ℝ)*base76 + (17904866485575767659/1514000000000000000000000000000000 : ℝ)*base77 + (39460251971164232341/1514000000000000000000000000000000 : ℝ)*base80 + (31269808851/121120000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9466549/2500000000000000000000 : ℝ)*base90 + (9466549/2500000000000000000000 : ℝ)*base92 + (9466549/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5827032332344033869619713/739257812500000000000000000000 : ℝ) := by norm_num
    linear_combination (624396693/50000000000000 : ℝ)*(base19) + (294698751/20000000000000 : ℝ)*(base23) + (5648343/4000000000000 : ℝ)*(upper3) + (12329469/3125000000000 : ℝ)*(lower4) + (22647733756129/390625000000 : ℝ)*(major0) + (22647733756129/390625000000 : ℝ)*(major1) + (22647733756129/390625000000 : ℝ)*(major2) + (22850805459/50000000000000 : ℝ)*(sp1) + (954719579/1562500000000 : ℝ)*(sp2) + (2186323407/50000000000000 : ℝ)*(sp3) + (3862703986591911/50000000000000 : ℝ)*(sp4) + (3862680511389759/50000000000000 : ℝ)*(sp5) + (772534539763701/10000000000000 : ℝ)*(sp6) + (483778384320619/12500000000000 : ℝ)*(sp7) + (1935115723605883/50000000000000 : ℝ)*(f.failure) + (3862703986591911/50000000000000 : ℝ)*(f.sum) + (165251182687/94625000000000000000000000 : ℝ)*base65 + (25609366969001841/5914062500000000000000000000000 : ℝ)*base68 + (375293067524299/369628906250000000000000000000 : ℝ)*base69 + (36087992506873159/5914062500000000000000000000000 : ℝ)*base71 + (631609613029/378500000000000000000000000 : ℝ)*base73 + (17422755981727483/2957031250000000000000000000000 : ℝ)*base76 + (19869216824571233/2957031250000000000000000000000 : ℝ)*base78 + (6127851132876841/5914062500000000000000000000000 : ℝ)*base80 + (82647336833/37850000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (29002319/5000000000000000000000 : ℝ)*base90 + (29002319/5000000000000000000000 : ℝ)*base92 + (29002319/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1159_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1159_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1159_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1159_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1159_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1159_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8351/2048 : ℝ) ≤ p) (hpb : p ≤ (261/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149805507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16453/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1159_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

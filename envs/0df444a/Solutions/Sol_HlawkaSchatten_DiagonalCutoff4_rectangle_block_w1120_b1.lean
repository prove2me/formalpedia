-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:58.96064+00:00
-- url     : https://prove2.me/submissions/dbeab87c-7fa7-427f-a740-fde1330e8434

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
theorem support_rectangle_w1120_s3_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-271675031/1250000000 : ℝ)*x 0 + (5431493559/10000000000 : ℝ)*x 1 + (5229963839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271675031/1250000000 : ℝ)^8313 ≤ (3299086543123/25000000000000 : ℝ)^6265 := by
    have hnat : (271675031 : ℕ)^8313*25000000000000^6265 ≤ 3299086543123^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271675031 1250000000 3299086543123 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431493559/10000000000 : ℝ)^8313 ≤ (11122581389863/25000000000000 : ℝ)^6265 := by
    have hnat : (5431493559 : ℕ)^8313*25000000000000^6265 ≤ 11122581389863^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431493559 10000000000 11122581389863 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229963839/10000000000 : ℝ)^8313 ≤ (8462665650939/20000000000000 : ℝ)^6265 := by
    have hnat : (5229963839 : ℕ)^8313*20000000000000^6265 ≤ 8462665650939^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229963839 10000000000 8462665650939 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271675031/1250000000 : ℝ), (5431493559/10000000000 : ℝ), (5229963839/10000000000 : ℝ)] ![(3299086543123/25000000000000 : ℝ), (11122581389863/25000000000000 : ℝ), (8462665650939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271675031/1250000000 : ℝ)|^8313 ≤ (3299086543123/25000000000000 : ℝ)^6265
        have hw : |(-271675031/1250000000 : ℝ)|=(271675031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431493559/10000000000 : ℝ)|^8313 ≤ (11122581389863/25000000000000 : ℝ)^6265
        have hw : |(5431493559/10000000000 : ℝ)|=(5431493559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229963839/10000000000 : ℝ)|^8313 ≤ (8462665650939/20000000000000 : ℝ)^6265
        have hw : |(5229963839/10000000000 : ℝ)|=(5229963839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s3_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677164881/5000000000 : ℝ)*x 0 + (-142279133/625000000 : ℝ)*x 1 + (2614981899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677164881/5000000000 : ℝ)^8313 ≤ (21826799322749/50000000000000 : ℝ)^6265 := by
    have hnat : (2677164881 : ℕ)^8313*50000000000000^6265 ≤ 21826799322749^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677164881 5000000000 21826799322749 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142279133/625000000 : ℝ)^8313 ≤ (14033073520221/100000000000000 : ℝ)^6265 := by
    have hnat : (142279133 : ℕ)^8313*100000000000000^6265 ≤ 14033073520221^6265*625000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142279133 625000000 14033073520221 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614981899/5000000000 : ℝ)^8313 ≤ (21156663907273/50000000000000 : ℝ)^6265 := by
    have hnat : (2614981899 : ℕ)^8313*50000000000000^6265 ≤ 21156663907273^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614981899 5000000000 21156663907273 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677164881/5000000000 : ℝ), (-142279133/625000000 : ℝ), (2614981899/5000000000 : ℝ)] ![(21826799322749/50000000000000 : ℝ), (14033073520221/100000000000000 : ℝ), (21156663907273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677164881/5000000000 : ℝ)|^8313 ≤ (21826799322749/50000000000000 : ℝ)^6265
        have hw : |(2677164881/5000000000 : ℝ)|=(2677164881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142279133/625000000 : ℝ)|^8313 ≤ (14033073520221/100000000000000 : ℝ)^6265
        have hw : |(-142279133/625000000 : ℝ)|=(142279133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614981899/5000000000 : ℝ)|^8313 ≤ (21156663907273/50000000000000 : ℝ)^6265
        have hw : |(2614981899/5000000000 : ℝ)|=(2614981899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s3_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (535432987/1000000000 : ℝ)*x 0 + (2614981951/5000000000 : ℝ)*x 1 + (-45529317/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535432987/1000000000 : ℝ)^8313 ≤ (8730719962771/20000000000000 : ℝ)^6265 := by
    have hnat : (535432987 : ℕ)^8313*20000000000000^6265 ≤ 8730719962771^6265*1000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535432987 1000000000 8730719962771 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614981951/5000000000 : ℝ)^8313 ≤ (2115666446551/5000000000000 : ℝ)^6265 := by
    have hnat : (2614981951 : ℕ)^8313*5000000000000^6265 ≤ 2115666446551^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614981951 5000000000 2115666446551 5000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45529317/200000000 : ℝ)^8313 ≤ (1754133905789/12500000000000 : ℝ)^6265 := by
    have hnat : (45529317 : ℕ)^8313*12500000000000^6265 ≤ 1754133905789^6265*200000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45529317 200000000 1754133905789 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535432987/1000000000 : ℝ), (2614981951/5000000000 : ℝ), (-45529317/200000000 : ℝ)] ![(8730719962771/20000000000000 : ℝ), (2115666446551/5000000000000 : ℝ), (1754133905789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535432987/1000000000 : ℝ)|^8313 ≤ (8730719962771/20000000000000 : ℝ)^6265
        have hw : |(535432987/1000000000 : ℝ)|=(535432987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614981951/5000000000 : ℝ)|^8313 ≤ (2115666446551/5000000000000 : ℝ)^6265
        have hw : |(2614981951/5000000000 : ℝ)|=(2614981951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45529317/200000000 : ℝ)|^8313 ≤ (1754133905789/12500000000000 : ℝ)^6265
        have hw : |(-45529317/200000000 : ℝ)|=(45529317/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s3_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365378287/10000000000 : ℝ)*x 0 + (2085166019/5000000000 : ℝ)*x 1 + (1142385049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365378287/10000000000 : ℝ)^8313 ≤ (8323130116901/25000000000000 : ℝ)^6265 := by
    have hnat : (4365378287 : ℕ)^8313*25000000000000^6265 ≤ 8323130116901^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365378287 10000000000 8323130116901 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085166019/5000000000 : ℝ)^8313 ≤ (31333300425581/100000000000000 : ℝ)^6265 := by
    have hnat : (2085166019 : ℕ)^8313*100000000000000^6265 ≤ 31333300425581^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085166019 5000000000 31333300425581 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142385049/2500000000 : ℝ)^8313 ≤ (35374179082369/100000000000000 : ℝ)^6265 := by
    have hnat : (1142385049 : ℕ)^8313*100000000000000^6265 ≤ 35374179082369^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142385049 2500000000 35374179082369 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365378287/10000000000 : ℝ), (2085166019/5000000000 : ℝ), (1142385049/2500000000 : ℝ)] ![(8323130116901/25000000000000 : ℝ), (31333300425581/100000000000000 : ℝ), (35374179082369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365378287/10000000000 : ℝ)|^8313 ≤ (8323130116901/25000000000000 : ℝ)^6265
        have hw : |(4365378287/10000000000 : ℝ)|=(4365378287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085166019/5000000000 : ℝ)|^8313 ≤ (31333300425581/100000000000000 : ℝ)^6265
        have hw : |(2085166019/5000000000 : ℝ)|=(2085166019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1142385049/2500000000 : ℝ)|^8313 ≤ (35374179082369/100000000000000 : ℝ)^6265
        have hw : |(1142385049/2500000000 : ℝ)|=(1142385049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s3_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16979839/78125000 : ℝ)*x 0 + (163461193/312500000 : ℝ)*x 1 + (21722779/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16979839/78125000 : ℝ)^8313 ≤ (1319650040787/10000000000000 : ℝ)^6265 := by
    have hnat : (16979839 : ℕ)^8313*10000000000000^6265 ≤ 1319650040787^6265*78125000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16979839 78125000 1319650040787 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163461193/312500000 : ℝ)^8313 ≤ (2116092796621/5000000000000 : ℝ)^6265 := by
    have hnat : (163461193 : ℕ)^8313*5000000000000^6265 ≤ 2116092796621^6265*312500000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163461193 312500000 2116092796621 5000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21722779/40000000 : ℝ)^8313 ≤ (2224082182223/5000000000000 : ℝ)^6265 := by
    have hnat : (21722779 : ℕ)^8313*5000000000000^6265 ≤ 2224082182223^6265*40000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21722779 40000000 2224082182223 5000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16979839/78125000 : ℝ), (163461193/312500000 : ℝ), (21722779/40000000 : ℝ)] ![(1319650040787/10000000000000 : ℝ), (2116092796621/5000000000000 : ℝ), (2224082182223/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16979839/78125000 : ℝ)|^8313 ≤ (1319650040787/10000000000000 : ℝ)^6265
        have hw : |(-16979839/78125000 : ℝ)|=(16979839/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163461193/312500000 : ℝ)|^8313 ≤ (2116092796621/5000000000000 : ℝ)^6265
        have hw : |(163461193/312500000 : ℝ)|=(163461193/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21722779/40000000 : ℝ)|^8313 ≤ (2224082182223/5000000000000 : ℝ)^6265
        have hw : |(21722779/40000000 : ℝ)|=(21722779/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s3_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325838977/2500000000 : ℝ)*x 0 + (-2075735071/10000000000 : ℝ)*x 1 + (5430694873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325838977/2500000000 : ℝ)^8313 ≤ (21551508738007/50000000000000 : ℝ)^6265 := by
    have hnat : (1325838977 : ℕ)^8313*50000000000000^6265 ≤ 21551508738007^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325838977 2500000000 21551508738007 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075735071/10000000000 : ℝ)^8313 ≤ (12415337529513/100000000000000 : ℝ)^6265 := by
    have hnat : (2075735071 : ℕ)^8313*100000000000000^6265 ≤ 12415337529513^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075735071 10000000000 12415337529513 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430694873/10000000000 : ℝ)^8313 ≤ (22240822490631/50000000000000 : ℝ)^6265 := by
    have hnat : (5430694873 : ℕ)^8313*50000000000000^6265 ≤ 22240822490631^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430694873 10000000000 22240822490631 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325838977/2500000000 : ℝ), (-2075735071/10000000000 : ℝ), (5430694873/10000000000 : ℝ)] ![(21551508738007/50000000000000 : ℝ), (12415337529513/100000000000000 : ℝ), (22240822490631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325838977/2500000000 : ℝ)|^8313 ≤ (21551508738007/50000000000000 : ℝ)^6265
        have hw : |(1325838977/2500000000 : ℝ)|=(1325838977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2075735071/10000000000 : ℝ)|^8313 ≤ (12415337529513/100000000000000 : ℝ)^6265
        have hw : |(-2075735071/10000000000 : ℝ)|=(2075735071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430694873/10000000000 : ℝ)|^8313 ≤ (22240822490631/50000000000000 : ℝ)^6265
        have hw : |(5430694873/10000000000 : ℝ)|=(5430694873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s3_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10358117/19531250 : ℝ)*x 0 + (1357673693/2500000000 : ℝ)*x 1 + (-1037867607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10358117/19531250 : ℝ)^8313 ≤ (10775754358219/25000000000000 : ℝ)^6265 := by
    have hnat : (10358117 : ℕ)^8313*25000000000000^6265 ≤ 10775754358219^6265*19531250^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10358117 19531250 10775754358219 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357673693/2500000000 : ℝ)^8313 ≤ (22240821941781/50000000000000 : ℝ)^6265 := by
    have hnat : (1357673693 : ℕ)^8313*50000000000000^6265 ≤ 22240821941781^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357673693 2500000000 22240821941781 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037867607/5000000000 : ℝ)^8313 ≤ (12415338664417/100000000000000 : ℝ)^6265 := by
    have hnat : (1037867607 : ℕ)^8313*100000000000000^6265 ≤ 12415338664417^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037867607 5000000000 12415338664417 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10358117/19531250 : ℝ), (1357673693/2500000000 : ℝ), (-1037867607/5000000000 : ℝ)] ![(10775754358219/25000000000000 : ℝ), (22240821941781/50000000000000 : ℝ), (12415338664417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10358117/19531250 : ℝ)|^8313 ≤ (10775754358219/25000000000000 : ℝ)^6265
        have hw : |(10358117/19531250 : ℝ)|=(10358117/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357673693/2500000000 : ℝ)|^8313 ≤ (22240821941781/50000000000000 : ℝ)^6265
        have hw : |(1357673693/2500000000 : ℝ)|=(1357673693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037867607/5000000000 : ℝ)|^8313 ≤ (12415338664417/100000000000000 : ℝ)^6265
        have hw : |(-1037867607/5000000000 : ℝ)|=(1037867607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s3_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365416191/10000000000 : ℝ)*x 0 + (4567967243/10000000000 : ℝ)*x 1 + (4171914043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365416191/10000000000 : ℝ)^8313 ≤ (33292904039833/100000000000000 : ℝ)^6265 := by
    have hnat : (4365416191 : ℕ)^8313*100000000000000^6265 ≤ 33292904039833^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365416191 10000000000 33292904039833 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4567967243/10000000000 : ℝ)^8313 ≤ (35358022783361/100000000000000 : ℝ)^6265 := by
    have hnat : (4567967243 : ℕ)^8313*100000000000000^6265 ≤ 35358022783361^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567967243 10000000000 35358022783361 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171914043/10000000000 : ℝ)^8313 ≤ (31349073159969/100000000000000 : ℝ)^6265 := by
    have hnat : (4171914043 : ℕ)^8313*100000000000000^6265 ≤ 31349073159969^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171914043 10000000000 31349073159969 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365416191/10000000000 : ℝ), (4567967243/10000000000 : ℝ), (4171914043/10000000000 : ℝ)] ![(33292904039833/100000000000000 : ℝ), (35358022783361/100000000000000 : ℝ), (31349073159969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365416191/10000000000 : ℝ)|^8313 ≤ (33292904039833/100000000000000 : ℝ)^6265
        have hw : |(4365416191/10000000000 : ℝ)|=(4365416191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4567967243/10000000000 : ℝ)|^8313 ≤ (35358022783361/100000000000000 : ℝ)^6265
        have hw : |(4567967243/10000000000 : ℝ)|=(4567967243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171914043/10000000000 : ℝ)|^8313 ≤ (31349073159969/100000000000000 : ℝ)^6265
        have hw : |(4171914043/10000000000 : ℝ)|=(4171914043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16569/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1321/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14833/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16569/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16569/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16569/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16569/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16569/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16569/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8969/100000 : ℝ) ^ (1039/256 : ℝ) ≤ (5618410165891063/100000000000000000000 : ℝ) := by
    have hpowers : (8969/100000 : ℝ)^1039 ≤ (5618410165891063/100000000000000000000 : ℝ)^256 := by
      have hnat : (8969 : ℕ)^1039*100000000000000000000^256 ≤ 5618410165891063^256*100000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8969 100000 5618410165891063 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8969/100000 : ℝ)) (X := (5618410165891063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16569/100000 : ℝ) ^ (1039/256 : ℝ) ≤ (67832970248674669/100000000000000000000 : ℝ) := by
    have hpowers : (16569/100000 : ℝ)^1039 ≤ (67832970248674669/100000000000000000000 : ℝ)^256 := by
      have hnat : (16569 : ℕ)^1039*100000000000000000000^256 ≤ 67832970248674669^256*100000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16569 100000 67832970248674669 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16569/100000 : ℝ)) (X := (67832970248674669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005618410165891063/50000000000000000000 : ℝ) ≤ (10000276853148617/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50005618410165891063/50000000000000000000 : ℝ)^256 ≤ (10000276853148617/10000000000000000 : ℝ)^1039 := by
      have hnat : (50005618410165891063 : ℕ)^256*10000000000000000^1039 ≤ 10000276853148617^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005618410165891063 50000000000000000000 10000276853148617 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000276853148617/10000000000000000 : ℝ)) (X := (50005618410165891063/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25018362845103641433/25000000000000000000 : ℝ) ≤ (10001809273473909/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (25018362845103641433/25000000000000000000 : ℝ)^256 ≤ (10001809273473909/10000000000000000 : ℝ)^1039 := by
      have hnat : (25018362845103641433 : ℕ)^256*10000000000000000^1039 ≤ 10001809273473909^1039*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018362845103641433 25000000000000000000 10001809273473909 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001809273473909/10000000000000000 : ℝ)) (X := (25018362845103641433/25000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50067832970248674669/50000000000000000000 : ℝ) ≤ (10003341693799201/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50067832970248674669/50000000000000000000 : ℝ)^256 ≤ (10003341693799201/10000000000000000 : ℝ)^1039 := by
      have hnat : (50067832970248674669 : ℕ)^256*10000000000000000^1039 ≤ 10003341693799201^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50067832970248674669 50000000000000000000 10003341693799201 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003341693799201/10000000000000000 : ℝ)) (X := (50067832970248674669/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5618410165891063/100000000000000000000 : ℝ) ≤ ((9496826941016800163/9500000000000000000 : ℝ)+2*(383105081323/190000000000000 : ℝ)*(8969/100000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (9496826941016800163/9500000000000000000 : ℝ)+2*(383105081323/190000000000000 : ℝ)*(8969/100000 : ℝ)=(10000276853148617/10000000000000000 : ℝ) by norm_num, show 1+2*(5618410165891063/100000000000000000000 : ℝ)=(50005618410165891063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(67832970248674669/100000000000000000000 : ℝ)+(5618410165891063/100000000000000000000 : ℝ) ≤ ((9496826941016800163/9500000000000000000 : ℝ)+(383105081323/190000000000000 : ℝ)*((16569/100000 : ℝ)+(8969/100000 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (9496826941016800163/9500000000000000000 : ℝ)+(383105081323/190000000000000 : ℝ)*((16569/100000 : ℝ)+(8969/100000 : ℝ))=(10001809273473909/10000000000000000 : ℝ) by norm_num, show 1+(67832970248674669/100000000000000000000 : ℝ)+(5618410165891063/100000000000000000000 : ℝ)=(25018362845103641433/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(67832970248674669/100000000000000000000 : ℝ) ≤ ((9496826941016800163/9500000000000000000 : ℝ)+2*(383105081323/190000000000000 : ℝ)*(16569/100000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (9496826941016800163/9500000000000000000 : ℝ)+2*(383105081323/190000000000000 : ℝ)*(16569/100000 : ℝ)=(10003341693799201/10000000000000000 : ℝ) by norm_num, show 1+2*(67832970248674669/100000000000000000000 : ℝ)=(50067832970248674669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9496826941016800163/9500000000000000000 : ℝ)*(X 1 0+X 2 0)+(383105081323/190000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (8969/100000 : ℝ)) (hi := (16569/100000 : ℝ)) (c := (9496826941016800163/9500000000000000000 : ℝ)) (alpha := (383105081323/190000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9496826941016800163/9500000000000000000 : ℝ)*(X 0 1+X 2 1)+(383105081323/190000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (8969/100000 : ℝ)) (hi := (16569/100000 : ℝ)) (c := (9496826941016800163/9500000000000000000 : ℝ)) (alpha := (383105081323/190000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9496826941016800163/9500000000000000000 : ℝ)*(X 0 2+X 1 2)+(383105081323/190000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (8969/100000 : ℝ)) (hi := (16569/100000 : ℝ)) (c := (9496826941016800163/9500000000000000000 : ℝ)) (alpha := (383105081323/190000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-271675031/1250000000 : ℝ)*X 0 0+(5431493559/10000000000 : ℝ)*X 0 1+(5229963839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677164881/5000000000 : ℝ)*X 1 0+(-142279133/625000000 : ℝ)*X 1 1+(2614981899/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535432987/1000000000 : ℝ)*X 2 0+(2614981951/5000000000 : ℝ)*X 2 1+(-45529317/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365378287/10000000000 : ℝ)*X 0 0+(2085166019/5000000000 : ℝ)*X 0 1+(1142385049/2500000000 : ℝ)*X 0 2+(4365378287/10000000000 : ℝ)*X 1 0+(2085166019/5000000000 : ℝ)*X 1 1+(1142385049/2500000000 : ℝ)*X 1 2+(4365378287/10000000000 : ℝ)*X 2 0+(2085166019/5000000000 : ℝ)*X 2 1+(1142385049/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16979839/78125000 : ℝ)*X 0 0+(163461193/312500000 : ℝ)*X 0 1+(21722779/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325838977/2500000000 : ℝ)*X 1 0+(-2075735071/10000000000 : ℝ)*X 1 1+(5430694873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10358117/19531250 : ℝ)*X 2 0+(1357673693/2500000000 : ℝ)*X 2 1+(-1037867607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365416191/10000000000 : ℝ)*X 0 0+(4567967243/10000000000 : ℝ)*X 0 1+(4171914043/10000000000 : ℝ)*X 0 2+(4365416191/10000000000 : ℝ)*X 1 0+(4567967243/10000000000 : ℝ)*X 1 1+(4171914043/10000000000 : ℝ)*X 1 2+(4365416191/10000000000 : ℝ)*X 2 0+(4567967243/10000000000 : ℝ)*X 2 1+(4171914043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4373723911984959618872097093/475000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2316349869/100000000000000 : ℝ)*(base19) + (2178096601/100000000000000 : ℝ)*(base23) + (31904093/25000000000000 : ℝ)*(lower2) + (1530701/1000000000000 : ℝ)*(upper3) + (69304881/25000000000000 : ℝ)*(upper5) + (3733565710588963/100000000000000 : ℝ)*(major0) + (3733565710588963/100000000000000 : ℝ)*(major1) + (3733565710588963/100000000000000 : ℝ)*(major2) + (1240521612838677/25000000000000 : ℝ)*(sp0) + (1240532635009123/25000000000000 : ℝ)*(sp1) + (4962130678289761/100000000000000 : ℝ)*(sp2) + (626244671871783/25000000000000 : ℝ)*(sp3) + (46405031653/100000000000000 : ℝ)*(sp4) + (4892594107/25000000000000 : ℝ)*(sp7) + (62624956446589/2500000000000 : ℝ)*(f.failure) + (4962132856386361/100000000000000 : ℝ)*(f.sum) + (30254413554049/9500000000000000000000000000 : ℝ)*base65 + (6085207683693149031/950000000000000000000000000000000 : ℝ)*base68 + (14276609414206850969/950000000000000000000000000000000 : ℝ)*base69 + (2146570991106850969/950000000000000000000000000000000 : ℝ)*base71 + (32258189179951/9500000000000000000000000000 : ℝ)*base74 + (8742298102906850969/950000000000000000000000000000000 : ℝ)*base75 + (15298574133406850969/950000000000000000000000000000000 : ℝ)*base77 + (11149977569593149031/950000000000000000000000000000000 : ℝ)*base80 + (56080084191049/9500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1427273/250000000000000000000 : ℝ)*base90 + (1427273/250000000000000000000 : ℝ)*base92 + (1427273/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55429959988899621090257697/6250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1675401649/100000000000000 : ℝ)*(base19) + (383465223/20000000000000 : ℝ)*(base23) + (103061429/50000000000000 : ℝ)*(upper3) + (60530531/50000000000000 : ℝ)*(lower4) + (152293563/100000000000000 : ℝ)*(upper5) + (940811974521129/25000000000000 : ℝ)*(major0) + (940811974521129/25000000000000 : ℝ)*(major1) + (940811974521129/25000000000000 : ℝ)*(major2) + (30933862021/100000000000000 : ℝ)*(sp1) + (8186656587/25000000000000 : ℝ)*(sp2) + (5001582278344767/100000000000000 : ℝ)*(sp4) + (5001549669081097/100000000000000 : ℝ)*(sp5) + (312596725899519/6250000000000 : ℝ)*(sp6) + (1262456611098903/50000000000000 : ℝ)*(sp7) + (1262456611098903/50000000000000 : ℝ)*(f.failure) + (5001582278344767/100000000000000 : ℝ)*(f.sum) + (8267832978917/2375000000000000000000000000 : ℝ)*base65 + (2642317254877505973/237500000000000000000000000000000 : ℝ)*base68 + (362039156152505973/237500000000000000000000000000000 : ℝ)*base70 + (1140980758702505973/237500000000000000000000000000000 : ℝ)*base72 + (4414582511729/1187500000000000000000000000 : ℝ)*base74 + (2124136726040005973/237500000000000000000000000000000 : ℝ)*base76 + (2154663414477505973/237500000000000000000000000000000 : ℝ)*base78 + (713783907977505973/237500000000000000000000000000000 : ℝ)*base80 + (10733022368917/2375000000000000000000000000 : ℝ)*base81 + (35326629/5000000000000000000000 : ℝ)*base89 + (35326629/5000000000000000000000 : ℝ)*base91 + (35326629/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1120_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16569/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14833/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1120_s4_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-272072911/1250000000 : ℝ)*x 0 + (5402974973/10000000000 : ℝ)*x 1 + (657050139/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272072911/1250000000 : ℝ)^8313 ≤ (13221996723693/100000000000000 : ℝ)^6265 := by
    have hnat : (272072911 : ℕ)^8313*100000000000000^6265 ≤ 13221996723693^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272072911 1250000000 13221996723693 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402974973/10000000000 : ℝ)^8313 ≤ (44180628060931/100000000000000 : ℝ)^6265 := by
    have hnat : (5402974973 : ℕ)^8313*100000000000000^6265 ≤ 44180628060931^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402974973 10000000000 44180628060931 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657050139/1250000000 : ℝ)^8313 ≤ (42597375205627/100000000000000 : ℝ)^6265 := by
    have hnat : (657050139 : ℕ)^8313*100000000000000^6265 ≤ 42597375205627^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657050139 1250000000 42597375205627 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272072911/1250000000 : ℝ), (5402974973/10000000000 : ℝ), (657050139/1250000000 : ℝ)] ![(13221996723693/100000000000000 : ℝ), (44180628060931/100000000000000 : ℝ), (42597375205627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272072911/1250000000 : ℝ)|^8313 ≤ (13221996723693/100000000000000 : ℝ)^6265
        have hw : |(-272072911/1250000000 : ℝ)|=(272072911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402974973/10000000000 : ℝ)|^8313 ≤ (44180628060931/100000000000000 : ℝ)^6265
        have hw : |(5402974973/10000000000 : ℝ)|=(5402974973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657050139/1250000000 : ℝ)|^8313 ≤ (42597375205627/100000000000000 : ℝ)^6265
        have hw : |(657050139/1250000000 : ℝ)|=(657050139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s4_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668403017/1250000000 : ℝ)*x 0 + (-2251088837/10000000000 : ℝ)*x 1 + (1314100291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668403017/1250000000 : ℝ)^8313 ≤ (43576745836457/100000000000000 : ℝ)^6265 := by
    have hnat : (668403017 : ℕ)^8313*100000000000000^6265 ≤ 43576745836457^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668403017 1250000000 43576745836457 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251088837/10000000000 : ℝ)^8313 ≤ (3456469597041/25000000000000 : ℝ)^6265 := by
    have hnat : (2251088837 : ℕ)^8313*25000000000000^6265 ≤ 3456469597041^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251088837 10000000000 3456469597041 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314100291/2500000000 : ℝ)^8313 ≤ (8519475152957/20000000000000 : ℝ)^6265 := by
    have hnat : (1314100291 : ℕ)^8313*20000000000000^6265 ≤ 8519475152957^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314100291 2500000000 8519475152957 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668403017/1250000000 : ℝ), (-2251088837/10000000000 : ℝ), (1314100291/2500000000 : ℝ)] ![(43576745836457/100000000000000 : ℝ), (3456469597041/25000000000000 : ℝ), (8519475152957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668403017/1250000000 : ℝ)|^8313 ≤ (43576745836457/100000000000000 : ℝ)^6265
        have hw : |(668403017/1250000000 : ℝ)|=(668403017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2251088837/10000000000 : ℝ)|^8313 ≤ (3456469597041/25000000000000 : ℝ)^6265
        have hw : |(-2251088837/10000000000 : ℝ)|=(2251088837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314100291/2500000000 : ℝ)|^8313 ≤ (8519475152957/20000000000000 : ℝ)^6265
        have hw : |(1314100291/2500000000 : ℝ)|=(1314100291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s4_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347224511/10000000000 : ℝ)*x 0 + (5256400847/10000000000 : ℝ)*x 1 + (-2251088757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347224511/10000000000 : ℝ)^8313 ≤ (4357674989149/10000000000000 : ℝ)^6265 := by
    have hnat : (5347224511 : ℕ)^8313*10000000000000^6265 ≤ 4357674989149^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347224511 10000000000 4357674989149 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256400847/10000000000 : ℝ)^8313 ≤ (42597372356073/100000000000000 : ℝ)^6265 := by
    have hnat : (5256400847 : ℕ)^8313*100000000000000^6265 ≤ 42597372356073^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256400847 10000000000 42597372356073 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251088757/10000000000 : ℝ)^8313 ≤ (3456469434049/25000000000000 : ℝ)^6265 := by
    have hnat : (2251088757 : ℕ)^8313*25000000000000^6265 ≤ 3456469434049^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251088757 10000000000 3456469434049 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347224511/10000000000 : ℝ), (5256400847/10000000000 : ℝ), (-2251088757/10000000000 : ℝ)] ![(4357674989149/10000000000000 : ℝ), (42597372356073/100000000000000 : ℝ), (3456469434049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347224511/10000000000 : ℝ)|^8313 ≤ (4357674989149/10000000000000 : ℝ)^6265
        have hw : |(5347224511/10000000000 : ℝ)|=(5347224511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256400847/10000000000 : ℝ)|^8313 ≤ (42597372356073/100000000000000 : ℝ)^6265
        have hw : |(5256400847/10000000000 : ℝ)|=(5256400847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2251088757/10000000000 : ℝ)|^8313 ≤ (3456469434049/25000000000000 : ℝ)^6265
        have hw : |(-2251088757/10000000000 : ℝ)|=(2251088757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s4_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218363839/500000000 : ℝ)*x 0 + (4224515419/10000000000 : ℝ)*x 1 + (4514863019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218363839/500000000 : ℝ)^8313 ≤ (33311733741047/100000000000000 : ℝ)^6265 := by
    have hnat : (218363839 : ℕ)^8313*100000000000000^6265 ≤ 33311733741047^6265*500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218363839 500000000 33311733741047 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224515419/10000000000 : ℝ)^8313 ≤ (31874623998451/100000000000000 : ℝ)^6265 := by
    have hnat : (4224515419 : ℕ)^8313*100000000000000^6265 ≤ 31874623998451^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224515419 10000000000 31874623998451 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514863019/10000000000 : ℝ)^8313 ≤ (2175852640269/6250000000000 : ℝ)^6265 := by
    have hnat : (4514863019 : ℕ)^8313*6250000000000^6265 ≤ 2175852640269^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514863019 10000000000 2175852640269 6250000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218363839/500000000 : ℝ), (4224515419/10000000000 : ℝ), (4514863019/10000000000 : ℝ)] ![(33311733741047/100000000000000 : ℝ), (31874623998451/100000000000000 : ℝ), (2175852640269/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218363839/500000000 : ℝ)|^8313 ≤ (33311733741047/100000000000000 : ℝ)^6265
        have hw : |(218363839/500000000 : ℝ)|=(218363839/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224515419/10000000000 : ℝ)|^8313 ≤ (31874623998451/100000000000000 : ℝ)^6265
        have hw : |(4224515419/10000000000 : ℝ)|=(4224515419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514863019/10000000000 : ℝ)|^8313 ≤ (2175852640269/6250000000000 : ℝ)^6265
        have hw : |(4514863019/10000000000 : ℝ)|=(4514863019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s4_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-435318229/2000000000 : ℝ)*x 0 + (5256821743/10000000000 : ℝ)*x 1 + (5402552259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435318229/2000000000 : ℝ)^8313 ≤ (2644412010913/20000000000000 : ℝ)^6265 := by
    have hnat : (435318229 : ℕ)^8313*20000000000000^6265 ≤ 2644412010913^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435318229 2000000000 2644412010913 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5256821743/10000000000 : ℝ)^8313 ≤ (42601898324511/100000000000000 : ℝ)^6265 := by
    have hnat : (5256821743 : ℕ)^8313*100000000000000^6265 ≤ 42601898324511^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256821743 10000000000 42601898324511 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402552259/10000000000 : ℝ)^8313 ≤ (44176041610411/100000000000000 : ℝ)^6265 := by
    have hnat : (5402552259 : ℕ)^8313*100000000000000^6265 ≤ 44176041610411^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402552259 10000000000 44176041610411 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435318229/2000000000 : ℝ), (5256821743/10000000000 : ℝ), (5402552259/10000000000 : ℝ)] ![(2644412010913/20000000000000 : ℝ), (42601898324511/100000000000000 : ℝ), (44176041610411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435318229/2000000000 : ℝ)|^8313 ≤ (2644412010913/20000000000000 : ℝ)^6265
        have hw : |(-435318229/2000000000 : ℝ)|=(435318229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5256821743/10000000000 : ℝ)|^8313 ≤ (42601898324511/100000000000000 : ℝ)^6265
        have hw : |(5256821743/10000000000 : ℝ)|=(5256821743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402552259/10000000000 : ℝ)|^8313 ≤ (44176041610411/100000000000000 : ℝ)^6265
        have hw : |(5402552259/10000000000 : ℝ)|=(5402552259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s4_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310152237/10000000000 : ℝ)*x 0 + (-263117179/1250000000 : ℝ)*x 1 + (84414881/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310152237/10000000000 : ℝ)^8313 ≤ (1727053070093/4000000000000 : ℝ)^6265 := by
    have hnat : (5310152237 : ℕ)^8313*4000000000000^6265 ≤ 1727053070093^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310152237 10000000000 1727053070093 4000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263117179/1250000000 : ℝ)^8313 ≤ (3161907568631/25000000000000 : ℝ)^6265 := by
    have hnat : (263117179 : ℕ)^8313*25000000000000^6265 ≤ 3161907568631^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263117179 1250000000 3161907568631 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84414881/156250000 : ℝ)^8313 ≤ (8835208593329/20000000000000 : ℝ)^6265 := by
    have hnat : (84414881 : ℕ)^8313*20000000000000^6265 ≤ 8835208593329^6265*156250000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84414881 156250000 8835208593329 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310152237/10000000000 : ℝ), (-263117179/1250000000 : ℝ), (84414881/156250000 : ℝ)] ![(1727053070093/4000000000000 : ℝ), (3161907568631/25000000000000 : ℝ), (8835208593329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310152237/10000000000 : ℝ)|^8313 ≤ (1727053070093/4000000000000 : ℝ)^6265
        have hw : |(5310152237/10000000000 : ℝ)|=(5310152237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263117179/1250000000 : ℝ)|^8313 ≤ (3161907568631/25000000000000 : ℝ)^6265
        have hw : |(-263117179/1250000000 : ℝ)|=(263117179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84414881/156250000 : ℝ)|^8313 ≤ (8835208593329/20000000000000 : ℝ)^6265
        have hw : |(84414881/156250000 : ℝ)|=(84414881/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s4_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310152333/10000000000 : ℝ)*x 0 + (540255249/1000000000 : ℝ)*x 1 + (-2104937157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310152333/10000000000 : ℝ)^8313 ≤ (5397040973507/12500000000000 : ℝ)^6265 := by
    have hnat : (5310152333 : ℕ)^8313*12500000000000^6265 ≤ 5397040973507^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310152333 10000000000 5397040973507 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540255249/1000000000 : ℝ)^8313 ≤ (44176044116731/100000000000000 : ℝ)^6265 := by
    have hnat : (540255249 : ℕ)^8313*100000000000000^6265 ≤ 44176044116731^6265*1000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540255249 1000000000 44176044116731 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104937157/10000000000 : ℝ)^8313 ≤ (6323814041013/50000000000000 : ℝ)^6265 := by
    have hnat : (2104937157 : ℕ)^8313*50000000000000^6265 ≤ 6323814041013^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104937157 10000000000 6323814041013 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310152333/10000000000 : ℝ), (540255249/1000000000 : ℝ), (-2104937157/10000000000 : ℝ)] ![(5397040973507/12500000000000 : ℝ), (44176044116731/100000000000000 : ℝ), (6323814041013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310152333/10000000000 : ℝ)|^8313 ≤ (5397040973507/12500000000000 : ℝ)^6265
        have hw : |(5310152333/10000000000 : ℝ)|=(5310152333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540255249/1000000000 : ℝ)|^8313 ≤ (44176044116731/100000000000000 : ℝ)^6265
        have hw : |(540255249/1000000000 : ℝ)|=(540255249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2104937157/10000000000 : ℝ)|^8313 ≤ (6323814041013/50000000000000 : ℝ)^6265
        have hw : |(-2104937157/10000000000 : ℝ)|=(2104937157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s4_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367291977/10000000000 : ℝ)*x 0 + (4514029097/10000000000 : ℝ)*x 1 + (4225352243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367291977/10000000000 : ℝ)^8313 ≤ (333118875499/1000000000000 : ℝ)^6265 := by
    have hnat : (4367291977 : ℕ)^8313*1000000000000^6265 ≤ 333118875499^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367291977 10000000000 333118875499 1000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514029097/10000000000 : ℝ)^8313 ≤ (34805110184161/100000000000000 : ℝ)^6265 := by
    have hnat : (4514029097 : ℕ)^8313*100000000000000^6265 ≤ 34805110184161^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514029097 10000000000 34805110184161 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225352243/10000000000 : ℝ)^8313 ≤ (6376600448719/20000000000000 : ℝ)^6265 := by
    have hnat : (4225352243 : ℕ)^8313*20000000000000^6265 ≤ 6376600448719^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225352243 10000000000 6376600448719 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367291977/10000000000 : ℝ), (4514029097/10000000000 : ℝ), (4225352243/10000000000 : ℝ)] ![(333118875499/1000000000000 : ℝ), (34805110184161/100000000000000 : ℝ), (6376600448719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367291977/10000000000 : ℝ)|^8313 ≤ (333118875499/1000000000000 : ℝ)^6265
        have hw : |(4367291977/10000000000 : ℝ)|=(4367291977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514029097/10000000000 : ℝ)|^8313 ≤ (34805110184161/100000000000000 : ℝ)^6265
        have hw : |(4514029097/10000000000 : ℝ)|=(4514029097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225352243/10000000000 : ℝ)|^8313 ≤ (6376600448719/20000000000000 : ℝ)^6265
        have hw : |(4225352243/10000000000 : ℝ)|=(4225352243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11133/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14833/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1321/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14833/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1321/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14833/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1321/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14833/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1321/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14833/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1321/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14833/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1321/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1321/12500 : ℝ) ^ (1039/256 : ℝ) ≤ (10934106428115429/100000000000000000000 : ℝ) := by
    have hpowers : (1321/12500 : ℝ)^1039 ≤ (10934106428115429/100000000000000000000 : ℝ)^256 := by
      have hnat : (1321 : ℕ)^1039*100000000000000000000^256 ≤ 10934106428115429^256*12500^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1321 12500 10934106428115429 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1321/12500 : ℝ)) (X := (10934106428115429/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14833/100000 : ℝ) ^ (1039/256 : ℝ) ≤ (21643385267589629/50000000000000000000 : ℝ) := by
    have hpowers : (14833/100000 : ℝ)^1039 ≤ (21643385267589629/50000000000000000000 : ℝ)^256 := by
      have hnat : (14833 : ℕ)^1039*50000000000000000000^256 ≤ 21643385267589629^256*100000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14833 100000 21643385267589629 50000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14833/100000 : ℝ)) (X := (21643385267589629/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010934106428115429/50000000000000000000 : ℝ) ≤ (156258418252603/156250000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50010934106428115429/50000000000000000000 : ℝ)^256 ≤ (156258418252603/156250000000000 : ℝ)^1039 := by
      have hnat : (50010934106428115429 : ℕ)^256*156250000000000^1039 ≤ 156258418252603^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010934106428115429 50000000000000000000 156258418252603 156250000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156258418252603/156250000000000 : ℝ)) (X := (50010934106428115429/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054220876963294687/100000000000000000000 : ℝ) ≤ (10001335679452539/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (100054220876963294687/100000000000000000000 : ℝ)^256 ≤ (10001335679452539/10000000000000000 : ℝ)^1039 := by
      have hnat : (100054220876963294687 : ℕ)^256*10000000000000000^1039 ≤ 10001335679452539^1039*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054220876963294687 100000000000000000000 10001335679452539 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001335679452539/10000000000000000 : ℝ)) (X := (100054220876963294687/100000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25021643385267589629/25000000000000000000 : ℝ) ≤ (5001066295369243/5000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (25021643385267589629/25000000000000000000 : ℝ)^256 ≤ (5001066295369243/5000000000000000 : ℝ)^1039 := by
      have hnat : (25021643385267589629 : ℕ)^256*5000000000000000^1039 ≤ 5001066295369243^1039*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021643385267589629 25000000000000000000 5001066295369243 5000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001066295369243/5000000000000000 : ℝ)) (X := (25021643385267589629/25000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10934106428115429/100000000000000000000 : ℝ) ≤ ((2664715895580671193/2665625000000000000 : ℝ)+2*(796911285947/426500000000000 : ℝ)*(1321/12500 : ℝ))^(1039/256 : ℝ) := by
    rw [show (2664715895580671193/2665625000000000000 : ℝ)+2*(796911285947/426500000000000 : ℝ)*(1321/12500 : ℝ)=(156258418252603/156250000000000 : ℝ) by norm_num, show 1+2*(10934106428115429/100000000000000000000 : ℝ)=(50010934106428115429/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21643385267589629/50000000000000000000 : ℝ)+(10934106428115429/100000000000000000000 : ℝ) ≤ ((2664715895580671193/2665625000000000000 : ℝ)+(796911285947/426500000000000 : ℝ)*((14833/100000 : ℝ)+(1321/12500 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (2664715895580671193/2665625000000000000 : ℝ)+(796911285947/426500000000000 : ℝ)*((14833/100000 : ℝ)+(1321/12500 : ℝ))=(10001335679452539/10000000000000000 : ℝ) by norm_num, show 1+(21643385267589629/50000000000000000000 : ℝ)+(10934106428115429/100000000000000000000 : ℝ)=(100054220876963294687/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21643385267589629/50000000000000000000 : ℝ) ≤ ((2664715895580671193/2665625000000000000 : ℝ)+2*(796911285947/426500000000000 : ℝ)*(14833/100000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (2664715895580671193/2665625000000000000 : ℝ)+2*(796911285947/426500000000000 : ℝ)*(14833/100000 : ℝ)=(5001066295369243/5000000000000000 : ℝ) by norm_num, show 1+2*(21643385267589629/50000000000000000000 : ℝ)=(25021643385267589629/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2664715895580671193/2665625000000000000 : ℝ)*(X 1 0+X 2 0)+(796911285947/426500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (1321/12500 : ℝ)) (hi := (14833/100000 : ℝ)) (c := (2664715895580671193/2665625000000000000 : ℝ)) (alpha := (796911285947/426500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2664715895580671193/2665625000000000000 : ℝ)*(X 0 1+X 2 1)+(796911285947/426500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (1321/12500 : ℝ)) (hi := (14833/100000 : ℝ)) (c := (2664715895580671193/2665625000000000000 : ℝ)) (alpha := (796911285947/426500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2664715895580671193/2665625000000000000 : ℝ)*(X 0 2+X 1 2)+(796911285947/426500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (1321/12500 : ℝ)) (hi := (14833/100000 : ℝ)) (c := (2664715895580671193/2665625000000000000 : ℝ)) (alpha := (796911285947/426500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-272072911/1250000000 : ℝ)*X 0 0+(5402974973/10000000000 : ℝ)*X 0 1+(657050139/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668403017/1250000000 : ℝ)*X 1 0+(-2251088837/10000000000 : ℝ)*X 1 1+(1314100291/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347224511/10000000000 : ℝ)*X 2 0+(5256400847/10000000000 : ℝ)*X 2 1+(-2251088757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218363839/500000000 : ℝ)*X 0 0+(4224515419/10000000000 : ℝ)*X 0 1+(4514863019/10000000000 : ℝ)*X 0 2+(218363839/500000000 : ℝ)*X 1 0+(4224515419/10000000000 : ℝ)*X 1 1+(4514863019/10000000000 : ℝ)*X 1 2+(218363839/500000000 : ℝ)*X 2 0+(4224515419/10000000000 : ℝ)*X 2 1+(4514863019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-435318229/2000000000 : ℝ)*X 0 0+(5256821743/10000000000 : ℝ)*X 0 1+(5402552259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310152237/10000000000 : ℝ)*X 1 0+(-263117179/1250000000 : ℝ)*X 1 1+(84414881/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310152333/10000000000 : ℝ)*X 2 0+(540255249/1000000000 : ℝ)*X 2 1+(-2104937157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367291977/10000000000 : ℝ)*X 0 0+(4514029097/10000000000 : ℝ)*X 0 1+(4225352243/10000000000 : ℝ)*X 0 2+(4367291977/10000000000 : ℝ)*X 1 0+(4514029097/10000000000 : ℝ)*X 1 1+(4225352243/10000000000 : ℝ)*X 1 2+(4367291977/10000000000 : ℝ)*X 2 0+(4514029097/10000000000 : ℝ)*X 2 1+(4225352243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114647772376412779641286857/16660156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (10857471/100000000000000 : ℝ)*(base21) + (139651411/50000000000000 : ℝ)*(lower2) + (17738467/50000000000000 : ℝ)*(upper3) + (39123807/100000000000000 : ℝ)*(lower4) + (63381839/100000000000000 : ℝ)*(upper5) + (641664708122829/12500000000000 : ℝ)*(major0) + (641664708122829/12500000000000 : ℝ)*(major1) + (641664708122829/12500000000000 : ℝ)*(major2) + (6822487386406547/100000000000000 : ℝ)*(sp0) + (6822487386406547/100000000000000 : ℝ)*(sp1) + (1705620446882477/25000000000000 : ℝ)*(sp2) + (3444145761328919/100000000000000 : ℝ)*(sp3) + (174625599/3125000000000 : ℝ)*(sp6) + (976422317/50000000000000 : ℝ)*(sp7) + (215259232135847/6250000000000 : ℝ)*(f.failure) + (6822487386406547/100000000000000 : ℝ)*(f.sum) + (177914693336323/10662500000000000000000000000 : ℝ)*base66 + (46190269060812657/8330078125000000000000000000000 : ℝ)*base68 + (30296607479045619/66640625000000000000000000000000 : ℝ)*base69 + (108883603101433633/2082519531250000000000000000000 : ℝ)*base72 + (1013008468953/666406250000000000000000000 : ℝ)*base74 + (242472829921891881/66640625000000000000000000000000 : ℝ)*base76 + (97708962225922189/16660156250000000000000000000000 : ℝ)*base78 + (959345806919704381/66640625000000000000000000000000 : ℝ)*base80 + (112758164554429/21325000000000000000000000000 : ℝ)*base81 + (6382379/625000000000000000000 : ℝ)*base90 + (6382379/625000000000000000000 : ℝ)*base92 + (6382379/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2221170370164666409064757/208251953125000000000000000000 : ℝ) := by norm_num
    linear_combination (873615489/50000000000000 : ℝ)*(base19) + (1237955013/50000000000000 : ℝ)*(base23) + (422672821/100000000000000 : ℝ)*(upper3) + (220345013/100000000000000 : ℝ)*(lower4) + (85825847/25000000000000 : ℝ)*(upper5) + (516302839251637/10000000000000 : ℝ)*(major0) + (516302839251637/10000000000000 : ℝ)*(major1) + (516302839251637/10000000000000 : ℝ)*(major2) + (31910931099/100000000000000 : ℝ)*(sp1) + (59079238163/100000000000000 : ℝ)*(sp2) + (6861974602348023/100000000000000 : ℝ)*(sp4) + (3430970472092973/50000000000000 : ℝ)*(sp5) + (1372382609439967/20000000000000 : ℝ)*(sp6) + (866020456789643/25000000000000 : ℝ)*(sp7) + (866020456789643/25000000000000 : ℝ)*(f.failure) + (6861974602348023/100000000000000 : ℝ)*(f.sum) + (8761757280407/4265000000000000000000000000 : ℝ)*base66 + (355854161238544559/26656250000000000000000000000000 : ℝ)*base68 + (81666135475830441/26656250000000000000000000000000 : ℝ)*base69 + (374324541746700809/26656250000000000000000000000000 : ℝ)*base72 + (25693280297007/4265000000000000000000000000 : ℝ)*base74 + (128416918501486691/26656250000000000000000000000000 : ℝ)*base75 + (407405259395013309/26656250000000000000000000000000 : ℝ)*base78 + (90765728459357059/26656250000000000000000000000000 : ℝ)*base80 + (1309223494083/266562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (17032449/2500000000000000000000 : ℝ)*base89 + (17032449/2500000000000000000000 : ℝ)*base91 + (17032449/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1120_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14833/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11133/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1120_s5_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177268629/10000000000 : ℝ)*x 0 + (5395500671/10000000000 : ℝ)*x 1 + (8224103/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177268629/10000000000 : ℝ)^8313 ≤ (132275211543/1000000000000 : ℝ)^6265 := by
    have hnat : (2177268629 : ℕ)^8313*1000000000000^6265 ≤ 132275211543^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177268629 10000000000 132275211543 1000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395500671/10000000000 : ℝ)^8313 ≤ (5512443640703/12500000000000 : ℝ)^6265 := by
    have hnat : (5395500671 : ℕ)^8313*12500000000000^6265 ≤ 5512443640703^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395500671 10000000000 5512443640703 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8224103/15625000 : ℝ)^8313 ≤ (42672929704879/100000000000000 : ℝ)^6265 := by
    have hnat : (8224103 : ℕ)^8313*100000000000000^6265 ≤ 42672929704879^6265*15625000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8224103 15625000 42672929704879 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177268629/10000000000 : ℝ), (5395500671/10000000000 : ℝ), (8224103/15625000 : ℝ)] ![(132275211543/1000000000000 : ℝ), (5512443640703/12500000000000 : ℝ), (42672929704879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177268629/10000000000 : ℝ)|^8313 ≤ (132275211543/1000000000000 : ℝ)^6265
        have hw : |(-2177268629/10000000000 : ℝ)|=(2177268629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395500671/10000000000 : ℝ)|^8313 ≤ (5512443640703/12500000000000 : ℝ)^6265
        have hw : |(5395500671/10000000000 : ℝ)|=(5395500671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8224103/15625000 : ℝ)|^8313 ≤ (42672929704879/100000000000000 : ℝ)^6265
        have hw : |(8224103/15625000 : ℝ)|=(8224103/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s5_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345354587/10000000000 : ℝ)*x 0 + (-2244295067/10000000000 : ℝ)*x 1 + (5263425953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345354587/10000000000 : ℝ)^8313 ≤ (680570793303/1562500000000 : ℝ)^6265 := by
    have hnat : (5345354587 : ℕ)^8313*1562500000000^6265 ≤ 680570793303^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345354587 10000000000 680570793303 1562500000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244295067/10000000000 : ℝ)^8313 ≤ (13770539145093/100000000000000 : ℝ)^6265 := by
    have hnat : (2244295067 : ℕ)^8313*100000000000000^6265 ≤ 13770539145093^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244295067 10000000000 13770539145093 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263425953/10000000000 : ℝ)^8313 ≤ (10668232514971/25000000000000 : ℝ)^6265 := by
    have hnat : (5263425953 : ℕ)^8313*25000000000000^6265 ≤ 10668232514971^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263425953 10000000000 10668232514971 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345354587/10000000000 : ℝ), (-2244295067/10000000000 : ℝ), (5263425953/10000000000 : ℝ)] ![(680570793303/1562500000000 : ℝ), (13770539145093/100000000000000 : ℝ), (10668232514971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345354587/10000000000 : ℝ)|^8313 ≤ (680570793303/1562500000000 : ℝ)^6265
        have hw : |(5345354587/10000000000 : ℝ)|=(5345354587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2244295067/10000000000 : ℝ)|^8313 ≤ (13770539145093/100000000000000 : ℝ)^6265
        have hw : |(-2244295067/10000000000 : ℝ)|=(2244295067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263425953/10000000000 : ℝ)|^8313 ≤ (10668232514971/25000000000000 : ℝ)^6265
        have hw : |(5263425953/10000000000 : ℝ)|=(5263425953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s5_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (26726773/50000000 : ℝ)*x 0 + (5263425931/10000000000 : ℝ)*x 1 + (-2244295079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26726773/50000000 : ℝ)^8313 ≤ (43556530911951/100000000000000 : ℝ)^6265 := by
    have hnat : (26726773 : ℕ)^8313*100000000000000^6265 ≤ 43556530911951^6265*50000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26726773 50000000 43556530911951 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263425931/10000000000 : ℝ)^8313 ≤ (21336464911607/50000000000000 : ℝ)^6265 := by
    have hnat : (5263425931 : ℕ)^8313*50000000000000^6265 ≤ 21336464911607^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263425931 10000000000 21336464911607 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244295079/10000000000 : ℝ)^8313 ≤ (1721317405349/12500000000000 : ℝ)^6265 := by
    have hnat : (2244295079 : ℕ)^8313*12500000000000^6265 ≤ 1721317405349^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244295079 10000000000 1721317405349 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26726773/50000000 : ℝ), (5263425931/10000000000 : ℝ), (-2244295079/10000000000 : ℝ)] ![(43556530911951/100000000000000 : ℝ), (21336464911607/50000000000000 : ℝ), (1721317405349/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26726773/50000000 : ℝ)|^8313 ≤ (43556530911951/100000000000000 : ℝ)^6265
        have hw : |(26726773/50000000 : ℝ)|=(26726773/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263425931/10000000000 : ℝ)|^8313 ≤ (21336464911607/50000000000000 : ℝ)^6265
        have hw : |(5263425931/10000000000 : ℝ)|=(5263425931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2244295079/10000000000 : ℝ)|^8313 ≤ (1721317405349/12500000000000 : ℝ)^6265
        have hw : |(-2244295079/10000000000 : ℝ)|=(2244295079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s5_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367677781/10000000000 : ℝ)*x 0 + (4238824063/10000000000 : ℝ)*x 1 + (2250224993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367677781/10000000000 : ℝ)^8313 ≤ (33315792331209/100000000000000 : ℝ)^6265 := by
    have hnat : (4367677781 : ℕ)^8313*100000000000000^6265 ≤ 33315792331209^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367677781 10000000000 33315792331209 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238824063/10000000000 : ℝ)^8313 ≤ (32017956121431/100000000000000 : ℝ)^6265 := by
    have hnat : (4238824063 : ℕ)^8313*100000000000000^6265 ≤ 32017956121431^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238824063 10000000000 32017956121431 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250224993/5000000000 : ℝ)^8313 ≤ (3466625152417/10000000000000 : ℝ)^6265 := by
    have hnat : (2250224993 : ℕ)^8313*10000000000000^6265 ≤ 3466625152417^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250224993 5000000000 3466625152417 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367677781/10000000000 : ℝ), (4238824063/10000000000 : ℝ), (2250224993/5000000000 : ℝ)] ![(33315792331209/100000000000000 : ℝ), (32017956121431/100000000000000 : ℝ), (3466625152417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367677781/10000000000 : ℝ)|^8313 ≤ (33315792331209/100000000000000 : ℝ)^6265
        have hw : |(4367677781/10000000000 : ℝ)|=(4367677781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238824063/10000000000 : ℝ)|^8313 ≤ (32017956121431/100000000000000 : ℝ)^6265
        have hw : |(4238824063/10000000000 : ℝ)|=(4238824063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250224993/5000000000 : ℝ)|^8313 ≤ (3466625152417/10000000000000 : ℝ)^6265
        have hw : |(2250224993/5000000000 : ℝ)|=(2250224993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s5_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177273951/10000000000 : ℝ)*x 0 + (1315941977/2500000000 : ℝ)*x 1 + (134878937/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177273951/10000000000 : ℝ)^8313 ≤ (6613782028183/50000000000000 : ℝ)^6265 := by
    have hnat : (2177273951 : ℕ)^8313*50000000000000^6265 ≤ 6613782028183^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177273951 10000000000 6613782028183 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315941977/2500000000 : ℝ)^8313 ≤ (21338304379303/50000000000000 : ℝ)^6265 := by
    have hnat : (1315941977 : ℕ)^8313*50000000000000^6265 ≤ 21338304379303^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315941977 2500000000 21338304379303 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134878937/250000000 : ℝ)^8313 ≤ (5511978397013/12500000000000 : ℝ)^6265 := by
    have hnat : (134878937 : ℕ)^8313*12500000000000^6265 ≤ 5511978397013^6265*250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134878937 250000000 5511978397013 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177273951/10000000000 : ℝ), (1315941977/2500000000 : ℝ), (134878937/250000000 : ℝ)] ![(6613782028183/50000000000000 : ℝ), (21338304379303/50000000000000 : ℝ), (5511978397013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177273951/10000000000 : ℝ)|^8313 ≤ (6613782028183/50000000000000 : ℝ)^6265
        have hw : |(-2177273951/10000000000 : ℝ)|=(2177273951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315941977/2500000000 : ℝ)|^8313 ≤ (21338304379303/50000000000000 : ℝ)^6265
        have hw : |(1315941977/2500000000 : ℝ)|=(1315941977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134878937/250000000 : ℝ)|^8313 ≤ (5511978397013/12500000000000 : ℝ)^6265
        have hw : |(134878937/250000000 : ℝ)|=(134878937/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s5_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655974127/5000000000 : ℝ)*x 0 + (-528140957/2500000000 : ℝ)*x 1 + (674394669/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655974127/5000000000 : ℝ)^8313 ≤ (43195704793487/100000000000000 : ℝ)^6265 := by
    have hnat : (2655974127 : ℕ)^8313*100000000000000^6265 ≤ 43195704793487^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655974127 5000000000 43195704793487 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528140957/2500000000 : ℝ)^8313 ≤ (6354234697467/50000000000000 : ℝ)^6265 := by
    have hnat : (528140957 : ℕ)^8313*50000000000000^6265 ≤ 6354234697467^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528140957 2500000000 6354234697467 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674394669/1250000000 : ℝ)^8313 ≤ (44095825787943/100000000000000 : ℝ)^6265 := by
    have hnat : (674394669 : ℕ)^8313*100000000000000^6265 ≤ 44095825787943^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674394669 1250000000 44095825787943 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655974127/5000000000 : ℝ), (-528140957/2500000000 : ℝ), (674394669/1250000000 : ℝ)] ![(43195704793487/100000000000000 : ℝ), (6354234697467/50000000000000 : ℝ), (44095825787943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655974127/5000000000 : ℝ)|^8313 ≤ (43195704793487/100000000000000 : ℝ)^6265
        have hw : |(2655974127/5000000000 : ℝ)|=(2655974127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528140957/2500000000 : ℝ)|^8313 ≤ (6354234697467/50000000000000 : ℝ)^6265
        have hw : |(-528140957/2500000000 : ℝ)|=(528140957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674394669/1250000000 : ℝ)|^8313 ≤ (44095825787943/100000000000000 : ℝ)^6265
        have hw : |(674394669/1250000000 : ℝ)|=(674394669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s5_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311948507/10000000000 : ℝ)*x 0 + (26975787/50000000 : ℝ)*x 1 + (-1056281711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311948507/10000000000 : ℝ)^8313 ≤ (4319570752337/10000000000000 : ℝ)^6265 := by
    have hnat : (5311948507 : ℕ)^8313*10000000000000^6265 ≤ 4319570752337^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311948507 10000000000 4319570752337 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26975787/50000000 : ℝ)^8313 ≤ (44095826308503/100000000000000 : ℝ)^6265 := by
    have hnat : (26975787 : ℕ)^8313*100000000000000^6265 ≤ 44095826308503^6265*50000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26975787 50000000 44095826308503 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056281711/5000000000 : ℝ)^8313 ≤ (635423307709/5000000000000 : ℝ)^6265 := by
    have hnat : (1056281711 : ℕ)^8313*5000000000000^6265 ≤ 635423307709^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056281711 5000000000 635423307709 5000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311948507/10000000000 : ℝ), (26975787/50000000 : ℝ), (-1056281711/5000000000 : ℝ)] ![(4319570752337/10000000000000 : ℝ), (44095826308503/100000000000000 : ℝ), (635423307709/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311948507/10000000000 : ℝ)|^8313 ≤ (4319570752337/10000000000000 : ℝ)^6265
        have hw : |(5311948507/10000000000 : ℝ)|=(5311948507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26975787/50000000 : ℝ)|^8313 ≤ (44095826308503/100000000000000 : ℝ)^6265
        have hw : |(26975787/50000000 : ℝ)|=(26975787/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056281711/5000000000 : ℝ)|^8313 ≤ (635423307709/5000000000000 : ℝ)^6265
        have hw : |(-1056281711/5000000000 : ℝ)|=(1056281711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s5_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436768891/1000000000 : ℝ)*x 0 + (1124943137/2500000000 : ℝ)*x 1 + (2119751811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436768891/1000000000 : ℝ)^8313 ≤ (16657952485597/50000000000000 : ℝ)^6265 := by
    have hnat : (436768891 : ℕ)^8313*50000000000000^6265 ≤ 16657952485597^6265*1000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436768891 1000000000 16657952485597 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124943137/2500000000 : ℝ)^8313 ≤ (3465932769223/10000000000000 : ℝ)^6265 := by
    have hnat : (1124943137 : ℕ)^8313*10000000000000^6265 ≤ 3465932769223^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124943137 2500000000 3465932769223 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119751811/5000000000 : ℝ)^8313 ≤ (6404953463767/20000000000000 : ℝ)^6265 := by
    have hnat : (2119751811 : ℕ)^8313*20000000000000^6265 ≤ 6404953463767^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119751811 5000000000 6404953463767 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436768891/1000000000 : ℝ), (1124943137/2500000000 : ℝ), (2119751811/5000000000 : ℝ)] ![(16657952485597/50000000000000 : ℝ), (3465932769223/10000000000000 : ℝ), (6404953463767/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436768891/1000000000 : ℝ)|^8313 ≤ (16657952485597/50000000000000 : ℝ)^6265
        have hw : |(436768891/1000000000 : ℝ)|=(436768891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124943137/2500000000 : ℝ)|^8313 ≤ (3465932769223/10000000000000 : ℝ)^6265
        have hw : |(1124943137/2500000000 : ℝ)|=(1124943137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119751811/5000000000 : ℝ)|^8313 ≤ (6404953463767/20000000000000 : ℝ)^6265
        have hw : |(2119751811/5000000000 : ℝ)|=(2119751811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5641/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (88/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11133/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11133/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11133/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11133/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11133/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11133/100000 : ℝ) ^ (1039/256 : ℝ) ≤ (270157025565821/2000000000000000000 : ℝ) := by
    have hpowers : (11133/100000 : ℝ)^1039 ≤ (270157025565821/2000000000000000000 : ℝ)^256 := by
      have hnat : (11133 : ℕ)^1039*2000000000000000000^256 ≤ 270157025565821^256*100000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11133 100000 270157025565821 2000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11133/100000 : ℝ)) (X := (270157025565821/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (1039/256 : ℝ) ≤ (18324813311064427/50000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^1039 ≤ (18324813311064427/50000000000000000000 : ℝ)^256 := by
      have hnat : (14237 : ℕ)^1039*50000000000000000000^256 ≤ 18324813311064427^256*100000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 18324813311064427 50000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (18324813311064427/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000270157025565821/1000000000000000000 : ℝ) ≤ (2500166393550039/2500000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (1000270157025565821/1000000000000000000 : ℝ)^256 ≤ (2500166393550039/2500000000000000 : ℝ)^1039 := by
      have hnat : (1000270157025565821 : ℕ)^256*2500000000000000^1039 ≤ 2500166393550039^1039*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000270157025565821 1000000000000000000 2500166393550039 2500000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500166393550039/2500000000000000 : ℝ)) (X := (1000270157025565821/1000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563283710592194061/1562500000000000000 : ℝ) ≤ (10001235600412863/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (1563283710592194061/1562500000000000000 : ℝ)^256 ≤ (10001235600412863/10000000000000000 : ℝ)^1039 := by
      have hnat : (1563283710592194061 : ℕ)^256*10000000000000000^1039 ≤ 10001235600412863^1039*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563283710592194061 1562500000000000000 10001235600412863 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001235600412863/10000000000000000 : ℝ)) (X := (1563283710592194061/1562500000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018324813311064427/25000000000000000000 : ℝ) ≤ (1000180562662557/1000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (25018324813311064427/25000000000000000000 : ℝ)^256 ≤ (1000180562662557/1000000000000000 : ℝ)^1039 := by
      have hnat : (25018324813311064427 : ℕ)^256*1000000000000000^1039 ≤ 1000180562662557^1039*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018324813311064427 25000000000000000000 1000180562662557 1000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000180562662557/1000000000000000 : ℝ)) (X := (25018324813311064427/25000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(270157025565821/2000000000000000000 : ℝ) ≤ ((15514686869332575081/15520000000000000000 : ℝ)+2*(570026212707/310400000000000 : ℝ)*(11133/100000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (15514686869332575081/15520000000000000000 : ℝ)+2*(570026212707/310400000000000 : ℝ)*(11133/100000 : ℝ)=(2500166393550039/2500000000000000 : ℝ) by norm_num, show 1+2*(270157025565821/2000000000000000000 : ℝ)=(1000270157025565821/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18324813311064427/50000000000000000000 : ℝ)+(270157025565821/2000000000000000000 : ℝ) ≤ ((15514686869332575081/15520000000000000000 : ℝ)+(570026212707/310400000000000 : ℝ)*((14237/100000 : ℝ)+(11133/100000 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (15514686869332575081/15520000000000000000 : ℝ)+(570026212707/310400000000000 : ℝ)*((14237/100000 : ℝ)+(11133/100000 : ℝ))=(10001235600412863/10000000000000000 : ℝ) by norm_num, show 1+(18324813311064427/50000000000000000000 : ℝ)+(270157025565821/2000000000000000000 : ℝ)=(1563283710592194061/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18324813311064427/50000000000000000000 : ℝ) ≤ ((15514686869332575081/15520000000000000000 : ℝ)+2*(570026212707/310400000000000 : ℝ)*(14237/100000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (15514686869332575081/15520000000000000000 : ℝ)+2*(570026212707/310400000000000 : ℝ)*(14237/100000 : ℝ)=(1000180562662557/1000000000000000 : ℝ) by norm_num, show 1+2*(18324813311064427/50000000000000000000 : ℝ)=(25018324813311064427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15514686869332575081/15520000000000000000 : ℝ)*(X 1 0+X 2 0)+(570026212707/310400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (11133/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (15514686869332575081/15520000000000000000 : ℝ)) (alpha := (570026212707/310400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15514686869332575081/15520000000000000000 : ℝ)*(X 0 1+X 2 1)+(570026212707/310400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (11133/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (15514686869332575081/15520000000000000000 : ℝ)) (alpha := (570026212707/310400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15514686869332575081/15520000000000000000 : ℝ)*(X 0 2+X 1 2)+(570026212707/310400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (11133/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (15514686869332575081/15520000000000000000 : ℝ)) (alpha := (570026212707/310400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2177268629/10000000000 : ℝ)*X 0 0+(5395500671/10000000000 : ℝ)*X 0 1+(8224103/15625000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345354587/10000000000 : ℝ)*X 1 0+(-2244295067/10000000000 : ℝ)*X 1 1+(5263425953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((26726773/50000000 : ℝ)*X 2 0+(5263425931/10000000000 : ℝ)*X 2 1+(-2244295079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367677781/10000000000 : ℝ)*X 0 0+(4238824063/10000000000 : ℝ)*X 0 1+(2250224993/5000000000 : ℝ)*X 0 2+(4367677781/10000000000 : ℝ)*X 1 0+(4238824063/10000000000 : ℝ)*X 1 1+(2250224993/5000000000 : ℝ)*X 1 2+(4367677781/10000000000 : ℝ)*X 2 0+(4238824063/10000000000 : ℝ)*X 2 1+(2250224993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2177273951/10000000000 : ℝ)*X 0 0+(1315941977/2500000000 : ℝ)*X 0 1+(134878937/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655974127/5000000000 : ℝ)*X 1 0+(-528140957/2500000000 : ℝ)*X 1 1+(674394669/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311948507/10000000000 : ℝ)*X 2 0+(26975787/50000000 : ℝ)*X 2 1+(-1056281711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436768891/1000000000 : ℝ)*X 0 0+(1124943137/2500000000 : ℝ)*X 0 1+(2119751811/5000000000 : ℝ)*X 0 2+(436768891/1000000000 : ℝ)*X 1 0+(1124943137/2500000000 : ℝ)*X 1 1+(2119751811/5000000000 : ℝ)*X 1 2+(436768891/1000000000 : ℝ)*X 2 0+(1124943137/2500000000 : ℝ)*X 2 1+(2119751811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33412890159039888860457/3104000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1080947353/50000000000000 : ℝ)*(base19) + (499935899/25000000000000 : ℝ)*(base23) + (48259291/50000000000000 : ℝ)*(lower2) + (14658941/5000000000000 : ℝ)*(upper3) + (35926157/25000000000000 : ℝ)*(upper5) + (1139390012473503/20000000000000 : ℝ)*(major0) + (1139390012473503/20000000000000 : ℝ)*(major1) + (1139390012473503/20000000000000 : ℝ)*(major2) + (37857656023649/500000000000 : ℝ)*(sp0) + (3785793208729069/50000000000000 : ℝ)*(sp1) + (7571586579609249/100000000000000 : ℝ)*(sp2) + (3822279126187683/100000000000000 : ℝ)*(sp3) + (11474924609/20000000000000 : ℝ)*(sp4) + (32060379093/100000000000000 : ℝ)*(sp7) + (477788898320847/12500000000000 : ℝ)*(f.failure) + (1892897144838211/25000000000000 : ℝ)*(f.sum) + (4032424982589/3104000000000000000000000000 : ℝ)*base65 + (1767952135289571257/310400000000000000000000000000000 : ℝ)*base68 + (1539499783408028743/310400000000000000000000000000000 : ℝ)*base69 + (1534537048511971257/310400000000000000000000000000000 : ℝ)*base72 + (10351711812067/3104000000000000000000000000 : ℝ)*base74 + (8830264094902428743/310400000000000000000000000000000 : ℝ)*base75 + (1412426502790428743/310400000000000000000000000000000 : ℝ)*base77 + (3286460024643171257/310400000000000000000000000000000 : ℝ)*base80 + (5581238555869/3104000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3072621/1250000000000000000000 : ℝ)*base89 + (3072621/1250000000000000000000 : ℝ)*base91 + (3072621/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2692424714113362612274681209/388000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (944727847/100000000000000 : ℝ)*(base19) + (1070087123/50000000000000 : ℝ)*(base23) + (53986439/25000000000000 : ℝ)*(upper3) + (73565901/25000000000000 : ℝ)*(lower4) + (30839519/20000000000000 : ℝ)*(upper5) + (5726565337348637/100000000000000 : ℝ)*(major0) + (5726565337348637/100000000000000 : ℝ)*(major1) + (5726565337348637/100000000000000 : ℝ)*(major2) + (2308986373/25000000000000 : ℝ)*(sp1) + (669968659/1250000000000 : ℝ)*(sp2) + (304437967470599/4000000000000 : ℝ)*(sp4) + (1522187801218327/20000000000000 : ℝ)*(sp5) + (7610893449098009/100000000000000 : ℝ)*(sp6) + (960545314156081/25000000000000 : ℝ)*(sp7) + (960545314156081/25000000000000 : ℝ)*(f.failure) + (304437967470599/4000000000000 : ℝ)*(f.sum) + (34170808614441/15520000000000000000000000000 : ℝ)*base66 + (17007502264489464597/1552000000000000000000000000000000 : ℝ)*base67 + (29290364447337464597/1552000000000000000000000000000000 : ℝ)*base69 + (4110552550774535403/1552000000000000000000000000000000 : ℝ)*base72 + (123993353190199/15520000000000000000000000000 : ℝ)*base73 + (31511522600745464597/1552000000000000000000000000000000 : ℝ)*base75 + (8497418257337464597/1552000000000000000000000000000000 : ℝ)*base77 + (14105391670249464597/1552000000000000000000000000000000 : ℝ)*base79 + (86789444858359/15520000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13924083/2500000000000000000000 : ℝ)*base89 + (13924083/2500000000000000000000 : ℝ)*base91 + (13924083/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1120_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1120_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16569/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1120_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1120_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1120_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16569/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5641/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

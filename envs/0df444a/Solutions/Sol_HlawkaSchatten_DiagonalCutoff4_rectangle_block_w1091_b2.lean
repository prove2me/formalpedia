-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1091_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:09.548054+00:00
-- url     : https://prove2.me/submissions/1b08535b-7e28-45fc-b111-4079ba244b46

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
theorem support_rectangle_w1091_s6_0 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095737703/5000000000 : ℝ)*x 0 + (269720377/500000000 : ℝ)*x 1 + (5264441243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095737703/5000000000 : ℝ)^2071 ≤ (13311413756497/100000000000000 : ℝ)^1559 := by
    have hnat : (1095737703 : ℕ)^2071*100000000000000^1559 ≤ 13311413756497^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095737703 5000000000 13311413756497 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269720377/500000000 : ℝ)^2071 ≤ (8809269221179/20000000000000 : ℝ)^1559 := by
    have hnat : (269720377 : ℕ)^2071*20000000000000^1559 ≤ 8809269221179^1559*500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269720377 500000000 8809269221179 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264441243/10000000000 : ℝ)^2071 ≤ (10660560030841/25000000000000 : ℝ)^1559 := by
    have hnat : (5264441243 : ℕ)^2071*25000000000000^1559 ≤ 10660560030841^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264441243 10000000000 10660560030841 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095737703/5000000000 : ℝ), (269720377/500000000 : ℝ), (5264441243/10000000000 : ℝ)] ![(13311413756497/100000000000000 : ℝ), (8809269221179/20000000000000 : ℝ), (10660560030841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095737703/5000000000 : ℝ)|^2071 ≤ (13311413756497/100000000000000 : ℝ)^1559
        have hw : |(-1095737703/5000000000 : ℝ)|=(1095737703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269720377/500000000 : ℝ)|^2071 ≤ (8809269221179/20000000000000 : ℝ)^1559
        have hw : |(269720377/500000000 : ℝ)|=(269720377/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264441243/10000000000 : ℝ)|^2071 ≤ (10660560030841/25000000000000 : ℝ)^1559
        have hw : |(5264441243/10000000000 : ℝ)|=(5264441243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s6_1 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668129757/1250000000 : ℝ)*x 0 + (-2257416521/10000000000 : ℝ)*x 1 + (5264441243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668129757/1250000000 : ℝ)^2071 ≤ (5438956684043/12500000000000 : ℝ)^1559 := by
    have hnat : (668129757 : ℕ)^2071*12500000000000^1559 ≤ 5438956684043^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668129757 1250000000 5438956684043 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257416521/10000000000 : ℝ)^2071 ≤ (1730763299373/12500000000000 : ℝ)^1559 := by
    have hnat : (2257416521 : ℕ)^2071*12500000000000^1559 ≤ 1730763299373^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257416521 10000000000 1730763299373 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264441243/10000000000 : ℝ)^2071 ≤ (10660560030841/25000000000000 : ℝ)^1559 := by
    have hnat : (5264441243 : ℕ)^2071*25000000000000^1559 ≤ 10660560030841^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264441243 10000000000 10660560030841 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668129757/1250000000 : ℝ), (-2257416521/10000000000 : ℝ), (5264441243/10000000000 : ℝ)] ![(5438956684043/12500000000000 : ℝ), (1730763299373/12500000000000 : ℝ), (10660560030841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668129757/1250000000 : ℝ)|^2071 ≤ (5438956684043/12500000000000 : ℝ)^1559
        have hw : |(668129757/1250000000 : ℝ)|=(668129757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2257416521/10000000000 : ℝ)|^2071 ≤ (1730763299373/12500000000000 : ℝ)^1559
        have hw : |(-2257416521/10000000000 : ℝ)|=(2257416521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264441243/10000000000 : ℝ)|^2071 ≤ (10660560030841/25000000000000 : ℝ)^1559
        have hw : |(5264441243/10000000000 : ℝ)|=(5264441243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s6_2 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668129757/1250000000 : ℝ)*x 0 + (5264441243/10000000000 : ℝ)*x 1 + (-2257416521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668129757/1250000000 : ℝ)^2071 ≤ (5438956684043/12500000000000 : ℝ)^1559 := by
    have hnat : (668129757 : ℕ)^2071*12500000000000^1559 ≤ 5438956684043^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668129757 1250000000 5438956684043 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264441243/10000000000 : ℝ)^2071 ≤ (10660560030841/25000000000000 : ℝ)^1559 := by
    have hnat : (5264441243 : ℕ)^2071*25000000000000^1559 ≤ 10660560030841^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264441243 10000000000 10660560030841 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257416521/10000000000 : ℝ)^2071 ≤ (1730763299373/12500000000000 : ℝ)^1559 := by
    have hnat : (2257416521 : ℕ)^2071*12500000000000^1559 ≤ 1730763299373^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257416521 10000000000 1730763299373 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668129757/1250000000 : ℝ), (5264441243/10000000000 : ℝ), (-2257416521/10000000000 : ℝ)] ![(5438956684043/12500000000000 : ℝ), (10660560030841/25000000000000 : ℝ), (1730763299373/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668129757/1250000000 : ℝ)|^2071 ≤ (5438956684043/12500000000000 : ℝ)^1559
        have hw : |(668129757/1250000000 : ℝ)|=(668129757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264441243/10000000000 : ℝ)|^2071 ≤ (10660560030841/25000000000000 : ℝ)^1559
        have hw : |(5264441243/10000000000 : ℝ)|=(5264441243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2257416521/10000000000 : ℝ)|^2071 ≤ (1730763299373/12500000000000 : ℝ)^1559
        have hw : |(-2257416521/10000000000 : ℝ)|=(2257416521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s6_3 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (54648559/125000000 : ℝ)*x 0 + (4245781213/10000000000 : ℝ)*x 1 + (562720229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54648559/125000000 : ℝ)^2071 ≤ (33316446937249/100000000000000 : ℝ)^1559 := by
    have hnat : (54648559 : ℕ)^2071*100000000000000^1559 ≤ 33316446937249^1559*125000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54648559 125000000 33316446937249 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245781213/10000000000 : ℝ)^2071 ≤ (16022971933283/50000000000000 : ℝ)^1559 := by
    have hnat : (4245781213 : ℕ)^2071*50000000000000^1559 ≤ 16022971933283^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245781213 10000000000 16022971933283 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562720229/1250000000 : ℝ)^2071 ≤ (1731880458531/5000000000000 : ℝ)^1559 := by
    have hnat : (562720229 : ℕ)^2071*5000000000000^1559 ≤ 1731880458531^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562720229 1250000000 1731880458531 5000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54648559/125000000 : ℝ), (4245781213/10000000000 : ℝ), (562720229/1250000000 : ℝ)] ![(33316446937249/100000000000000 : ℝ), (16022971933283/50000000000000 : ℝ), (1731880458531/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54648559/125000000 : ℝ)|^2071 ≤ (33316446937249/100000000000000 : ℝ)^1559
        have hw : |(54648559/125000000 : ℝ)|=(54648559/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245781213/10000000000 : ℝ)|^2071 ≤ (16022971933283/50000000000000 : ℝ)^1559
        have hw : |(4245781213/10000000000 : ℝ)|=(4245781213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562720229/1250000000 : ℝ)|^2071 ≤ (1731880458531/5000000000000 : ℝ)^1559
        have hw : |(562720229/1250000000 : ℝ)|=(562720229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s6_4 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2191480577/10000000000 : ℝ)*x 0 + (1316192353/2500000000 : ℝ)*x 1 + (1078815627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191480577/10000000000 : ℝ)^2071 ≤ (1331145548149/10000000000000 : ℝ)^1559 := by
    have hnat : (2191480577 : ℕ)^2071*10000000000000^1559 ≤ 1331145548149^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191480577 10000000000 1331145548149 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316192353/2500000000 : ℝ)^2071 ≤ (42645771334711/100000000000000 : ℝ)^1559 := by
    have hnat : (1316192353 : ℕ)^2071*100000000000000^1559 ≤ 42645771334711^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316192353 2500000000 42645771334711 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078815627/2000000000 : ℝ)^2071 ≤ (11010693291009/25000000000000 : ℝ)^1559 := by
    have hnat : (1078815627 : ℕ)^2071*25000000000000^1559 ≤ 11010693291009^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078815627 2000000000 11010693291009 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2191480577/10000000000 : ℝ), (1316192353/2500000000 : ℝ), (1078815627/2000000000 : ℝ)] ![(1331145548149/10000000000000 : ℝ), (42645771334711/100000000000000 : ℝ), (11010693291009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2191480577/10000000000 : ℝ)|^2071 ≤ (1331145548149/10000000000000 : ℝ)^1559
        have hw : |(-2191480577/10000000000 : ℝ)|=(2191480577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316192353/2500000000 : ℝ)|^2071 ≤ (42645771334711/100000000000000 : ℝ)^1559
        have hw : |(1316192353/2500000000 : ℝ)|=(1316192353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078815627/2000000000 : ℝ)|^2071 ≤ (11010693291009/25000000000000 : ℝ)^1559
        have hw : |(1078815627/2000000000 : ℝ)|=(1078815627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s6_5 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312237833/10000000000 : ℝ)*x 0 + (-1063889791/5000000000 : ℝ)*x 1 + (5394078123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312237833/10000000000 : ℝ)^2071 ≤ (168583233653/390625000000 : ℝ)^1559 := by
    have hnat : (5312237833 : ℕ)^2071*390625000000^1559 ≤ 168583233653^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312237833 10000000000 168583233653 390625000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063889791/5000000000 : ℝ)^2071 ≤ (639995956957/5000000000000 : ℝ)^1559 := by
    have hnat : (1063889791 : ℕ)^2071*5000000000000^1559 ≤ 639995956957^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063889791 5000000000 639995956957 5000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394078123/10000000000 : ℝ)^2071 ≤ (44042773033877/100000000000000 : ℝ)^1559 := by
    have hnat : (5394078123 : ℕ)^2071*100000000000000^1559 ≤ 44042773033877^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394078123 10000000000 44042773033877 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312237833/10000000000 : ℝ), (-1063889791/5000000000 : ℝ), (5394078123/10000000000 : ℝ)] ![(168583233653/390625000000 : ℝ), (639995956957/5000000000000 : ℝ), (44042773033877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312237833/10000000000 : ℝ)|^2071 ≤ (168583233653/390625000000 : ℝ)^1559
        have hw : |(5312237833/10000000000 : ℝ)|=(5312237833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1063889791/5000000000 : ℝ)|^2071 ≤ (639995956957/5000000000000 : ℝ)^1559
        have hw : |(-1063889791/5000000000 : ℝ)|=(1063889791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394078123/10000000000 : ℝ)|^2071 ≤ (44042773033877/100000000000000 : ℝ)^1559
        have hw : |(5394078123/10000000000 : ℝ)|=(5394078123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s6_6 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312237819/10000000000 : ℝ)*x 0 + (2697039059/5000000000 : ℝ)*x 1 + (-2127779607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312237819/10000000000 : ℝ)^2071 ≤ (43157307664077/100000000000000 : ℝ)^1559 := by
    have hnat : (5312237819 : ℕ)^2071*100000000000000^1559 ≤ 43157307664077^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312237819 10000000000 43157307664077 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697039059/5000000000 : ℝ)^2071 ≤ (11010693244911/25000000000000 : ℝ)^1559 := by
    have hnat : (2697039059 : ℕ)^2071*25000000000000^1559 ≤ 11010693244911^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697039059 5000000000 11010693244911 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127779607/10000000000 : ℝ)^2071 ≤ (12799919338921/100000000000000 : ℝ)^1559 := by
    have hnat : (2127779607 : ℕ)^2071*100000000000000^1559 ≤ 12799919338921^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127779607 10000000000 12799919338921 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312237819/10000000000 : ℝ), (2697039059/5000000000 : ℝ), (-2127779607/10000000000 : ℝ)] ![(43157307664077/100000000000000 : ℝ), (11010693244911/25000000000000 : ℝ), (12799919338921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312237819/10000000000 : ℝ)|^2071 ≤ (43157307664077/100000000000000 : ℝ)^1559
        have hw : |(5312237819/10000000000 : ℝ)|=(5312237819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697039059/5000000000 : ℝ)|^2071 ≤ (11010693244911/25000000000000 : ℝ)^1559
        have hw : |(2697039059/5000000000 : ℝ)|=(2697039059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2127779607/10000000000 : ℝ)|^2071 ≤ (12799919338921/100000000000000 : ℝ)^1559
        have hw : |(-2127779607/10000000000 : ℝ)|=(2127779607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s6_7 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2185947411/5000000000 : ℝ)*x 0 + (281319711/625000000 : ℝ)*x 1 + (1061607497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185947411/5000000000 : ℝ)^2071 ≤ (33316549203301/100000000000000 : ℝ)^1559 := by
    have hnat : (2185947411 : ℕ)^2071*100000000000000^1559 ≤ 33316549203301^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185947411 5000000000 33316549203301 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281319711/625000000 : ℝ)^2071 ≤ (34631001808549/100000000000000 : ℝ)^1559 := by
    have hnat : (281319711 : ℕ)^2071*100000000000000^1559 ≤ 34631001808549^1559*625000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281319711 625000000 34631001808549 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061607497/2500000000 : ℝ)^2071 ≤ (32052448973549/100000000000000 : ℝ)^1559 := by
    have hnat : (1061607497 : ℕ)^2071*100000000000000^1559 ≤ 32052448973549^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061607497 2500000000 32052448973549 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185947411/5000000000 : ℝ), (281319711/625000000 : ℝ), (1061607497/2500000000 : ℝ)] ![(33316549203301/100000000000000 : ℝ), (34631001808549/100000000000000 : ℝ), (32052448973549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185947411/5000000000 : ℝ)|^2071 ≤ (33316549203301/100000000000000 : ℝ)^1559
        have hw : |(2185947411/5000000000 : ℝ)|=(2185947411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281319711/625000000 : ℝ)|^2071 ≤ (34631001808549/100000000000000 : ℝ)^1559
        have hw : |(281319711/625000000 : ℝ)|=(281319711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061607497/2500000000 : ℝ)|^2071 ≤ (32052448973549/100000000000000 : ℝ)^1559
        have hw : |(1061607497/2500000000 : ℝ)|=(1061607497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1091_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2819/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14029/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5619/50000 : ℝ) ^ (8283/2048 : ℝ) ≤ (2894708314929057/20000000000000000000 : ℝ) := by
    have hpowers : (5619/50000 : ℝ)^8283 ≤ (2894708314929057/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5619 : ℕ)^8283*20000000000000000000^2048 ≤ 2894708314929057^2048*50000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5619 50000 2894708314929057 20000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5619/50000 : ℝ)) (X := (2894708314929057/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/25000 : ℝ) ^ (8283/2048 : ℝ) ≤ (35898999190603653/100000000000000000000 : ℝ) := by
    have hpowers : (3517/25000 : ℝ)^8283 ≤ (35898999190603653/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3517 : ℕ)^8283*100000000000000000000^2048 ≤ 35898999190603653^2048*25000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 25000 35898999190603653 100000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/25000 : ℝ)) (X := (35898999190603653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002894708314929057/10000000000000000000 : ℝ) ≤ (10000715648538993/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (10002894708314929057/10000000000000000000 : ℝ)^2048 ≤ (10000715648538993/10000000000000000 : ℝ)^8283 := by
      have hnat : (10002894708314929057 : ℕ)^2048*10000000000000000^8283 ≤ 10000715648538993^8283*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002894708314929057 10000000000000000000 10000715648538993 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000715648538993/10000000000000000 : ℝ)) (X := (10002894708314929057/10000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025186270382624469/50000000000000000000 : ℝ) ≤ (10001245242191233/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (50025186270382624469/50000000000000000000 : ℝ)^2048 ≤ (10001245242191233/10000000000000000 : ℝ)^8283 := by
      have hnat : (50025186270382624469 : ℕ)^2048*10000000000000000^8283 ≤ 10001245242191233^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025186270382624469 50000000000000000000 10001245242191233 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001245242191233/10000000000000000 : ℝ)) (X := (50025186270382624469/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035898999190603653/50000000000000000000 : ℝ) ≤ (10001774835843473/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (50035898999190603653/50000000000000000000 : ℝ)^2048 ≤ (10001774835843473/10000000000000000 : ℝ)^8283 := by
      have hnat : (50035898999190603653 : ℕ)^2048*10000000000000000^8283 ≤ 10001774835843473^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035898999190603653 50000000000000000000 10001774835843473 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001774835843473/10000000000000000 : ℝ)) (X := (50035898999190603653/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2894708314929057/20000000000000000000 : ℝ) ≤ ((565802442768752079/566000000000000000 : ℝ)+2*(6619920653/3537500000000 : ℝ)*(5619/50000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (565802442768752079/566000000000000000 : ℝ)+2*(6619920653/3537500000000 : ℝ)*(5619/50000 : ℝ)=(10000715648538993/10000000000000000 : ℝ) by norm_num, show 1+2*(2894708314929057/20000000000000000000 : ℝ)=(10002894708314929057/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35898999190603653/100000000000000000000 : ℝ)+(2894708314929057/20000000000000000000 : ℝ) ≤ ((565802442768752079/566000000000000000 : ℝ)+(6619920653/3537500000000 : ℝ)*((3517/25000 : ℝ)+(5619/50000 : ℝ)))^(8283/2048 : ℝ) := by
    rw [show (565802442768752079/566000000000000000 : ℝ)+(6619920653/3537500000000 : ℝ)*((3517/25000 : ℝ)+(5619/50000 : ℝ))=(10001245242191233/10000000000000000 : ℝ) by norm_num, show 1+(35898999190603653/100000000000000000000 : ℝ)+(2894708314929057/20000000000000000000 : ℝ)=(50025186270382624469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35898999190603653/100000000000000000000 : ℝ) ≤ ((565802442768752079/566000000000000000 : ℝ)+2*(6619920653/3537500000000 : ℝ)*(3517/25000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (565802442768752079/566000000000000000 : ℝ)+2*(6619920653/3537500000000 : ℝ)*(3517/25000 : ℝ)=(10001774835843473/10000000000000000 : ℝ) by norm_num, show 1+2*(35898999190603653/100000000000000000000 : ℝ)=(50035898999190603653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (565802442768752079/566000000000000000 : ℝ)*(X 1 0+X 2 0)+(6619920653/3537500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (565802442768752079/566000000000000000 : ℝ)) (alpha := (6619920653/3537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (565802442768752079/566000000000000000 : ℝ)*(X 0 1+X 2 1)+(6619920653/3537500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (565802442768752079/566000000000000000 : ℝ)) (alpha := (6619920653/3537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (565802442768752079/566000000000000000 : ℝ)*(X 0 2+X 1 2)+(6619920653/3537500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (565802442768752079/566000000000000000 : ℝ)) (alpha := (6619920653/3537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1095737703/5000000000 : ℝ)*X 0 0+(269720377/500000000 : ℝ)*X 0 1+(5264441243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668129757/1250000000 : ℝ)*X 1 0+(-2257416521/10000000000 : ℝ)*X 1 1+(5264441243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668129757/1250000000 : ℝ)*X 2 0+(5264441243/10000000000 : ℝ)*X 2 1+(-2257416521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((54648559/125000000 : ℝ)*X 0 0+(4245781213/10000000000 : ℝ)*X 0 1+(562720229/1250000000 : ℝ)*X 0 2+(54648559/125000000 : ℝ)*X 1 0+(4245781213/10000000000 : ℝ)*X 1 1+(562720229/1250000000 : ℝ)*X 1 2+(54648559/125000000 : ℝ)*X 2 0+(4245781213/10000000000 : ℝ)*X 2 1+(562720229/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2191480577/10000000000 : ℝ)*X 0 0+(1316192353/2500000000 : ℝ)*X 0 1+(1078815627/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312237833/10000000000 : ℝ)*X 1 0+(-1063889791/5000000000 : ℝ)*X 1 1+(5394078123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312237819/10000000000 : ℝ)*X 2 0+(2697039059/5000000000 : ℝ)*X 2 1+(-2127779607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185947411/5000000000 : ℝ)*X 0 0+(281319711/625000000 : ℝ)*X 0 1+(1061607497/2500000000 : ℝ)*X 0 2+(2185947411/5000000000 : ℝ)*X 1 0+(281319711/625000000 : ℝ)*X 1 1+(1061607497/2500000000 : ℝ)*X 1 2+(2185947411/5000000000 : ℝ)*X 2 0+(281319711/625000000 : ℝ)*X 2 1+(1061607497/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (139710817717022500898828049/28300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (494721457/50000000000000 : ℝ)*(base19) + (460594773/50000000000000 : ℝ)*(base23) + (9120421/25000000000000 : ℝ)*(lower2) + (125692357/100000000000000 : ℝ)*(upper3) + (1873003/2500000000000 : ℝ)*(upper5) + (5800465089919477/100000000000000 : ℝ)*(major0) + (5800465089919477/100000000000000 : ℝ)*(major1) + (2900232544959739/50000000000000 : ℝ)*(major2) + (3847165101836333/50000000000000 : ℝ)*(sp0) + (480897228891749/6250000000000 : ℝ)*(sp1) + (961794466315169/12500000000000 : ℝ)*(sp2) + (976639707685149/25000000000000 : ℝ)*(sp3) + (26448038231/100000000000000 : ℝ)*(sp4) + (2906565637/20000000000000 : ℝ)*(sp7) + (1953286681784391/50000000000000 : ℝ)*(f.failure) + (3847178325855449/50000000000000 : ℝ)*(f.sum) + (925324509611/283000000000000000000000000 : ℝ)*base65 + (6133379764217317/56600000000000000000000000000000 : ℝ)*base68 + (200164006103527381/28300000000000000000000000000000 : ℝ)*base69 + (148301815907382683/56600000000000000000000000000000 : ℝ)*base71 + (8114362739/1768750000000000000000000 : ℝ)*base73 + (236921600715172619/28300000000000000000000000000000 : ℝ)*base76 + (385373141009897317/56600000000000000000000000000000 : ℝ)*base78 + (472627312847097317/56600000000000000000000000000000 : ℝ)*base80 + (2174698148737/353750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (7737893/1000000000000000000000 : ℝ)*base89 + (7737893/1000000000000000000000 : ℝ)*base91 + (2262107/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2999401261928703972609/353750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1914181671/100000000000000 : ℝ)*(base19) + (1942917949/100000000000000 : ℝ)*(base23) + (23398759/12500000000000 : ℝ)*(upper3) + (29861973/100000000000000 : ℝ)*(lower4) + (106741149/50000000000000 : ℝ)*(upper5) + (5829921363876603/100000000000000 : ℝ)*(major0) + (5829921363876603/100000000000000 : ℝ)*(major1) + (5829921363876603/100000000000000 : ℝ)*(major2) + (52854321551/100000000000000 : ℝ)*(sp1) + (51704984479/100000000000000 : ℝ)*(sp2) + (1546686096707653/20000000000000 : ℝ)*(sp4) + (1933343928758761/25000000000000 : ℝ)*(sp5) + (3866688417817919/50000000000000 : ℝ)*(sp6) + (49080149519823/1250000000000 : ℝ)*(sp7) + (49080149519823/1250000000000 : ℝ)*(f.failure) + (1546686096707653/20000000000000 : ℝ)*(f.sum) + (12542603874553/1415000000000000000000000000 : ℝ)*base66 + (444994736405147637/56600000000000000000000000000000 : ℝ)*base67 + (641188466800147637/56600000000000000000000000000000 : ℝ)*base69 + (66457521183652363/56600000000000000000000000000000 : ℝ)*base72 + (1839145673743/1415000000000000000000000000 : ℝ)*base74 + (163354187597852363/56600000000000000000000000000000 : ℝ)*base76 + (2280232294452363/56600000000000000000000000000000 : ℝ)*base78 + (490766584688547637/56600000000000000000000000000000 : ℝ)*base79 + (6880400530647/1415000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (31629/25000000000000000000 : ℝ)*base89 + (31629/25000000000000000000 : ℝ)*base91 + (31629/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1091_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1091_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1091_s7_0 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2191508407/10000000000 : ℝ)*x 0 + (2696999621/5000000000 : ℝ)*x 1 + (5264828067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191508407/10000000000 : ℝ)^2071 ≤ (13311680043359/100000000000000 : ℝ)^1559 := by
    have hnat : (2191508407 : ℕ)^2071*100000000000000^1559 ≤ 13311680043359^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191508407 10000000000 13311680043359 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696999621/5000000000 : ℝ)^2071 ≤ (22020958724823/50000000000000 : ℝ)^1559 := by
    have hnat : (2696999621 : ℕ)^2071*50000000000000^1559 ≤ 22020958724823^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696999621 5000000000 22020958724823 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264828067/10000000000 : ℝ)^2071 ≤ (21323201245153/50000000000000 : ℝ)^1559 := by
    have hnat : (5264828067 : ℕ)^2071*50000000000000^1559 ≤ 21323201245153^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264828067 10000000000 21323201245153 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2191508407/10000000000 : ℝ), (2696999621/5000000000 : ℝ), (5264828067/10000000000 : ℝ)] ![(13311680043359/100000000000000 : ℝ), (22020958724823/50000000000000 : ℝ), (21323201245153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2191508407/10000000000 : ℝ)|^2071 ≤ (13311680043359/100000000000000 : ℝ)^1559
        have hw : |(-2191508407/10000000000 : ℝ)|=(2191508407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696999621/5000000000 : ℝ)|^2071 ≤ (22020958724823/50000000000000 : ℝ)^1559
        have hw : |(2696999621/5000000000 : ℝ)|=(2696999621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264828067/10000000000 : ℝ)|^2071 ≤ (21323201245153/50000000000000 : ℝ)^1559
        have hw : |(5264828067/10000000000 : ℝ)|=(5264828067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s7_1 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336234131/2500000000 : ℝ)*x 0 + (-564260071/2500000000 : ℝ)*x 1 + (658103521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336234131/2500000000 : ℝ)^2071 ≤ (10877638875661/25000000000000 : ℝ)^1559 := by
    have hnat : (1336234131 : ℕ)^2071*25000000000000^1559 ≤ 10877638875661^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336234131 2500000000 10877638875661 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564260071/2500000000 : ℝ)^2071 ≤ (3460760226843/25000000000000 : ℝ)^1559 := by
    have hnat : (564260071 : ℕ)^2071*25000000000000^1559 ≤ 3460760226843^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564260071 2500000000 3460760226843 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658103521/1250000000 : ℝ)^2071 ≤ (10661600894279/25000000000000 : ℝ)^1559 := by
    have hnat : (658103521 : ℕ)^2071*25000000000000^1559 ≤ 10661600894279^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658103521 1250000000 10661600894279 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336234131/2500000000 : ℝ), (-564260071/2500000000 : ℝ), (658103521/1250000000 : ℝ)] ![(10877638875661/25000000000000 : ℝ), (3460760226843/25000000000000 : ℝ), (10661600894279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336234131/2500000000 : ℝ)|^2071 ≤ (10877638875661/25000000000000 : ℝ)^1559
        have hw : |(1336234131/2500000000 : ℝ)|=(1336234131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-564260071/2500000000 : ℝ)|^2071 ≤ (3460760226843/25000000000000 : ℝ)^1559
        have hw : |(-564260071/2500000000 : ℝ)|=(564260071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658103521/1250000000 : ℝ)|^2071 ≤ (10661600894279/25000000000000 : ℝ)^1559
        have hw : |(658103521/1250000000 : ℝ)|=(658103521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s7_2 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672468387/5000000000 : ℝ)*x 0 + (2632413999/5000000000 : ℝ)*x 1 + (-2257040177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672468387/5000000000 : ℝ)^2071 ≤ (21755279103071/50000000000000 : ℝ)^1559 := by
    have hnat : (2672468387 : ℕ)^2071*50000000000000^1559 ≤ 21755279103071^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672468387 5000000000 21755279103071 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632413999/5000000000 : ℝ)^2071 ≤ (5330800218479/12500000000000 : ℝ)^1559 := by
    have hnat : (2632413999 : ℕ)^2071*12500000000000^1559 ≤ 5330800218479^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632413999 5000000000 5330800218479 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257040177/10000000000 : ℝ)^2071 ≤ (6921520017793/50000000000000 : ℝ)^1559 := by
    have hnat : (2257040177 : ℕ)^2071*50000000000000^1559 ≤ 6921520017793^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257040177 10000000000 6921520017793 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672468387/5000000000 : ℝ), (2632413999/5000000000 : ℝ), (-2257040177/10000000000 : ℝ)] ![(21755279103071/50000000000000 : ℝ), (5330800218479/12500000000000 : ℝ), (6921520017793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672468387/5000000000 : ℝ)|^2071 ≤ (21755279103071/50000000000000 : ℝ)^1559
        have hw : |(2672468387/5000000000 : ℝ)|=(2672468387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632413999/5000000000 : ℝ)|^2071 ≤ (5330800218479/12500000000000 : ℝ)^1559
        have hw : |(2632413999/5000000000 : ℝ)|=(2632413999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2257040177/10000000000 : ℝ)|^2071 ≤ (6921520017793/50000000000000 : ℝ)^1559
        have hw : |(-2257040177/10000000000 : ℝ)|=(2257040177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s7_3 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4371905139/10000000000 : ℝ)*x 0 + (4246561739/10000000000 : ℝ)*x 1 + (2250487951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371905139/10000000000 : ℝ)^2071 ≤ (33316653645953/100000000000000 : ℝ)^1559 := by
    have hnat : (4371905139 : ℕ)^2071*100000000000000^1559 ≤ 33316653645953^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371905139 10000000000 33316653645953 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246561739/10000000000 : ℝ)^2071 ≤ (1602688502411/5000000000000 : ℝ)^1559 := by
    have hnat : (4246561739 : ℕ)^2071*5000000000000^1559 ≤ 1602688502411^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246561739 10000000000 1602688502411 5000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250487951/5000000000 : ℝ)^2071 ≤ (17314788149813/50000000000000 : ℝ)^1559 := by
    have hnat : (2250487951 : ℕ)^2071*50000000000000^1559 ≤ 17314788149813^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250487951 5000000000 17314788149813 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371905139/10000000000 : ℝ), (4246561739/10000000000 : ℝ), (2250487951/5000000000 : ℝ)] ![(33316653645953/100000000000000 : ℝ), (1602688502411/5000000000000 : ℝ), (17314788149813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371905139/10000000000 : ℝ)|^2071 ≤ (33316653645953/100000000000000 : ℝ)^1559
        have hw : |(4371905139/10000000000 : ℝ)|=(4371905139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246561739/10000000000 : ℝ)|^2071 ≤ (1602688502411/5000000000000 : ℝ)^1559
        have hw : |(4246561739/10000000000 : ℝ)|=(4246561739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250487951/5000000000 : ℝ)|^2071 ≤ (17314788149813/50000000000000 : ℝ)^1559
        have hw : |(2250487951/5000000000 : ℝ)|=(2250487951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s7_4 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2191513533/10000000000 : ℝ)*x 0 + (5265152327/10000000000 : ℝ)*x 1 + (5393673733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191513533/10000000000 : ℝ)^2071 ≤ (266234428109/2000000000000 : ℝ)^1559 := by
    have hnat : (2191513533 : ℕ)^2071*2000000000000^1559 ≤ 266234428109^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191513533 10000000000 266234428109 2000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265152327/10000000000 : ℝ)^2071 ≤ (42649891723237/100000000000000 : ℝ)^1559 := by
    have hnat : (5265152327 : ℕ)^2071*100000000000000^1559 ≤ 42649891723237^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265152327 10000000000 42649891723237 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393673733/10000000000 : ℝ)^2071 ≤ (22019193426849/50000000000000 : ℝ)^1559 := by
    have hnat : (5393673733 : ℕ)^2071*50000000000000^1559 ≤ 22019193426849^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393673733 10000000000 22019193426849 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2191513533/10000000000 : ℝ), (5265152327/10000000000 : ℝ), (5393673733/10000000000 : ℝ)] ![(266234428109/2000000000000 : ℝ), (42649891723237/100000000000000 : ℝ), (22019193426849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2191513533/10000000000 : ℝ)|^2071 ≤ (266234428109/2000000000000 : ℝ)^1559
        have hw : |(-2191513533/10000000000 : ℝ)|=(2191513533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265152327/10000000000 : ℝ)|^2071 ≤ (42649891723237/100000000000000 : ℝ)^1559
        have hw : |(5265152327/10000000000 : ℝ)|=(5265152327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393673733/10000000000 : ℝ)|^2071 ≤ (22019193426849/50000000000000 : ℝ)^1559
        have hw : |(5393673733/10000000000 : ℝ)|=(5393673733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s7_5 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312336873/10000000000 : ℝ)*x 0 + (-16626521/78125000 : ℝ)*x 1 + (1348418433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312336873/10000000000 : ℝ)^2071 ≤ (2157918833999/5000000000000 : ℝ)^1559 := by
    have hnat : (5312336873 : ℕ)^2071*5000000000000^1559 ≤ 2157918833999^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312336873 10000000000 2157918833999 5000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16626521/78125000 : ℝ)^2071 ≤ (12803236460119/100000000000000 : ℝ)^1559 := by
    have hnat : (16626521 : ℕ)^2071*100000000000000^1559 ≤ 12803236460119^1559*78125000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16626521 78125000 12803236460119 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348418433/2500000000 : ℝ)^2071 ≤ (11009596710713/25000000000000 : ℝ)^1559 := by
    have hnat : (1348418433 : ℕ)^2071*25000000000000^1559 ≤ 11009596710713^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348418433 2500000000 11009596710713 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312336873/10000000000 : ℝ), (-16626521/78125000 : ℝ), (1348418433/2500000000 : ℝ)] ![(2157918833999/5000000000000 : ℝ), (12803236460119/100000000000000 : ℝ), (11009596710713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312336873/10000000000 : ℝ)|^2071 ≤ (2157918833999/5000000000000 : ℝ)^1559
        have hw : |(5312336873/10000000000 : ℝ)|=(5312336873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16626521/78125000 : ℝ)|^2071 ≤ (12803236460119/100000000000000 : ℝ)^1559
        have hw : |(-16626521/78125000 : ℝ)|=(16626521/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348418433/2500000000 : ℝ)|^2071 ≤ (11009596710713/25000000000000 : ℝ)^1559
        have hw : |(1348418433/2500000000 : ℝ)|=(1348418433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s7_6 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (8499739/16000000 : ℝ)*x 0 + (5393673731/10000000000 : ℝ)*x 1 + (-2128194687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8499739/16000000 : ℝ)^2071 ≤ (10789594175391/25000000000000 : ℝ)^1559 := by
    have hnat : (8499739 : ℕ)^2071*25000000000000^1559 ≤ 10789594175391^1559*16000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8499739 16000000 10789594175391 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393673731/10000000000 : ℝ)^2071 ≤ (22019193416003/50000000000000 : ℝ)^1559 := by
    have hnat : (5393673731 : ℕ)^2071*50000000000000^1559 ≤ 22019193416003^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393673731 10000000000 22019193416003 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128194687/10000000000 : ℝ)^2071 ≤ (400101139129/3125000000000 : ℝ)^1559 := by
    have hnat : (2128194687 : ℕ)^2071*3125000000000^1559 ≤ 400101139129^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128194687 10000000000 400101139129 3125000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8499739/16000000 : ℝ), (5393673731/10000000000 : ℝ), (-2128194687/10000000000 : ℝ)] ![(10789594175391/25000000000000 : ℝ), (22019193416003/50000000000000 : ℝ), (400101139129/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8499739/16000000 : ℝ)|^2071 ≤ (10789594175391/25000000000000 : ℝ)^1559
        have hw : |(8499739/16000000 : ℝ)|=(8499739/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393673731/10000000000 : ℝ)|^2071 ≤ (22019193416003/50000000000000 : ℝ)^1559
        have hw : |(5393673731/10000000000 : ℝ)|=(5393673731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128194687/10000000000 : ℝ)|^2071 ≤ (400101139129/3125000000000 : ℝ)^1559
        have hw : |(-2128194687/10000000000 : ℝ)|=(2128194687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s7_7 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (68311171/156250000 : ℝ)*x 0 + (22501687/50000000 : ℝ)*x 1 + (1061800657/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68311171/156250000 : ℝ)^2071 ≤ (16658376452761/50000000000000 : ℝ)^1559 := by
    have hnat : (68311171 : ℕ)^2071*50000000000000^1559 ≤ 16658376452761^1559*156250000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68311171 156250000 16658376452761 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22501687/50000000 : ℝ)^2071 ≤ (1384922024277/4000000000000 : ℝ)^1559 := by
    have hnat : (22501687 : ℕ)^2071*4000000000000^1559 ≤ 1384922024277^1559*50000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22501687 50000000 1384922024277 4000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061800657/2500000000 : ℝ)^2071 ≤ (1603009823509/5000000000000 : ℝ)^1559 := by
    have hnat : (1061800657 : ℕ)^2071*5000000000000^1559 ≤ 1603009823509^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061800657 2500000000 1603009823509 5000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68311171/156250000 : ℝ), (22501687/50000000 : ℝ), (1061800657/2500000000 : ℝ)] ![(16658376452761/50000000000000 : ℝ), (1384922024277/4000000000000 : ℝ), (1603009823509/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68311171/156250000 : ℝ)|^2071 ≤ (16658376452761/50000000000000 : ℝ)^1559
        have hw : |(68311171/156250000 : ℝ)|=(68311171/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22501687/50000000 : ℝ)|^2071 ≤ (1384922024277/4000000000000 : ℝ)^1559
        have hw : |(22501687/50000000 : ℝ)|=(22501687/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061800657/2500000000 : ℝ)|^2071 ≤ (1603009823509/5000000000000 : ℝ)^1559
        have hw : |(1061800657/2500000000 : ℝ)|=(1061800657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1091_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2821/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (701/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2819/25000 : ℝ) ^ (8283/2048 : ℝ) ≤ (14672499794947173/100000000000000000000 : ℝ) := by
    have hpowers : (2819/25000 : ℝ)^8283 ≤ (14672499794947173/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2819 : ℕ)^8283*100000000000000000000^2048 ≤ 14672499794947173^2048*25000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 25000 14672499794947173 100000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/25000 : ℝ)) (X := (14672499794947173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14029/100000 : ℝ) ^ (8283/2048 : ℝ) ≤ (35498188601034111/100000000000000000000 : ℝ) := by
    have hpowers : (14029/100000 : ℝ)^8283 ≤ (35498188601034111/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14029 : ℕ)^8283*100000000000000000000^2048 ≤ 35498188601034111^2048*100000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14029 100000 35498188601034111 100000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14029/100000 : ℝ)) (X := (35498188601034111/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014672499794947173/50000000000000000000 : ℝ) ≤ (10000725485000699/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (50014672499794947173/50000000000000000000 : ℝ)^2048 ≤ (10000725485000699/10000000000000000 : ℝ)^8283 := by
      have hnat : (50014672499794947173 : ℕ)^2048*10000000000000000^8283 ≤ 10000725485000699^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014672499794947173 50000000000000000000 10000725485000699 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000725485000699/10000000000000000 : ℝ)) (X := (50014672499794947173/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012542672098995321/25000000000000000000 : ℝ) ≤ (10001240253210361/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (25012542672098995321/25000000000000000000 : ℝ)^2048 ≤ (10001240253210361/10000000000000000 : ℝ)^8283 := by
      have hnat : (25012542672098995321 : ℕ)^2048*10000000000000000^8283 ≤ 10001240253210361^8283*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012542672098995321 25000000000000000000 10001240253210361 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001240253210361/10000000000000000 : ℝ)) (X := (25012542672098995321/25000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035498188601034111/50000000000000000000 : ℝ) ≤ (10001755021420023/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (50035498188601034111/50000000000000000000 : ℝ)^2048 ≤ (10001755021420023/10000000000000000 : ℝ)^8283 := by
      have hnat : (50035498188601034111 : ℕ)^2048*10000000000000000^8283 ≤ 10001755021420023^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035498188601034111 50000000000000000000 10001755021420023 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001755021420023/10000000000000000 : ℝ)) (X := (50035498188601034111/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14672499794947173/100000000000000000000 : ℝ) ≤ ((27520388207542626923/27530000000000000000 : ℝ)+2*(257384104831/137650000000000 : ℝ)*(2819/25000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (27520388207542626923/27530000000000000000 : ℝ)+2*(257384104831/137650000000000 : ℝ)*(2819/25000 : ℝ)=(10000725485000699/10000000000000000 : ℝ) by norm_num, show 1+2*(14672499794947173/100000000000000000000 : ℝ)=(50014672499794947173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35498188601034111/100000000000000000000 : ℝ)+(14672499794947173/100000000000000000000 : ℝ) ≤ ((27520388207542626923/27530000000000000000 : ℝ)+(257384104831/137650000000000 : ℝ)*((14029/100000 : ℝ)+(2819/25000 : ℝ)))^(8283/2048 : ℝ) := by
    rw [show (27520388207542626923/27530000000000000000 : ℝ)+(257384104831/137650000000000 : ℝ)*((14029/100000 : ℝ)+(2819/25000 : ℝ))=(10001240253210361/10000000000000000 : ℝ) by norm_num, show 1+(35498188601034111/100000000000000000000 : ℝ)+(14672499794947173/100000000000000000000 : ℝ)=(25012542672098995321/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35498188601034111/100000000000000000000 : ℝ) ≤ ((27520388207542626923/27530000000000000000 : ℝ)+2*(257384104831/137650000000000 : ℝ)*(14029/100000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (27520388207542626923/27530000000000000000 : ℝ)+2*(257384104831/137650000000000 : ℝ)*(14029/100000 : ℝ)=(10001755021420023/10000000000000000 : ℝ) by norm_num, show 1+2*(35498188601034111/100000000000000000000 : ℝ)=(50035498188601034111/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27520388207542626923/27530000000000000000 : ℝ)*(X 1 0+X 2 0)+(257384104831/137650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (27520388207542626923/27530000000000000000 : ℝ)) (alpha := (257384104831/137650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27520388207542626923/27530000000000000000 : ℝ)*(X 0 1+X 2 1)+(257384104831/137650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (27520388207542626923/27530000000000000000 : ℝ)) (alpha := (257384104831/137650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27520388207542626923/27530000000000000000 : ℝ)*(X 0 2+X 1 2)+(257384104831/137650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (27520388207542626923/27530000000000000000 : ℝ)) (alpha := (257384104831/137650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2191508407/10000000000 : ℝ)*X 0 0+(2696999621/5000000000 : ℝ)*X 0 1+(5264828067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336234131/2500000000 : ℝ)*X 1 0+(-564260071/2500000000 : ℝ)*X 1 1+(658103521/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672468387/5000000000 : ℝ)*X 2 0+(2632413999/5000000000 : ℝ)*X 2 1+(-2257040177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371905139/10000000000 : ℝ)*X 0 0+(4246561739/10000000000 : ℝ)*X 0 1+(2250487951/5000000000 : ℝ)*X 0 2+(4371905139/10000000000 : ℝ)*X 1 0+(4246561739/10000000000 : ℝ)*X 1 1+(2250487951/5000000000 : ℝ)*X 1 2+(4371905139/10000000000 : ℝ)*X 2 0+(4246561739/10000000000 : ℝ)*X 2 1+(2250487951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2191513533/10000000000 : ℝ)*X 0 0+(5265152327/10000000000 : ℝ)*X 0 1+(5393673733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312336873/10000000000 : ℝ)*X 1 0+(-16626521/78125000 : ℝ)*X 1 1+(1348418433/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((8499739/16000000 : ℝ)*X 2 0+(5393673731/10000000000 : ℝ)*X 2 1+(-2128194687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((68311171/156250000 : ℝ)*X 0 0+(22501687/50000000 : ℝ)*X 0 1+(1061800657/2500000000 : ℝ)*X 0 2+(68311171/156250000 : ℝ)*X 1 0+(22501687/50000000 : ℝ)*X 1 1+(1061800657/2500000000 : ℝ)*X 1 2+(68311171/156250000 : ℝ)*X 2 0+(22501687/50000000 : ℝ)*X 2 1+(1061800657/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2321488205359724067620715171/344125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1459841947/100000000000000 : ℝ)*(base19) + (60516613/4000000000000 : ℝ)*(base23) + (3303531/2000000000000 : ℝ)*(lower2) + (1071823/1000000000000 : ℝ)*(upper3) + (28820173/25000000000000 : ℝ)*(upper5) + (1459049953115741/25000000000000 : ℝ)*(major0) + (1459049953115741/25000000000000 : ℝ)*(major1) + (1459049953115741/25000000000000 : ℝ)*(major2) + (309668301851077/4000000000000 : ℝ)*(sp0) + (3870878743333423/50000000000000 : ℝ)*(sp1) + (7741757433593467/100000000000000 : ℝ)*(sp2) + (982654464564127/25000000000000 : ℝ)*(sp3) + (51400231869/100000000000000 : ℝ)*(sp4) + (22595291923/100000000000000 : ℝ)*(sp7) + (3930640453548431/100000000000000 : ℝ)*(f.failure) + (7741758946508793/100000000000000 : ℝ)*(f.sum) + (12044639901761/1720625000000000000000000000 : ℝ)*base65 + (361526593150355057/688250000000000000000000000000000 : ℝ)*base68 + (4968606820396894943/688250000000000000000000000000000 : ℝ)*base69 + (14563513549084894943/688250000000000000000000000000000 : ℝ)*base71 + (19385900306763/3441250000000000000000000000 : ℝ)*base74 + (2806813485105057/688250000000000000000000000000000 : ℝ)*base76 + (3187310814094394943/688250000000000000000000000000000 : ℝ)*base77 + (3744236316122394943/688250000000000000000000000000000 : ℝ)*base79 + (22588833391403/13765000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (3746813/2000000000000000000000 : ℝ)*base89 + (3746813/2000000000000000000000 : ℝ)*base91 + (3746813/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69728353776330192001377/13765000000000000000000000000 : ℝ) := by norm_num
    linear_combination (926796697/100000000000000 : ℝ)*(base19) + (1014893171/100000000000000 : ℝ)*(base23) + (100616239/100000000000000 : ℝ)*(upper3) + (38479827/100000000000000 : ℝ)*(lower4) + (51197247/50000000000000 : ℝ)*(upper5) + (2932817180566601/50000000000000 : ℝ)*(major0) + (2932817180566601/50000000000000 : ℝ)*(major1) + (2932817180566601/50000000000000 : ℝ)*(major2) + (25264236483/100000000000000 : ℝ)*(sp1) + (27338844441/100000000000000 : ℝ)*(sp2) + (1945201033419513/25000000000000 : ℝ)*(sp4) + (972597242830609/12500000000000 : ℝ)*(sp5) + (194519394498511/2500000000000 : ℝ)*(sp6) + (1975232209867059/50000000000000 : ℝ)*(sp7) + (1975232209867059/50000000000000 : ℝ)*(f.failure) + (1945201033419513/25000000000000 : ℝ)*(f.sum) + (64473572993/26884765625000000000000000 : ℝ)*base66 + (9857836123822601277/1376500000000000000000000000000000 : ℝ)*base68 + (4241069190846601277/1376500000000000000000000000000000 : ℝ)*base70 + (6018866929873398723/1376500000000000000000000000000000 : ℝ)*base71 + (2432495453041/860312500000000000000000000 : ℝ)*base74 + (26494045906655398723/1376500000000000000000000000000000 : ℝ)*base75 + (109487242855601277/1376500000000000000000000000000000 : ℝ)*base78 + (4788930843796398723/1376500000000000000000000000000000 : ℝ)*base79 + (71761386394969/13765000000000000000000000000 : ℝ)*base81 + (4300457/1000000000000000000000 : ℝ)*base89 + (4300457/1000000000000000000000 : ℝ)*base91 + (4300457/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1091_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (701/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1091_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1091_s8_0 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2191518717/10000000000 : ℝ)*x 0 + (5393908373/10000000000 : ℝ)*x 1 + (5264911931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191518717/10000000000 : ℝ)^2071 ≤ (13311763235579/100000000000000 : ℝ)^1559 := by
    have hnat : (2191518717 : ℕ)^2071*100000000000000^1559 ≤ 13311763235579^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191518717 10000000000 13311763235579 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393908373/10000000000 : ℝ)^2071 ≤ (11010232960611/25000000000000 : ℝ)^1559 := by
    have hnat : (5393908373 : ℕ)^2071*25000000000000^1559 ≤ 11010232960611^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393908373 10000000000 11010232960611 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264911931/10000000000 : ℝ)^2071 ≤ (42647304910699/100000000000000 : ℝ)^1559 := by
    have hnat : (5264911931 : ℕ)^2071*100000000000000^1559 ≤ 42647304910699^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264911931 10000000000 42647304910699 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2191518717/10000000000 : ℝ), (5393908373/10000000000 : ℝ), (5264911931/10000000000 : ℝ)] ![(13311763235579/100000000000000 : ℝ), (11010232960611/25000000000000 : ℝ), (42647304910699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2191518717/10000000000 : ℝ)|^2071 ≤ (13311763235579/100000000000000 : ℝ)^1559
        have hw : |(-2191518717/10000000000 : ℝ)|=(2191518717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393908373/10000000000 : ℝ)|^2071 ≤ (11010232960611/25000000000000 : ℝ)^1559
        have hw : |(5393908373/10000000000 : ℝ)|=(5393908373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264911931/10000000000 : ℝ)|^2071 ≤ (42647304910699/100000000000000 : ℝ)^1559
        have hw : |(5264911931/10000000000 : ℝ)|=(5264911931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s8_1 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668114133/1250000000 : ℝ)*x 0 + (-1128480417/5000000000 : ℝ)*x 1 + (5264911901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668114133/1250000000 : ℝ)^2071 ≤ (8702060361313/20000000000000 : ℝ)^1559 := by
    have hnat : (668114133 : ℕ)^2071*20000000000000^1559 ≤ 8702060361313^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668114133 1250000000 8702060361313 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128480417/5000000000 : ℝ)^2071 ≤ (6921196794773/50000000000000 : ℝ)^1559 := by
    have hnat : (1128480417 : ℕ)^2071*50000000000000^1559 ≤ 6921196794773^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128480417 5000000000 6921196794773 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264911901/10000000000 : ℝ)^2071 ≤ (21323652293941/50000000000000 : ℝ)^1559 := by
    have hnat : (5264911901 : ℕ)^2071*50000000000000^1559 ≤ 21323652293941^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264911901 10000000000 21323652293941 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668114133/1250000000 : ℝ), (-1128480417/5000000000 : ℝ), (5264911901/10000000000 : ℝ)] ![(8702060361313/20000000000000 : ℝ), (6921196794773/50000000000000 : ℝ), (21323652293941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668114133/1250000000 : ℝ)|^2071 ≤ (8702060361313/20000000000000 : ℝ)^1559
        have hw : |(668114133/1250000000 : ℝ)|=(668114133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128480417/5000000000 : ℝ)|^2071 ≤ (6921196794773/50000000000000 : ℝ)^1559
        have hw : |(-1128480417/5000000000 : ℝ)|=(1128480417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264911901/10000000000 : ℝ)|^2071 ≤ (21323652293941/50000000000000 : ℝ)^1559
        have hw : |(5264911901/10000000000 : ℝ)|=(5264911901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s8_2 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344913699/10000000000 : ℝ)*x 0 + (2632455411/5000000000 : ℝ)*x 1 + (-282120177/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344913699/10000000000 : ℝ)^2071 ≤ (43510308673441/100000000000000 : ℝ)^1559 := by
    have hnat : (5344913699 : ℕ)^2071*100000000000000^1559 ≤ 43510308673441^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344913699 10000000000 43510308673441 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632455411/5000000000 : ℝ)^2071 ≤ (170589171909/400000000000 : ℝ)^1559 := by
    have hnat : (2632455411 : ℕ)^2071*400000000000^1559 ≤ 170589171909^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632455411 5000000000 170589171909 400000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282120177/1250000000 : ℝ)^2071 ≤ (3460599582839/25000000000000 : ℝ)^1559 := by
    have hnat : (282120177 : ℕ)^2071*25000000000000^1559 ≤ 3460599582839^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282120177 1250000000 3460599582839 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344913699/10000000000 : ℝ), (2632455411/5000000000 : ℝ), (-282120177/1250000000 : ℝ)] ![(43510308673441/100000000000000 : ℝ), (170589171909/400000000000 : ℝ), (3460599582839/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344913699/10000000000 : ℝ)|^2071 ≤ (43510308673441/100000000000000 : ℝ)^1559
        have hw : |(5344913699/10000000000 : ℝ)|=(5344913699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632455411/5000000000 : ℝ)|^2071 ≤ (170589171909/400000000000 : ℝ)^1559
        have hw : |(2632455411/5000000000 : ℝ)|=(2632455411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282120177/1250000000 : ℝ)|^2071 ≤ (3460599582839/25000000000000 : ℝ)^1559
        have hw : |(-282120177/1250000000 : ℝ)|=(282120177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s8_3 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4371909111/10000000000 : ℝ)*x 0 + (4246732997/10000000000 : ℝ)*x 1 + (1125200987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371909111/10000000000 : ℝ)^2071 ≤ (1665834692797/5000000000000 : ℝ)^1559 := by
    have hnat : (4371909111 : ℕ)^2071*5000000000000^1559 ≤ 1665834692797^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371909111 10000000000 1665834692797 5000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246732997/10000000000 : ℝ)^2071 ≤ (32055487281917/100000000000000 : ℝ)^1559 := by
    have hnat : (4246732997 : ℕ)^2071*100000000000000^1559 ≤ 32055487281917^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246732997 10000000000 32055487281917 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125200987/2500000000 : ℝ)^2071 ≤ (34627818845361/100000000000000 : ℝ)^1559 := by
    have hnat : (1125200987 : ℕ)^2071*100000000000000^1559 ≤ 34627818845361^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125200987 2500000000 34627818845361 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371909111/10000000000 : ℝ), (4246732997/10000000000 : ℝ), (1125200987/2500000000 : ℝ)] ![(1665834692797/5000000000000 : ℝ), (32055487281917/100000000000000 : ℝ), (34627818845361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371909111/10000000000 : ℝ)|^2071 ≤ (1665834692797/5000000000000 : ℝ)^1559
        have hw : |(4371909111/10000000000 : ℝ)|=(4371909111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246732997/10000000000 : ℝ)|^2071 ≤ (32055487281917/100000000000000 : ℝ)^1559
        have hw : |(4246732997/10000000000 : ℝ)|=(4246732997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125200987/2500000000 : ℝ)|^2071 ≤ (34627818845361/100000000000000 : ℝ)^1559
        have hw : |(1125200987/2500000000 : ℝ)|=(1125200987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s8_4 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-273940447/1250000000 : ℝ)*x 0 + (2632617557/5000000000 : ℝ)*x 1 + (5267172/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273940447/1250000000 : ℝ)^2071 ≤ (6655901221643/50000000000000 : ℝ)^1559 := by
    have hnat : (273940447 : ℕ)^2071*50000000000000^1559 ≤ 6655901221643^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273940447 1250000000 6655901221643 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632617557/5000000000 : ℝ)^2071 ≤ (5331347821567/12500000000000 : ℝ)^1559 := by
    have hnat : (2632617557 : ℕ)^2071*12500000000000^1559 ≤ 5331347821567^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632617557 5000000000 5331347821567 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267172/9765625 : ℝ)^2071 ≤ (44037414975649/100000000000000 : ℝ)^1559 := by
    have hnat : (5267172 : ℕ)^2071*100000000000000^1559 ≤ 44037414975649^1559*9765625^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267172 9765625 44037414975649 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273940447/1250000000 : ℝ), (2632617557/5000000000 : ℝ), (5267172/9765625 : ℝ)] ![(6655901221643/50000000000000 : ℝ), (5331347821567/12500000000000 : ℝ), (44037414975649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273940447/1250000000 : ℝ)|^2071 ≤ (6655901221643/50000000000000 : ℝ)^1559
        have hw : |(-273940447/1250000000 : ℝ)|=(273940447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632617557/5000000000 : ℝ)|^2071 ≤ (5331347821567/12500000000000 : ℝ)^1559
        have hw : |(2632617557/5000000000 : ℝ)|=(2632617557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267172/9765625 : ℝ)|^2071 ≤ (44037414975649/100000000000000 : ℝ)^1559
        have hw : |(5267172/9765625 : ℝ)|=(5267172/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s8_5 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312357599/10000000000 : ℝ)*x 0 + (-2128288003/10000000000 : ℝ)*x 1 + (5393584353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312357599/10000000000 : ℝ)^2071 ≤ (43158600361059/100000000000000 : ℝ)^1559 := by
    have hnat : (5312357599 : ℕ)^2071*100000000000000^1559 ≤ 43158600361059^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312357599 10000000000 43158600361059 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128288003/10000000000 : ℝ)^2071 ≤ (3200995554127/25000000000000 : ℝ)^1559 := by
    have hnat : (2128288003 : ℕ)^2071*25000000000000^1559 ≤ 3200995554127^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128288003 10000000000 3200995554127 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393584353/10000000000 : ℝ)^2071 ≤ (44037417416049/100000000000000 : ℝ)^1559 := by
    have hnat : (5393584353 : ℕ)^2071*100000000000000^1559 ≤ 44037417416049^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393584353 10000000000 44037417416049 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312357599/10000000000 : ℝ), (-2128288003/10000000000 : ℝ), (5393584353/10000000000 : ℝ)] ![(43158600361059/100000000000000 : ℝ), (3200995554127/25000000000000 : ℝ), (44037417416049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312357599/10000000000 : ℝ)|^2071 ≤ (43158600361059/100000000000000 : ℝ)^1559
        have hw : |(5312357599/10000000000 : ℝ)|=(5312357599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2128288003/10000000000 : ℝ)|^2071 ≤ (3200995554127/25000000000000 : ℝ)^1559
        have hw : |(-2128288003/10000000000 : ℝ)|=(2128288003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393584353/10000000000 : ℝ)|^2071 ≤ (44037417416049/100000000000000 : ℝ)^1559
        have hw : |(5393584353/10000000000 : ℝ)|=(5393584353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s8_6 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656178761/5000000000 : ℝ)*x 0 + (1078716909/2000000000 : ℝ)*x 1 + (-425657569/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656178761/5000000000 : ℝ)^2071 ≤ (10789649882513/25000000000000 : ℝ)^1559 := by
    have hnat : (2656178761 : ℕ)^2071*25000000000000^1559 ≤ 10789649882513^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656178761 5000000000 10789649882513 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078716909/2000000000 : ℝ)^2071 ≤ (44037419498523/100000000000000 : ℝ)^1559 := by
    have hnat : (1078716909 : ℕ)^2071*100000000000000^1559 ≤ 44037419498523^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078716909 2000000000 44037419498523 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425657569/2000000000 : ℝ)^2071 ≤ (200062202403/1562500000000 : ℝ)^1559 := by
    have hnat : (425657569 : ℕ)^2071*1562500000000^1559 ≤ 200062202403^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425657569 2000000000 200062202403 1562500000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656178761/5000000000 : ℝ), (1078716909/2000000000 : ℝ), (-425657569/2000000000 : ℝ)] ![(10789649882513/25000000000000 : ℝ), (44037419498523/100000000000000 : ℝ), (200062202403/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656178761/5000000000 : ℝ)|^2071 ≤ (10789649882513/25000000000000 : ℝ)^1559
        have hw : |(2656178761/5000000000 : ℝ)|=(2656178761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078716909/2000000000 : ℝ)|^2071 ≤ (44037419498523/100000000000000 : ℝ)^1559
        have hw : |(1078716909/2000000000 : ℝ)|=(1078716909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425657569/2000000000 : ℝ)|^2071 ≤ (200062202403/1562500000000 : ℝ)^1559
        have hw : |(-425657569/2000000000 : ℝ)|=(425657569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s8_7 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4371919591/10000000000 : ℝ)*x 0 + (1125041809/2500000000 : ℝ)*x 1 + (849474273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371919591/10000000000 : ℝ)^2071 ≤ (33316799948813/100000000000000 : ℝ)^1559 := by
    have hnat : (4371919591 : ℕ)^2071*100000000000000^1559 ≤ 33316799948813^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371919591 10000000000 33316799948813 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125041809/2500000000 : ℝ)^2071 ≤ (17310655764127/50000000000000 : ℝ)^1559 := by
    have hnat : (1125041809 : ℕ)^2071*50000000000000^1559 ≤ 17310655764127^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125041809 2500000000 17310655764127 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849474273/2000000000 : ℝ)^2071 ≤ (32061888509063/100000000000000 : ℝ)^1559 := by
    have hnat : (849474273 : ℕ)^2071*100000000000000^1559 ≤ 32061888509063^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849474273 2000000000 32061888509063 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371919591/10000000000 : ℝ), (1125041809/2500000000 : ℝ), (849474273/2000000000 : ℝ)] ![(33316799948813/100000000000000 : ℝ), (17310655764127/50000000000000 : ℝ), (32061888509063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371919591/10000000000 : ℝ)|^2071 ≤ (33316799948813/100000000000000 : ℝ)^1559
        have hw : |(4371919591/10000000000 : ℝ)|=(4371919591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125041809/2500000000 : ℝ)|^2071 ≤ (17310655764127/50000000000000 : ℝ)^1559
        have hw : |(1125041809/2500000000 : ℝ)|=(1125041809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849474273/2000000000 : ℝ)|^2071 ≤ (32061888509063/100000000000000 : ℝ)^1559
        have hw : |(849474273/2000000000 : ℝ)|=(849474273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1091_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5643/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7009/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2821/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2821/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2821/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2821/25000 : ℝ) ^ (8283/2048 : ℝ) ≤ (14714646704883011/100000000000000000000 : ℝ) := by
    have hpowers : (2821/25000 : ℝ)^8283 ≤ (14714646704883011/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2821 : ℕ)^8283*100000000000000000000^2048 ≤ 14714646704883011^2048*25000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 25000 14714646704883011 100000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/25000 : ℝ)) (X := (14714646704883011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (701/5000 : ℝ) ^ (8283/2048 : ℝ) ≤ (7081234850063299/20000000000000000000 : ℝ) := by
    have hpowers : (701/5000 : ℝ)^8283 ≤ (7081234850063299/20000000000000000000 : ℝ)^2048 := by
      have hnat : (701 : ℕ)^8283*20000000000000000000^2048 ≤ 7081234850063299^2048*5000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 5000 7081234850063299 20000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/5000 : ℝ)) (X := (7081234850063299/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014714646704883011/50000000000000000000 : ℝ) ≤ (10000727568733217/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (50014714646704883011/50000000000000000000 : ℝ)^2048 ≤ (10000727568733217/10000000000000000 : ℝ)^8283 := by
      have hnat : (50014714646704883011 : ℕ)^2048*10000000000000000^8283 ≤ 10000727568733217^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014714646704883011 50000000000000000000 10000727568733217 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000727568733217/10000000000000000 : ℝ)) (X := (50014714646704883011/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025060410477599753/50000000000000000000 : ℝ) ≤ (10001239020686093/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (50025060410477599753/50000000000000000000 : ℝ)^2048 ≤ (10001239020686093/10000000000000000 : ℝ)^8283 := by
      have hnat : (50025060410477599753 : ℕ)^2048*10000000000000000^8283 ≤ 10001239020686093^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025060410477599753 50000000000000000000 10001239020686093 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001239020686093/10000000000000000 : ℝ)) (X := (50025060410477599753/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007081234850063299/10000000000000000000 : ℝ) ≤ (10001750472638969/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (10007081234850063299/10000000000000000000 : ℝ)^2048 ≤ (10001750472638969/10000000000000000 : ℝ)^8283 := by
      have hnat : (10007081234850063299 : ℕ)^2048*10000000000000000^8283 ≤ 10001750472638969^8283*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007081234850063299 10000000000000000000 10001750472638969 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001750472638969/10000000000000000 : ℝ)) (X := (10007081234850063299/10000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14714646704883011/100000000000000000000 : ℝ) ≤ ((189933667919316501/190000000000000000 : ℝ)+2*(14206998691/7600000000000 : ℝ)*(2821/25000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (189933667919316501/190000000000000000 : ℝ)+2*(14206998691/7600000000000 : ℝ)*(2821/25000 : ℝ)=(10000727568733217/10000000000000000 : ℝ) by norm_num, show 1+2*(14714646704883011/100000000000000000000 : ℝ)=(50014714646704883011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7081234850063299/20000000000000000000 : ℝ)+(14714646704883011/100000000000000000000 : ℝ) ≤ ((189933667919316501/190000000000000000 : ℝ)+(14206998691/7600000000000 : ℝ)*((701/5000 : ℝ)+(2821/25000 : ℝ)))^(8283/2048 : ℝ) := by
    rw [show (189933667919316501/190000000000000000 : ℝ)+(14206998691/7600000000000 : ℝ)*((701/5000 : ℝ)+(2821/25000 : ℝ))=(10001239020686093/10000000000000000 : ℝ) by norm_num, show 1+(7081234850063299/20000000000000000000 : ℝ)+(14714646704883011/100000000000000000000 : ℝ)=(50025060410477599753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7081234850063299/20000000000000000000 : ℝ) ≤ ((189933667919316501/190000000000000000 : ℝ)+2*(14206998691/7600000000000 : ℝ)*(701/5000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (189933667919316501/190000000000000000 : ℝ)+2*(14206998691/7600000000000 : ℝ)*(701/5000 : ℝ)=(10001750472638969/10000000000000000 : ℝ) by norm_num, show 1+2*(7081234850063299/20000000000000000000 : ℝ)=(10007081234850063299/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (189933667919316501/190000000000000000 : ℝ)*(X 1 0+X 2 0)+(14206998691/7600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (189933667919316501/190000000000000000 : ℝ)) (alpha := (14206998691/7600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (189933667919316501/190000000000000000 : ℝ)*(X 0 1+X 2 1)+(14206998691/7600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (189933667919316501/190000000000000000 : ℝ)) (alpha := (14206998691/7600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (189933667919316501/190000000000000000 : ℝ)*(X 0 2+X 1 2)+(14206998691/7600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (2821/25000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (189933667919316501/190000000000000000 : ℝ)) (alpha := (14206998691/7600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2191518717/10000000000 : ℝ)*X 0 0+(5393908373/10000000000 : ℝ)*X 0 1+(5264911931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668114133/1250000000 : ℝ)*X 1 0+(-1128480417/5000000000 : ℝ)*X 1 1+(5264911901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344913699/10000000000 : ℝ)*X 2 0+(2632455411/5000000000 : ℝ)*X 2 1+(-282120177/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371909111/10000000000 : ℝ)*X 0 0+(4246732997/10000000000 : ℝ)*X 0 1+(1125200987/2500000000 : ℝ)*X 0 2+(4371909111/10000000000 : ℝ)*X 1 0+(4246732997/10000000000 : ℝ)*X 1 1+(1125200987/2500000000 : ℝ)*X 1 2+(4371909111/10000000000 : ℝ)*X 2 0+(4246732997/10000000000 : ℝ)*X 2 1+(1125200987/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-273940447/1250000000 : ℝ)*X 0 0+(2632617557/5000000000 : ℝ)*X 0 1+(5267172/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312357599/10000000000 : ℝ)*X 1 0+(-2128288003/10000000000 : ℝ)*X 1 1+(5393584353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656178761/5000000000 : ℝ)*X 2 0+(1078716909/2000000000 : ℝ)*X 2 1+(-425657569/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371919591/10000000000 : ℝ)*X 0 0+(1125041809/2500000000 : ℝ)*X 0 1+(849474273/2000000000 : ℝ)*X 0 2+(4371919591/10000000000 : ℝ)*X 1 0+(1125041809/2500000000 : ℝ)*X 1 1+(849474273/2000000000 : ℝ)*X 1 2+(4371919591/10000000000 : ℝ)*X 2 0+(1125041809/2500000000 : ℝ)*X 2 1+(849474273/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (185200178675722435983/38000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130389603/50000000000000 : ℝ)*(base19) + (1851428463/100000000000000 : ℝ)*(base23) + (201312449/50000000000000 : ℝ)*(upper2) + (100224807/100000000000000 : ℝ)*(upper3) + (241461201/100000000000000 : ℝ)*(upper5) + (584403172196721/10000000000000 : ℝ)*(major0) + (584403172196721/10000000000000 : ℝ)*(major1) + (584403172196721/10000000000000 : ℝ)*(major2) + (7752148090717951/100000000000000 : ℝ)*(sp0) + (1550429565987749/20000000000000 : ℝ)*(sp1) + (60563535232779/781250000000 : ℝ)*(sp2) + (1967956462819469/50000000000000 : ℝ)*(sp3) + (858093361/6250000000000 : ℝ)*(sp6) + (566280307/25000000000000 : ℝ)*(sp7) + (1967957595380083/50000000000000 : ℝ)*(f.failure) + (7752148090717951/100000000000000 : ℝ)*(f.sum) + (67377921751/38000000000000000000000000 : ℝ)*base66 + (18940543576368221/1900000000000000000000000000000 : ℝ)*base67 + (13760185628831779/1900000000000000000000000000000 : ℝ)*base70 + (27499321901268221/1900000000000000000000000000000 : ℝ)*base71 + (196762475021/38000000000000000000000000 : ℝ)*base74 + (17704074270431779/1900000000000000000000000000000 : ℝ)*base76 + (7604654550731779/1900000000000000000000000000000 : ℝ)*base78 + (6505075000468221/1900000000000000000000000000000 : ℝ)*base79 + (24922776801/7600000000000000000000000 : ℝ)*base82 + (501609/1000000000000000000000 : ℝ)*base89 + (501609/1000000000000000000000 : ℝ)*base91 + (501609/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5814367304230950885698889/2375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13835821/1250000000000 : ℝ)*(base19) + (1240341879/100000000000000 : ℝ)*(base23) + (383888137/100000000000000 : ℝ)*(lower1) + (2507183/4000000000000 : ℝ)*(upper2) + (18830157/6250000000000 : ℝ)*(upper3) + (85577303/100000000000000 : ℝ)*(upper5) + (1468370402068463/25000000000000 : ℝ)*(major0) + (1468370402068463/25000000000000 : ℝ)*(major1) + (1468370402068463/25000000000000 : ℝ)*(major2) + (20954576551/100000000000000 : ℝ)*(sp2) + (1947803412051001/25000000000000 : ℝ)*(sp4) + (1947803135334581/25000000000000 : ℝ)*(sp5) + (311647658131423/4000000000000 : ℝ)*(sp6) + (1977874743369267/50000000000000 : ℝ)*(sp7) + (1977874743369267/50000000000000 : ℝ)*(f.failure) + (1947803412051001/25000000000000 : ℝ)*(f.sum) + (614299359383/95000000000000000000000000 : ℝ)*base65 + (3822727164067037/4750000000000000000000000000000 : ℝ)*base68 + (66999907138567037/4750000000000000000000000000000 : ℝ)*base70 + (13829815683432963/4750000000000000000000000000000 : ℝ)*base71 + (233679601993/95000000000000000000000000 : ℝ)*base73 + (83455412526432963/4750000000000000000000000000000 : ℝ)*base75 + (506127125817037/4750000000000000000000000000000 : ℝ)*base78 + (78314967158817037/4750000000000000000000000000000 : ℝ)*base80 + (27372210367/5937500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6601559/1000000000000000000000 : ℝ)*base90 + (6601559/1000000000000000000000 : ℝ)*base92 + (6601559/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1091_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1091_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1091_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1091_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1091_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1091_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1091_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

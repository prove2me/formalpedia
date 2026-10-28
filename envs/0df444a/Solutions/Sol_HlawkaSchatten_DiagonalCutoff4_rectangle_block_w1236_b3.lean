-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1236_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:17:15.130295+00:00
-- url     : https://prove2.me/submissions/7d73fda5-7724-4b9e-b178-b704c0e5ab1b

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
theorem support_rectangle_w1236_box_0 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-399769359/2000000000 : ℝ)*x 0 + (4199167/7812500 : ℝ)*x 1 + (1074986763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399769359/2000000000 : ℝ)^8429 ≤ (5961186616499/50000000000000 : ℝ)^6381 := by
    have hnat : (399769359 : ℕ)^8429*50000000000000^6381 ≤ 5961186616499^6381*2000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399769359 2000000000 5961186616499 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4199167/7812500 : ℝ)^8429 ≤ (44038813076071/100000000000000 : ℝ)^6381 := by
    have hnat : (4199167 : ℕ)^8429*100000000000000^6381 ≤ 44038813076071^6381*7812500^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199167 7812500 44038813076071 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074986763/2000000000 : ℝ)^8429 ≤ (22019406835669/50000000000000 : ℝ)^6381 := by
    have hnat : (1074986763 : ℕ)^8429*50000000000000^6381 ≤ 22019406835669^6381*2000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074986763 2000000000 22019406835669 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399769359/2000000000 : ℝ), (4199167/7812500 : ℝ), (1074986763/2000000000 : ℝ)] ![(5961186616499/50000000000000 : ℝ), (44038813076071/100000000000000 : ℝ), (22019406835669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399769359/2000000000 : ℝ)|^8429 ≤ (5961186616499/50000000000000 : ℝ)^6381
        have hw : |(-399769359/2000000000 : ℝ)|=(399769359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4199167/7812500 : ℝ)|^8429 ≤ (44038813076071/100000000000000 : ℝ)^6381
        have hw : |(4199167/7812500 : ℝ)|=(4199167/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1074986763/2000000000 : ℝ)|^8429 ≤ (22019406835669/50000000000000 : ℝ)^6381
        have hw : |(1074986763/2000000000 : ℝ)|=(1074986763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_1 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648376721/5000000000 : ℝ)*x 0 + (-263136679/1250000000 : ℝ)*x 1 + (5374933399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648376721/5000000000 : ℝ)^8429 ≤ (21597322469577/50000000000000 : ℝ)^6381 := by
    have hnat : (2648376721 : ℕ)^8429*50000000000000^6381 ≤ 21597322469577^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648376721 5000000000 21597322469577 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263136679/1250000000 : ℝ)^8429 ≤ (12766545875109/100000000000000 : ℝ)^6381 := by
    have hnat : (263136679 : ℕ)^8429*100000000000000^6381 ≤ 12766545875109^6381*1250000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263136679 1250000000 12766545875109 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374933399/10000000000 : ℝ)^8429 ≤ (11009702292237/25000000000000 : ℝ)^6381 := by
    have hnat : (5374933399 : ℕ)^8429*25000000000000^6381 ≤ 11009702292237^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374933399 10000000000 11009702292237 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648376721/5000000000 : ℝ), (-263136679/1250000000 : ℝ), (5374933399/10000000000 : ℝ)] ![(21597322469577/50000000000000 : ℝ), (12766545875109/100000000000000 : ℝ), (11009702292237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648376721/5000000000 : ℝ)|^8429 ≤ (21597322469577/50000000000000 : ℝ)^6381
        have hw : |(2648376721/5000000000 : ℝ)|=(2648376721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263136679/1250000000 : ℝ)|^8429 ≤ (12766545875109/100000000000000 : ℝ)^6381
        have hw : |(-263136679/1250000000 : ℝ)|=(263136679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374933399/10000000000 : ℝ)|^8429 ≤ (11009702292237/25000000000000 : ℝ)^6381
        have hw : |(5374933399/10000000000 : ℝ)|=(5374933399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_2 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (264837649/500000000 : ℝ)*x 0 + (5374933527/10000000000 : ℝ)*x 1 + (-2105093881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264837649/500000000 : ℝ)^8429 ≤ (43194639962363/100000000000000 : ℝ)^6381 := by
    have hnat : (264837649 : ℕ)^8429*100000000000000^6381 ≤ 43194639962363^6381*500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264837649 500000000 43194639962363 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374933527/10000000000 : ℝ)^8429 ≤ (44038810554299/100000000000000 : ℝ)^6381 := by
    have hnat : (5374933527 : ℕ)^8429*100000000000000^6381 ≤ 44038810554299^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374933527 10000000000 44038810554299 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2105093881/10000000000 : ℝ)^8429 ≤ (1276654947207/10000000000000 : ℝ)^6381 := by
    have hnat : (2105093881 : ℕ)^8429*10000000000000^6381 ≤ 1276654947207^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105093881 10000000000 1276654947207 10000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264837649/500000000 : ℝ), (5374933527/10000000000 : ℝ), (-2105093881/10000000000 : ℝ)] ![(43194639962363/100000000000000 : ℝ), (44038810554299/100000000000000 : ℝ), (1276654947207/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264837649/500000000 : ℝ)|^8429 ≤ (43194639962363/100000000000000 : ℝ)^6381
        have hw : |(264837649/500000000 : ℝ)|=(264837649/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374933527/10000000000 : ℝ)|^8429 ≤ (44038810554299/100000000000000 : ℝ)^6381
        have hw : |(5374933527/10000000000 : ℝ)|=(5374933527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2105093881/10000000000 : ℝ)|^8429 ≤ (1276654947207/10000000000000 : ℝ)^6381
        have hw : |(-2105093881/10000000000 : ℝ)|=(2105093881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_3 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2229092703/5000000000 : ℝ)*x 0 + (4300351269/10000000000 : ℝ)*x 1 + (1075087681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2229092703/5000000000 : ℝ)^8429 ≤ (17199841240421/50000000000000 : ℝ)^6381 := by
    have hnat : (2229092703 : ℕ)^8429*50000000000000^6381 ≤ 17199841240421^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229092703 5000000000 17199841240421 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4300351269/10000000000 : ℝ)^8429 ≤ (32800161499047/100000000000000 : ℝ)^6381 := by
    have hnat : (4300351269 : ℕ)^8429*100000000000000^6381 ≤ 32800161499047^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300351269 10000000000 32800161499047 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075087681/2500000000 : ℝ)^8429 ≤ (32800156007991/100000000000000 : ℝ)^6381 := by
    have hnat : (1075087681 : ℕ)^8429*100000000000000^6381 ≤ 32800156007991^6381*2500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075087681 2500000000 32800156007991 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2229092703/5000000000 : ℝ), (4300351269/10000000000 : ℝ), (1075087681/2500000000 : ℝ)] ![(17199841240421/50000000000000 : ℝ), (32800161499047/100000000000000 : ℝ), (32800156007991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2229092703/5000000000 : ℝ)|^8429 ≤ (17199841240421/50000000000000 : ℝ)^6381
        have hw : |(2229092703/5000000000 : ℝ)|=(2229092703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4300351269/10000000000 : ℝ)|^8429 ≤ (32800161499047/100000000000000 : ℝ)^6381
        have hw : |(4300351269/10000000000 : ℝ)|=(4300351269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075087681/2500000000 : ℝ)|^8429 ≤ (32800156007991/100000000000000 : ℝ)^6381
        have hw : |(1075087681/2500000000 : ℝ)|=(1075087681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_4 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1123996519/5000000000 : ℝ)*x 0 + (5282223829/10000000000 : ℝ)*x 1 + (2641111931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123996519/5000000000 : ℝ)^8429 ≤ (3480901467081/25000000000000 : ℝ)^6381 := by
    have hnat : (1123996519 : ℕ)^8429*25000000000000^6381 ≤ 3480901467081^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123996519 5000000000 3480901467081 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282223829/10000000000 : ℝ)^8429 ≤ (43038196884513/100000000000000 : ℝ)^6381 := by
    have hnat : (5282223829 : ℕ)^8429*100000000000000^6381 ≤ 43038196884513^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282223829 10000000000 43038196884513 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641111931/5000000000 : ℝ)^8429 ≤ (10759549309921/25000000000000 : ℝ)^6381 := by
    have hnat : (2641111931 : ℕ)^8429*25000000000000^6381 ≤ 10759549309921^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641111931 5000000000 10759549309921 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1123996519/5000000000 : ℝ), (5282223829/10000000000 : ℝ), (2641111931/5000000000 : ℝ)] ![(3480901467081/25000000000000 : ℝ), (43038196884513/100000000000000 : ℝ), (10759549309921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1123996519/5000000000 : ℝ)|^8429 ≤ (3480901467081/25000000000000 : ℝ)^6381
        have hw : |(-1123996519/5000000000 : ℝ)|=(1123996519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282223829/10000000000 : ℝ)|^8429 ≤ (43038196884513/100000000000000 : ℝ)^6381
        have hw : |(5282223829/10000000000 : ℝ)|=(5282223829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641111931/5000000000 : ℝ)|^8429 ≤ (10759549309921/25000000000000 : ℝ)^6381
        have hw : |(2641111931/5000000000 : ℝ)|=(2641111931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_5 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362115679/10000000000 : ℝ)*x 0 + (-2141830317/10000000000 : ℝ)*x 1 + (5282223817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362115679/10000000000 : ℝ)^8429 ≤ (8780027084631/20000000000000 : ℝ)^6381 := by
    have hnat : (5362115679 : ℕ)^8429*20000000000000^6381 ≤ 8780027084631^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362115679 10000000000 8780027084631 20000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141830317/10000000000 : ℝ)^8429 ≤ (13061667800731/100000000000000 : ℝ)^6381 := by
    have hnat : (2141830317 : ℕ)^8429*100000000000000^6381 ≤ 13061667800731^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141830317 10000000000 13061667800731 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282223817/10000000000 : ℝ)^8429 ≤ (43038196755359/100000000000000 : ℝ)^6381 := by
    have hnat : (5282223817 : ℕ)^8429*100000000000000^6381 ≤ 43038196755359^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282223817 10000000000 43038196755359 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362115679/10000000000 : ℝ), (-2141830317/10000000000 : ℝ), (5282223817/10000000000 : ℝ)] ![(8780027084631/20000000000000 : ℝ), (13061667800731/100000000000000 : ℝ), (43038196755359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362115679/10000000000 : ℝ)|^8429 ≤ (8780027084631/20000000000000 : ℝ)^6381
        have hw : |(5362115679/10000000000 : ℝ)|=(5362115679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141830317/10000000000 : ℝ)|^8429 ≤ (13061667800731/100000000000000 : ℝ)^6381
        have hw : |(-2141830317/10000000000 : ℝ)|=(2141830317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282223817/10000000000 : ℝ)|^8429 ≤ (43038196755359/100000000000000 : ℝ)^6381
        have hw : |(5282223817/10000000000 : ℝ)|=(5282223817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_6 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335132227/625000000 : ℝ)*x 0 + (2641111933/5000000000 : ℝ)*x 1 + (-1070915157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335132227/625000000 : ℝ)^8429 ≤ (43900134914861/100000000000000 : ℝ)^6381 := by
    have hnat : (335132227 : ℕ)^8429*100000000000000^6381 ≤ 43900134914861^6381*625000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335132227 625000000 43900134914861 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641111933/5000000000 : ℝ)^8429 ≤ (2689887330171/6250000000000 : ℝ)^6381 := by
    have hnat : (2641111933 : ℕ)^8429*6250000000000^6381 ≤ 2689887330171^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641111933 5000000000 2689887330171 6250000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1070915157/5000000000 : ℝ)^8429 ≤ (3265416944141/25000000000000 : ℝ)^6381 := by
    have hnat : (1070915157 : ℕ)^8429*25000000000000^6381 ≤ 3265416944141^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070915157 5000000000 3265416944141 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335132227/625000000 : ℝ), (2641111933/5000000000 : ℝ), (-1070915157/5000000000 : ℝ)] ![(43900134914861/100000000000000 : ℝ), (2689887330171/6250000000000 : ℝ), (3265416944141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335132227/625000000 : ℝ)|^8429 ≤ (43900134914861/100000000000000 : ℝ)^6381
        have hw : |(335132227/625000000 : ℝ)|=(335132227/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641111933/5000000000 : ℝ)|^8429 ≤ (2689887330171/6250000000000 : ℝ)^6381
        have hw : |(2641111933/5000000000 : ℝ)|=(2641111933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1070915157/5000000000 : ℝ)|^8429 ≤ (3265416944141/25000000000000 : ℝ)^6381
        have hw : |(-1070915157/5000000000 : ℝ)|=(1070915157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_7 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4244611727/10000000000 : ℝ)*x 0 + (4407117641/10000000000 : ℝ)*x 1 + (2203558871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244611727/10000000000 : ℝ)^8429 ≤ (32239738698109/100000000000000 : ℝ)^6381 := by
    have hnat : (4244611727 : ℕ)^8429*100000000000000^6381 ≤ 32239738698109^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244611727 10000000000 32239738698109 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4407117641/10000000000 : ℝ)^8429 ≤ (16940065063489/50000000000000 : ℝ)^6381 := by
    have hnat : (4407117641 : ℕ)^8429*50000000000000^6381 ≤ 16940065063489^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407117641 10000000000 16940065063489 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203558871/5000000000 : ℝ)^8429 ≤ (8470032788157/25000000000000 : ℝ)^6381 := by
    have hnat : (2203558871 : ℕ)^8429*25000000000000^6381 ≤ 8470032788157^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203558871 5000000000 8470032788157 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244611727/10000000000 : ℝ), (4407117641/10000000000 : ℝ), (2203558871/5000000000 : ℝ)] ![(32239738698109/100000000000000 : ℝ), (16940065063489/50000000000000 : ℝ), (8470032788157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244611727/10000000000 : ℝ)|^8429 ≤ (32239738698109/100000000000000 : ℝ)^6381
        have hw : |(4244611727/10000000000 : ℝ)|=(4244611727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4407117641/10000000000 : ℝ)|^8429 ≤ (16940065063489/50000000000000 : ℝ)^6381
        have hw : |(4407117641/10000000000 : ℝ)|=(4407117641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203558871/5000000000 : ℝ)|^8429 ≤ (8470032788157/25000000000000 : ℝ)^6381
        have hw : |(2203558871/5000000000 : ℝ)|=(2203558871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_8 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219579103/1000000000 : ℝ)*x 0 + (5218996853/10000000000 : ℝ)*x 1 + (1346136723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219579103/1000000000 : ℝ)^8429 ≤ (674905212089/5000000000000 : ℝ)^6381 := by
    have hnat : (219579103 : ℕ)^8429*5000000000000^6381 ≤ 674905212089^6381*1000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219579103 1000000000 674905212089 5000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218996853/10000000000 : ℝ)^8429 ≤ (5294876172193/12500000000000 : ℝ)^6381 := by
    have hnat : (5218996853 : ℕ)^8429*12500000000000^6381 ≤ 5294876172193^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218996853 10000000000 5294876172193 12500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346136723/2500000000 : ℝ)^8429 ≤ (44142886366171/100000000000000 : ℝ)^6381 := by
    have hnat : (1346136723 : ℕ)^8429*100000000000000^6381 ≤ 44142886366171^6381*2500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346136723 2500000000 44142886366171 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219579103/1000000000 : ℝ), (5218996853/10000000000 : ℝ), (1346136723/2500000000 : ℝ)] ![(674905212089/5000000000000 : ℝ), (5294876172193/12500000000000 : ℝ), (44142886366171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219579103/1000000000 : ℝ)|^8429 ≤ (674905212089/5000000000000 : ℝ)^6381
        have hw : |(-219579103/1000000000 : ℝ)|=(219579103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218996853/10000000000 : ℝ)|^8429 ≤ (5294876172193/12500000000000 : ℝ)^6381
        have hw : |(5218996853/10000000000 : ℝ)|=(5218996853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346136723/2500000000 : ℝ)|^8429 ≤ (44142886366171/100000000000000 : ℝ)^6381
        have hw : |(1346136723/2500000000 : ℝ)|=(1346136723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_9 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289972629/10000000000 : ℝ)*x 0 + (-2626521/12500000 : ℝ)*x 1 + (215381873/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289972629/10000000000 : ℝ)^8429 ≤ (21560807581313/50000000000000 : ℝ)^6381 := by
    have hnat : (5289972629 : ℕ)^8429*50000000000000^6381 ≤ 21560807581313^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289972629 10000000000 21560807581313 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626521/12500000 : ℝ)^8429 ≤ (6367749585521/50000000000000 : ℝ)^6381 := by
    have hnat : (2626521 : ℕ)^8429*50000000000000^6381 ≤ 6367749585521^6381*12500000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626521 12500000 6367749585521 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215381873/400000000 : ℝ)^8429 ≤ (4414288564061/10000000000000 : ℝ)^6381 := by
    have hnat : (215381873 : ℕ)^8429*10000000000000^6381 ≤ 4414288564061^6381*400000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215381873 400000000 4414288564061 10000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289972629/10000000000 : ℝ), (-2626521/12500000 : ℝ), (215381873/400000000 : ℝ)] ![(21560807581313/50000000000000 : ℝ), (6367749585521/50000000000000 : ℝ), (4414288564061/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289972629/10000000000 : ℝ)|^8429 ≤ (21560807581313/50000000000000 : ℝ)^6381
        have hw : |(5289972629/10000000000 : ℝ)|=(5289972629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2626521/12500000 : ℝ)|^8429 ≤ (6367749585521/50000000000000 : ℝ)^6381
        have hw : |(-2626521/12500000 : ℝ)|=(2626521/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215381873/400000000 : ℝ)|^8429 ≤ (4414288564061/10000000000000 : ℝ)^6381
        have hw : |(215381873/400000000 : ℝ)|=(215381873/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_10 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289972609/10000000000 : ℝ)*x 0 + (5384546931/10000000000 : ℝ)*x 1 + (-420243337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289972609/10000000000 : ℝ)^8429 ≤ (43121614947269/100000000000000 : ℝ)^6381 := by
    have hnat : (5289972609 : ℕ)^8429*100000000000000^6381 ≤ 43121614947269^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289972609 10000000000 43121614947269 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384546931/10000000000 : ℝ)^8429 ≤ (1379465212141/3125000000000 : ℝ)^6381 := by
    have hnat : (5384546931 : ℕ)^8429*3125000000000^6381 ≤ 1379465212141^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384546931 10000000000 1379465212141 3125000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420243337/2000000000 : ℝ)^8429 ≤ (3183874562579/25000000000000 : ℝ)^6381 := by
    have hnat : (420243337 : ℕ)^8429*25000000000000^6381 ≤ 3183874562579^6381*2000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420243337 2000000000 3183874562579 25000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289972609/10000000000 : ℝ), (5384546931/10000000000 : ℝ), (-420243337/2000000000 : ℝ)] ![(43121614947269/100000000000000 : ℝ), (1379465212141/3125000000000 : ℝ), (3183874562579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289972609/10000000000 : ℝ)|^8429 ≤ (43121614947269/100000000000000 : ℝ)^6381
        have hw : |(5289972609/10000000000 : ℝ)|=(5289972609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384546931/10000000000 : ℝ)|^8429 ≤ (1379465212141/3125000000000 : ℝ)^6381
        have hw : |(5384546931/10000000000 : ℝ)|=(5384546931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420243337/2000000000 : ℝ)|^8429 ≤ (3183874562579/25000000000000 : ℝ)^6381
        have hw : |(-420243337/2000000000 : ℝ)|=(420243337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_11 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (560007357/1250000000 : ℝ)*x 0 + (4289273681/10000000000 : ℝ)*x 1 + (268079611/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560007357/1250000000 : ℝ)^8429 ≤ (17311402225369/50000000000000 : ℝ)^6381 := by
    have hnat : (560007357 : ℕ)^8429*50000000000000^6381 ≤ 17311402225369^6381*1250000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560007357 1250000000 17311402225369 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4289273681/10000000000 : ℝ)^8429 ≤ (32688597288579/100000000000000 : ℝ)^6381 := by
    have hnat : (4289273681 : ℕ)^8429*100000000000000^6381 ≤ 32688597288579^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289273681 10000000000 32688597288579 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268079611/625000000 : ℝ)^8429 ≤ (2043037390309/6250000000000 : ℝ)^6381 := by
    have hnat : (268079611 : ℕ)^8429*6250000000000^6381 ≤ 2043037390309^6381*625000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268079611 625000000 2043037390309 6250000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(560007357/1250000000 : ℝ), (4289273681/10000000000 : ℝ), (268079611/625000000 : ℝ)] ![(17311402225369/50000000000000 : ℝ), (32688597288579/100000000000000 : ℝ), (2043037390309/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(560007357/1250000000 : ℝ)|^8429 ≤ (17311402225369/50000000000000 : ℝ)^6381
        have hw : |(560007357/1250000000 : ℝ)|=(560007357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4289273681/10000000000 : ℝ)|^8429 ≤ (32688597288579/100000000000000 : ℝ)^6381
        have hw : |(4289273681/10000000000 : ℝ)|=(4289273681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(268079611/625000000 : ℝ)|^8429 ≤ (2043037390309/6250000000000 : ℝ)^6381
        have hw : |(268079611/625000000 : ℝ)|=(268079611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_12 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1025655979/5000000000 : ℝ)*x 0 + (271847407/500000000 : ℝ)*x 1 + (5274146699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025655979/5000000000 : ℝ)^8429 ≤ (12337476644681/100000000000000 : ℝ)^6381 := by
    have hnat : (1025655979 : ℕ)^8429*100000000000000^6381 ≤ 12337476644681^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025655979 5000000000 12337476644681 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271847407/500000000 : ℝ)^8429 ≤ (44711237506301/100000000000000 : ℝ)^6381 := by
    have hnat : (271847407 : ℕ)^8429*100000000000000^6381 ≤ 44711237506301^6381*500000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271847407 500000000 44711237506301 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274146699/10000000000 : ℝ)^8429 ≤ (42951285827919/100000000000000 : ℝ)^6381 := by
    have hnat : (5274146699 : ℕ)^8429*100000000000000^6381 ≤ 42951285827919^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274146699 10000000000 42951285827919 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1025655979/5000000000 : ℝ), (271847407/500000000 : ℝ), (5274146699/10000000000 : ℝ)] ![(12337476644681/100000000000000 : ℝ), (44711237506301/100000000000000 : ℝ), (42951285827919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1025655979/5000000000 : ℝ)|^8429 ≤ (12337476644681/100000000000000 : ℝ)^6381
        have hw : |(-1025655979/5000000000 : ℝ)|=(1025655979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271847407/500000000 : ℝ)|^8429 ≤ (44711237506301/100000000000000 : ℝ)^6381
        have hw : |(271847407/500000000 : ℝ)|=(271847407/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274146699/10000000000 : ℝ)|^8429 ≤ (42951285827919/100000000000000 : ℝ)^6381
        have hw : |(5274146699/10000000000 : ℝ)|=(5274146699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_13 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683904153/5000000000 : ℝ)*x 0 + (-1072487497/5000000000 : ℝ)*x 1 + (5274146479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683904153/5000000000 : ℝ)^8429 ≤ (43961710318773/100000000000000 : ℝ)^6381 := by
    have hnat : (2683904153 : ℕ)^8429*100000000000000^6381 ≤ 43961710318773^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683904153 5000000000 43961710318773 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072487497/5000000000 : ℝ)^8429 ≤ (13087006201799/100000000000000 : ℝ)^6381 := by
    have hnat : (1072487497 : ℕ)^8429*100000000000000^6381 ≤ 13087006201799^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072487497 5000000000 13087006201799 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274146479/10000000000 : ℝ)^8429 ≤ (42951283461269/100000000000000 : ℝ)^6381 := by
    have hnat : (5274146479 : ℕ)^8429*100000000000000^6381 ≤ 42951283461269^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274146479 10000000000 42951283461269 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683904153/5000000000 : ℝ), (-1072487497/5000000000 : ℝ), (5274146479/10000000000 : ℝ)] ![(43961710318773/100000000000000 : ℝ), (13087006201799/100000000000000 : ℝ), (42951283461269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683904153/5000000000 : ℝ)|^8429 ≤ (43961710318773/100000000000000 : ℝ)^6381
        have hw : |(2683904153/5000000000 : ℝ)|=(2683904153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072487497/5000000000 : ℝ)|^8429 ≤ (13087006201799/100000000000000 : ℝ)^6381
        have hw : |(-1072487497/5000000000 : ℝ)|=(1072487497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274146479/10000000000 : ℝ)|^8429 ≤ (42951283461269/100000000000000 : ℝ)^6381
        have hw : |(5274146479/10000000000 : ℝ)|=(5274146479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_14 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683904177/5000000000 : ℝ)*x 0 + (1054829327/2000000000 : ℝ)*x 1 + (-2144974723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683904177/5000000000 : ℝ)^8429 ≤ (43961710838059/100000000000000 : ℝ)^6381 := by
    have hnat : (2683904177 : ℕ)^8429*100000000000000^6381 ≤ 43961710838059^6381*5000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683904177 5000000000 43961710838059 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054829327/2000000000 : ℝ)^8429 ≤ (42951285139439/100000000000000 : ℝ)^6381 := by
    have hnat : (1054829327 : ℕ)^8429*100000000000000^6381 ≤ 42951285139439^6381*2000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054829327 2000000000 42951285139439 100000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2144974723/10000000000 : ℝ)^8429 ≤ (1635875502211/12500000000000 : ℝ)^6381 := by
    have hnat : (2144974723 : ℕ)^8429*12500000000000^6381 ≤ 1635875502211^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144974723 10000000000 1635875502211 12500000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683904177/5000000000 : ℝ), (1054829327/2000000000 : ℝ), (-2144974723/10000000000 : ℝ)] ![(43961710838059/100000000000000 : ℝ), (42951285139439/100000000000000 : ℝ), (1635875502211/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683904177/5000000000 : ℝ)|^8429 ≤ (43961710838059/100000000000000 : ℝ)^6381
        have hw : |(2683904177/5000000000 : ℝ)|=(2683904177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054829327/2000000000 : ℝ)|^8429 ≤ (42951285139439/100000000000000 : ℝ)^6381
        have hw : |(1054829327/2000000000 : ℝ)|=(1054829327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2144974723/10000000000 : ℝ)|^8429 ≤ (1635875502211/12500000000000 : ℝ)^6381
        have hw : |(-2144974723/10000000000 : ℝ)|=(2144974723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1236_box_15 (p : ℝ) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4225772201/10000000000 : ℝ)*x 0 + (4416414353/10000000000 : ℝ)*x 1 + (276025949/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225772201/10000000000 : ℝ)^8429 ≤ (500794564579/1562500000000 : ℝ)^6381 := by
    have hnat : (4225772201 : ℕ)^8429*1562500000000^6381 ≤ 500794564579^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225772201 10000000000 500794564579 1562500000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4416414353/10000000000 : ℝ)^8429 ≤ (16987284852259/50000000000000 : ℝ)^6381 := by
    have hnat : (4416414353 : ℕ)^8429*50000000000000^6381 ≤ 16987284852259^6381*10000000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416414353 10000000000 16987284852259 50000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276025949/625000000 : ℝ)^8429 ≤ (3397457814899/10000000000000 : ℝ)^6381 := by
    have hnat : (276025949 : ℕ)^8429*10000000000000^6381 ≤ 3397457814899^6381*625000000^8429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276025949 625000000 3397457814899 10000000000000 8429 6381 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8429/2048 : ℝ)) 8429 6381 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225772201/10000000000 : ℝ), (4416414353/10000000000 : ℝ), (276025949/625000000 : ℝ)] ![(500794564579/1562500000000 : ℝ), (16987284852259/50000000000000 : ℝ), (3397457814899/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225772201/10000000000 : ℝ)|^8429 ≤ (500794564579/1562500000000 : ℝ)^6381
        have hw : |(4225772201/10000000000 : ℝ)|=(4225772201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4416414353/10000000000 : ℝ)|^8429 ≤ (16987284852259/50000000000000 : ℝ)^6381
        have hw : |(4416414353/10000000000 : ℝ)|=(4416414353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276025949/625000000 : ℝ)|^8429 ≤ (3397457814899/10000000000000 : ℝ)^6381
        have hw : |(276025949/625000000 : ℝ)|=(276025949/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1236_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(31123/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14843/25000 : ℝ) ∧ (80091/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83333/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (717/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (717/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (717/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14101/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (717/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (717/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14101/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (717/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (717/6250 : ℝ) ^ (2107/512 : ℝ) ≤ (13495676429643841/100000000000000000000 : ℝ) := by
    have hpowers : (717/6250 : ℝ)^2107 ≤ (13495676429643841/100000000000000000000 : ℝ)^512 := by
      have hnat : (717 : ℕ)^2107*100000000000000000000^512 ≤ 13495676429643841^512*6250^2107 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        717 6250 13495676429643841 100000000000000000000 2107 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (717/6250 : ℝ)) (X := (13495676429643841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14101/100000 : ℝ) ^ (2107/512 : ℝ) ≤ (15773715376981037/50000000000000000000 : ℝ) := by
    have hpowers : (14101/100000 : ℝ)^2107 ≤ (15773715376981037/50000000000000000000 : ℝ)^512 := by
      have hnat : (14101 : ℕ)^2107*50000000000000000000^512 ≤ 15773715376981037^512*100000^2107 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14101 100000 15773715376981037 50000000000000000000 2107 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14101/100000 : ℝ)) (X := (15773715376981037/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013495676429643841/50000000000000000000 : ℝ) ≤ (10000655821596929/10000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (50013495676429643841/50000000000000000000 : ℝ)^512 ≤ (10000655821596929/10000000000000000 : ℝ)^2107 := by
      have hnat : (50013495676429643841 : ℕ)^512*10000000000000000^2107 ≤ 10000655821596929^2107*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013495676429643841 50000000000000000000 10000655821596929 10000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000655821596929/10000000000000000 : ℝ)) (X := (50013495676429643841/50000000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009008621436721183/20000000000000000000 : ℝ) ≤ (10001094358808847/10000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (20009008621436721183/20000000000000000000 : ℝ)^512 ≤ (10001094358808847/10000000000000000 : ℝ)^2107 := by
      have hnat : (20009008621436721183 : ℕ)^512*10000000000000000^2107 ≤ 10001094358808847^2107*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009008621436721183 20000000000000000000 10001094358808847 10000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001094358808847/10000000000000000 : ℝ)) (X := (20009008621436721183/20000000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015773715376981037/25000000000000000000 : ℝ) ≤ (2000306579204153/2000000000000000 : ℝ) ^ (2107/512 : ℝ) := by
    have hpowers : (25015773715376981037/25000000000000000000 : ℝ)^512 ≤ (2000306579204153/2000000000000000 : ℝ)^2107 := by
      have hnat : (25015773715376981037 : ℕ)^512*2000000000000000^2107 ≤ 2000306579204153^2107*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015773715376981037 25000000000000000000 2000306579204153 2000000000000000 512 2107 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000306579204153/2000000000000000 : ℝ)) (X := (25015773715376981037/25000000000000000000 : ℝ)) (by norm_num) 2107 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13495676429643841/100000000000000000000 : ℝ) ≤ ((109965114465222091/110000000000000000 : ℝ)+2*(219268605959/131450000000000 : ℝ)*(717/6250 : ℝ))^(2107/512 : ℝ) := by
    rw [show (109965114465222091/110000000000000000 : ℝ)+2*(219268605959/131450000000000 : ℝ)*(717/6250 : ℝ)=(10000655821596929/10000000000000000 : ℝ) by norm_num, show 1+2*(13495676429643841/100000000000000000000 : ℝ)=(50013495676429643841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15773715376981037/50000000000000000000 : ℝ)+(13495676429643841/100000000000000000000 : ℝ) ≤ ((109965114465222091/110000000000000000 : ℝ)+(219268605959/131450000000000 : ℝ)*((14101/100000 : ℝ)+(717/6250 : ℝ)))^(2107/512 : ℝ) := by
    rw [show (109965114465222091/110000000000000000 : ℝ)+(219268605959/131450000000000 : ℝ)*((14101/100000 : ℝ)+(717/6250 : ℝ))=(10001094358808847/10000000000000000 : ℝ) by norm_num, show 1+(15773715376981037/50000000000000000000 : ℝ)+(13495676429643841/100000000000000000000 : ℝ)=(20009008621436721183/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15773715376981037/50000000000000000000 : ℝ) ≤ ((109965114465222091/110000000000000000 : ℝ)+2*(219268605959/131450000000000 : ℝ)*(14101/100000 : ℝ))^(2107/512 : ℝ) := by
    rw [show (109965114465222091/110000000000000000 : ℝ)+2*(219268605959/131450000000000 : ℝ)*(14101/100000 : ℝ)=(2000306579204153/2000000000000000 : ℝ) by norm_num, show 1+2*(15773715376981037/50000000000000000000 : ℝ)=(25015773715376981037/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (109965114465222091/110000000000000000 : ℝ)*(X 1 0+X 2 0)+(219268605959/131450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (109965114465222091/110000000000000000 : ℝ)) (alpha := (219268605959/131450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (109965114465222091/110000000000000000 : ℝ)*(X 0 1+X 2 1)+(219268605959/131450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (109965114465222091/110000000000000000 : ℝ)) (alpha := (219268605959/131450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (109965114465222091/110000000000000000 : ℝ)*(X 0 2+X 1 2)+(219268605959/131450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2107/512 : ℝ)) (lo := (717/6250 : ℝ)) (hi := (14101/100000 : ℝ)) (c := (109965114465222091/110000000000000000 : ℝ)) (alpha := (219268605959/131450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-399769359/2000000000 : ℝ)*X 0 0+(4199167/7812500 : ℝ)*X 0 1+(1074986763/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648376721/5000000000 : ℝ)*X 1 0+(-263136679/1250000000 : ℝ)*X 1 1+(5374933399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((264837649/500000000 : ℝ)*X 2 0+(5374933527/10000000000 : ℝ)*X 2 1+(-2105093881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2229092703/5000000000 : ℝ)*X 0 0+(4300351269/10000000000 : ℝ)*X 0 1+(1075087681/2500000000 : ℝ)*X 0 2+(2229092703/5000000000 : ℝ)*X 1 0+(4300351269/10000000000 : ℝ)*X 1 1+(1075087681/2500000000 : ℝ)*X 1 2+(2229092703/5000000000 : ℝ)*X 2 0+(4300351269/10000000000 : ℝ)*X 2 1+(1075087681/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1123996519/5000000000 : ℝ)*X 0 0+(5282223829/10000000000 : ℝ)*X 0 1+(2641111931/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362115679/10000000000 : ℝ)*X 1 0+(-2141830317/10000000000 : ℝ)*X 1 1+(5282223817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((335132227/625000000 : ℝ)*X 2 0+(2641111933/5000000000 : ℝ)*X 2 1+(-1070915157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4244611727/10000000000 : ℝ)*X 0 0+(4407117641/10000000000 : ℝ)*X 0 1+(2203558871/5000000000 : ℝ)*X 0 2+(4244611727/10000000000 : ℝ)*X 1 0+(4407117641/10000000000 : ℝ)*X 1 1+(2203558871/5000000000 : ℝ)*X 1 2+(4244611727/10000000000 : ℝ)*X 2 0+(4407117641/10000000000 : ℝ)*X 2 1+(2203558871/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-219579103/1000000000 : ℝ)*X 0 0+(5218996853/10000000000 : ℝ)*X 0 1+(1346136723/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289972629/10000000000 : ℝ)*X 1 0+(-2626521/12500000 : ℝ)*X 1 1+(215381873/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289972609/10000000000 : ℝ)*X 2 0+(5384546931/10000000000 : ℝ)*X 2 1+(-420243337/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((560007357/1250000000 : ℝ)*X 0 0+(4289273681/10000000000 : ℝ)*X 0 1+(268079611/625000000 : ℝ)*X 0 2+(560007357/1250000000 : ℝ)*X 1 0+(4289273681/10000000000 : ℝ)*X 1 1+(268079611/625000000 : ℝ)*X 1 2+(560007357/1250000000 : ℝ)*X 2 0+(4289273681/10000000000 : ℝ)*X 2 1+(268079611/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1025655979/5000000000 : ℝ)*X 0 0+(271847407/500000000 : ℝ)*X 0 1+(5274146699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683904153/5000000000 : ℝ)*X 1 0+(-1072487497/5000000000 : ℝ)*X 1 1+(5274146479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2683904177/5000000000 : ℝ)*X 2 0+(1054829327/2000000000 : ℝ)*X 2 1+(-2144974723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4225772201/10000000000 : ℝ)*X 0 0+(4416414353/10000000000 : ℝ)*X 0 1+(276025949/625000000 : ℝ)*X 0 2+(4225772201/10000000000 : ℝ)*X 1 0+(4416414353/10000000000 : ℝ)*X 1 1+(276025949/625000000 : ℝ)*X 1 2+(4225772201/10000000000 : ℝ)*X 2 0+(4416414353/10000000000 : ℝ)*X 2 1+(276025949/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1236_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31123/50000 : ℝ) ≤ (-3719020495414616865110117248311/5975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43726183/100000000000000 : ℝ)*(upper0) + (54512627/100000000000000 : ℝ)*(upper1) + (16017137/50000000000000 : ℝ)*(upper2) + (30326151/100000000000000 : ℝ)*(upper3) + (73219389/100000000000000 : ℝ)*(upper5) + (3998193214402953/100000000000000 : ℝ)*(major0) + (3998193214402953/100000000000000 : ℝ)*(major1) + (1999096607201477/50000000000000 : ℝ)*(major2) + (1036198783/100000000000000 : ℝ)*(sp2) + (3215944371/100000000000000 : ℝ)*(sp3) + (5374766813297063/100000000000000 : ℝ)*(sp4) + (5374766813297063/100000000000000 : ℝ)*(sp5) + (134369144427457/2500000000000 : ℝ)*(sp6) + (264236407317897/10000000000000 : ℝ)*(sp7) + (1321183644561671/50000000000000 : ℝ)*(f.failure) + (5374766813297063/100000000000000 : ℝ)*(f.sum) + (8641018410693/1195000000000000000000000000 : ℝ)*base65 + (25443016739478298797/2629000000000000000000000000000000 : ℝ)*base67 + (395998621723154289273/1314500000000000000000000000000000 : ℝ)*base69 + (27268855144165298797/2629000000000000000000000000000000 : ℝ)*base71 + (6062179520373/1195000000000000000000000000 : ℝ)*base73 + (62902176242261789273/1314500000000000000000000000000000 : ℝ)*base75 + (29015388483006498797/2629000000000000000000000000000000 : ℝ)*base77 + (156868791410960498797/2629000000000000000000000000000000 : ℝ)*base79 + (4978650699408709/13145000000000000000000000000 : ℝ)*base81 + (2918191/625000000000000000000 : ℝ)*base90 + (2918191/625000000000000000000 : ℝ)*base92 + (9168191/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (14843/25000 : ℝ) ≤ (780484049920577944089991630845381/1314500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12092201/25000000000000 : ℝ)*(lower0) + (231476769/100000000000000 : ℝ)*(upper1) + (166973761/50000000000000 : ℝ)*(upper2) + (36299/20000000000000 : ℝ)*(upper3) + (12425671/20000000000000 : ℝ)*(lower5) + (4063874066294123/100000000000000 : ℝ)*(major0) + (4063874066294123/100000000000000 : ℝ)*(major1) + (4063874066294123/100000000000000 : ℝ)*(major2) + (5422181344236513/100000000000000 : ℝ)*(sp0) + (2711090362952193/50000000000000 : ℝ)*(sp1) + (677758029968569/12500000000000 : ℝ)*(sp2) + (16786094562053/625000000000 : ℝ)*(sp3) + (309166063/50000000000000 : ℝ)*(sp5) + (2927612199/2500000000000 : ℝ)*(sp10) + (16786094562053/625000000000 : ℝ)*(f.failure) + (5422181344236513/100000000000000 : ℝ)*(f.sum) + (24717634498611/13145000000000000000000000000 : ℝ)*base66 + (32945104665194584873/2629000000000000000000000000000000 : ℝ)*base68 + (43065930776029584873/2629000000000000000000000000000000 : ℝ)*base70 + (3973900733128584873/2629000000000000000000000000000000 : ℝ)*base72 + (909763473779/205390625000000000000000000 : ℝ)*base74 + (2983512655401415127/2629000000000000000000000000000000 : ℝ)*base75 + (12156138337885415127/2629000000000000000000000000000000 : ℝ)*base77 + (44487925772330584873/2629000000000000000000000000000000 : ℝ)*base80 + (89132581227123/6572500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (18553/1953125000000000000 : ℝ)*base89 + (18553/1953125000000000000 : ℝ)*base91 + (18553/1953125000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80091/100000 : ℝ) ≤ (5264150399669354323073225883/6572500000000000000000000000 : ℝ) := by norm_num
    linear_combination (226057/25000000000000 : ℝ)*(lower1) + (15488939/20000000000000 : ℝ)*(lower3) + (2211981/10000000000000 : ℝ)*(upper4) + (4530751901292049/100000000000000 : ℝ)*(major0) + (4530751901292049/100000000000000 : ℝ)*(major1) + (4530751901292049/100000000000000 : ℝ)*(major2) + (36588619/1562500000000 : ℝ)*(sp0) + (19930643357/50000000000000 : ℝ)*(sp1) + (18060945279/20000000000000 : ℝ)*(sp2) + (39482581153/100000000000000 : ℝ)*(sp3) + (3020236709356681/50000000000000 : ℝ)*(sp8) + (755054487387283/12500000000000 : ℝ)*(sp9) + (6040385455658583/100000000000000 : ℝ)*(sp10) + (748572675089389/25000000000000 : ℝ)*(sp11) + (2994330182938709/100000000000000 : ℝ)*(f.failure) + (3020237880192489/50000000000000 : ℝ)*(f.sum) + (8547134816437/3286250000000000000000000000 : ℝ)*base66 + (6514775637518815701/2629000000000000000000000000000000 : ℝ)*base67 + (97444032771838184299/2629000000000000000000000000000000 : ℝ)*base70 + (3918231982692184299/2629000000000000000000000000000000 : ℝ)*base72 + (362033221043/13145000000000000000000000000 : ℝ)*base74 + (77337916203443815701/2629000000000000000000000000000000 : ℝ)*base75 + (8274155051079184299/2629000000000000000000000000000000 : ℝ)*base78 + (18438347516550815701/2629000000000000000000000000000000 : ℝ)*base79 + (5461858824209/1643125000000000000000000000 : ℝ)*base81 + (6057789/1250000000000000000000 : ℝ)*base90 + (6057789/1250000000000000000000 : ℝ)*base92 + (6057789/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83333/100000 : ℝ) ≤ (-27384375824611784384049695287119/32862500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1042701/12500000000000 : ℝ)*(upper3) + (37611969/100000000000000 : ℝ)*(lower4) + (115654161/25000000000000 : ℝ)*(upper5) + (228311932896623/5000000000000 : ℝ)*(major0) + (228311932896623/5000000000000 : ℝ)*(major1) + (228311932896623/5000000000000 : ℝ)*(major2) + (35397087551/100000000000000 : ℝ)*(sp4) + (213024109713/100000000000000 : ℝ)*(sp5) + (330883028869/100000000000000 : ℝ)*(sp6) + (4836670007/2000000000000 : ℝ)*(sp7) + (6142435603055849/100000000000000 : ℝ)*(sp12) + (6142257976033687/100000000000000 : ℝ)*(sp13) + (6142140117114531/100000000000000 : ℝ)*(sp14) + (3017541204244353/100000000000000 : ℝ)*(sp15) + (47152859964761/1562500000000 : ℝ)*(f.failure) + (30712355000717/500000000000 : ℝ)*(f.sum) + (11047579378711/2629000000000000000000000000 : ℝ)*base66 + (429697064818912373/131450000000000000000000000000000 : ℝ)*base68 + (477939670556062373/131450000000000000000000000000000 : ℝ)*base70 + (657727737912212373/131450000000000000000000000000000 : ℝ)*base72 + (819027976229/657250000000000000000000000 : ℝ)*base73 + (784671995551487627/131450000000000000000000000000000 : ℝ)*base75 + (492216129060062373/131450000000000000000000000000000 : ℝ)*base78 + (449929467613912373/131450000000000000000000000000000 : ℝ)*base80 + (3592018653461/2629000000000000000000000000 : ℝ)*base82 + (224169/19531250000000000000 : ℝ)*base89 + (224169/19531250000000000000 : ℝ)*base91 + (224169/19531250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1236_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14843/25000 : ℝ) else (80091/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83333/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1236_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1236_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14843/25000 : ℝ) else (80091/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83333/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1236_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2107/512 : ℝ) ≤ p) (hpb : p ≤ (8429/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18913879/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14843/25000 : ℝ) else (80091/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83333/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1236_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

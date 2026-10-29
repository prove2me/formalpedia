-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1405_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:47:22.873416+00:00
-- url     : https://prove2.me/submissions/595f92cf-733c-4d76-8dcf-03579bb5079f

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
theorem support_rectangle_w1405_s6_0 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-124422987/625000000 : ℝ)*x 0 + (5409460347/10000000000 : ℝ)*x 1 + (5246342817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (124422987/625000000 : ℝ)^4365 ≤ (3034686914817/25000000000000 : ℝ)^3341 := by
    have hnat : (124422987 : ℕ)^4365*25000000000000^3341 ≤ 3034686914817^3341*625000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124422987 625000000 3034686914817 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409460347/10000000000 : ℝ)^4365 ≤ (22404587220509/50000000000000 : ℝ)^3341 := by
    have hnat : (5409460347 : ℕ)^4365*50000000000000^3341 ≤ 22404587220509^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409460347 10000000000 22404587220509 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246342817/10000000000 : ℝ)^4365 ≤ (43052077885681/100000000000000 : ℝ)^3341 := by
    have hnat : (5246342817 : ℕ)^4365*100000000000000^3341 ≤ 43052077885681^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246342817 10000000000 43052077885681 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-124422987/625000000 : ℝ), (5409460347/10000000000 : ℝ), (5246342817/10000000000 : ℝ)] ![(3034686914817/25000000000000 : ℝ), (22404587220509/50000000000000 : ℝ), (43052077885681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-124422987/625000000 : ℝ)|^4365 ≤ (3034686914817/25000000000000 : ℝ)^3341
        have hw : |(-124422987/625000000 : ℝ)|=(124422987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409460347/10000000000 : ℝ)|^4365 ≤ (22404587220509/50000000000000 : ℝ)^3341
        have hw : |(5409460347/10000000000 : ℝ)|=(5409460347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246342817/10000000000 : ℝ)|^4365 ≤ (43052077885681/100000000000000 : ℝ)^3341
        have hw : |(5246342817/10000000000 : ℝ)|=(5246342817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s6_1 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66847777/125000000 : ℝ)*x 0 + (-1036915239/5000000000 : ℝ)*x 1 + (5246342911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66847777/125000000 : ℝ)^4365 ≤ (44143273545751/100000000000000 : ℝ)^3341 := by
    have hnat : (66847777 : ℕ)^4365*100000000000000^3341 ≤ 44143273545751^3341*125000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66847777 125000000 44143273545751 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036915239/5000000000 : ℝ)^4365 ≤ (800290471939/6250000000000 : ℝ)^3341 := by
    have hnat : (1036915239 : ℕ)^4365*6250000000000^3341 ≤ 800290471939^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036915239 5000000000 800290471939 6250000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246342911/10000000000 : ℝ)^4365 ≤ (21526039446739/50000000000000 : ℝ)^3341 := by
    have hnat : (5246342911 : ℕ)^4365*50000000000000^3341 ≤ 21526039446739^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246342911 10000000000 21526039446739 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66847777/125000000 : ℝ), (-1036915239/5000000000 : ℝ), (5246342911/10000000000 : ℝ)] ![(44143273545751/100000000000000 : ℝ), (800290471939/6250000000000 : ℝ), (21526039446739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66847777/125000000 : ℝ)|^4365 ≤ (44143273545751/100000000000000 : ℝ)^3341
        have hw : |(66847777/125000000 : ℝ)|=(66847777/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036915239/5000000000 : ℝ)|^4365 ≤ (800290471939/6250000000000 : ℝ)^3341
        have hw : |(-1036915239/5000000000 : ℝ)|=(1036915239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246342911/10000000000 : ℝ)|^4365 ≤ (21526039446739/50000000000000 : ℝ)^3341
        have hw : |(5246342911/10000000000 : ℝ)|=(5246342911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s6_2 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347821967/10000000000 : ℝ)*x 0 + (2623171477/5000000000 : ℝ)*x 1 + (-2073830679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347821967/10000000000 : ℝ)^4365 ≤ (8828654292873/20000000000000 : ℝ)^3341 := by
    have hnat : (5347821967 : ℕ)^4365*20000000000000^3341 ≤ 8828654292873^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347821967 10000000000 8828654292873 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623171477/5000000000 : ℝ)^4365 ≤ (10763019838623/25000000000000 : ℝ)^3341 := by
    have hnat : (2623171477 : ℕ)^4365*25000000000000^3341 ≤ 10763019838623^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623171477 5000000000 10763019838623 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073830679/10000000000 : ℝ)^4365 ≤ (6402324586227/50000000000000 : ℝ)^3341 := by
    have hnat : (2073830679 : ℕ)^4365*50000000000000^3341 ≤ 6402324586227^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073830679 10000000000 6402324586227 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347821967/10000000000 : ℝ), (2623171477/5000000000 : ℝ), (-2073830679/10000000000 : ℝ)] ![(8828654292873/20000000000000 : ℝ), (10763019838623/25000000000000 : ℝ), (6402324586227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347821967/10000000000 : ℝ)|^4365 ≤ (8828654292873/20000000000000 : ℝ)^3341
        have hw : |(5347821967/10000000000 : ℝ)|=(5347821967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623171477/5000000000 : ℝ)|^4365 ≤ (10763019838623/25000000000000 : ℝ)^3341
        have hw : |(2623171477/5000000000 : ℝ)|=(2623171477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2073830679/10000000000 : ℝ)|^4365 ≤ (6402324586227/50000000000000 : ℝ)^3341
        have hw : |(-2073830679/10000000000 : ℝ)|=(2073830679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s6_3 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310410503/10000000000 : ℝ)*x 0 + (2069373977/5000000000 : ℝ)*x 1 + (4488524613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310410503/10000000000 : ℝ)^4365 ≤ (8326076688821/25000000000000 : ℝ)^3341 := by
    have hnat : (4310410503 : ℕ)^4365*25000000000000^3341 ≤ 8326076688821^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310410503 10000000000 8326076688821 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069373977/5000000000 : ℝ)^4365 ≤ (15791057597961/50000000000000 : ℝ)^3341 := by
    have hnat : (2069373977 : ℕ)^4365*50000000000000^3341 ≤ 15791057597961^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069373977 5000000000 15791057597961 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488524613/10000000000 : ℝ)^4365 ≤ (17556789019609/50000000000000 : ℝ)^3341 := by
    have hnat : (4488524613 : ℕ)^4365*50000000000000^3341 ≤ 17556789019609^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488524613 10000000000 17556789019609 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310410503/10000000000 : ℝ), (2069373977/5000000000 : ℝ), (4488524613/10000000000 : ℝ)] ![(8326076688821/25000000000000 : ℝ), (15791057597961/50000000000000 : ℝ), (17556789019609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310410503/10000000000 : ℝ)|^4365 ≤ (8326076688821/25000000000000 : ℝ)^3341
        have hw : |(4310410503/10000000000 : ℝ)|=(4310410503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2069373977/5000000000 : ℝ)|^4365 ≤ (15791057597961/50000000000000 : ℝ)^3341
        have hw : |(2069373977/5000000000 : ℝ)|=(2069373977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488524613/10000000000 : ℝ)|^4365 ≤ (17556789019609/50000000000000 : ℝ)^3341
        have hw : |(4488524613/10000000000 : ℝ)|=(4488524613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s6_4 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398155919/2000000000 : ℝ)*x 0 + (5246929923/10000000000 : ℝ)*x 1 + (5408870017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398155919/2000000000 : ℝ)^4365 ≤ (12138841686543/100000000000000 : ℝ)^3341 := by
    have hnat : (398155919 : ℕ)^4365*100000000000000^3341 ≤ 12138841686543^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398155919 2000000000 12138841686543 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246929923/10000000000 : ℝ)^4365 ≤ (43058372500943/100000000000000 : ℝ)^3341 := by
    have hnat : (5246929923 : ℕ)^4365*100000000000000^3341 ≤ 43058372500943^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246929923 10000000000 43058372500943 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408870017/10000000000 : ℝ)^4365 ≤ (44802785801783/100000000000000 : ℝ)^3341 := by
    have hnat : (5408870017 : ℕ)^4365*100000000000000^3341 ≤ 44802785801783^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408870017 10000000000 44802785801783 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398155919/2000000000 : ℝ), (5246929923/10000000000 : ℝ), (5408870017/10000000000 : ℝ)] ![(12138841686543/100000000000000 : ℝ), (43058372500943/100000000000000 : ℝ), (44802785801783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398155919/2000000000 : ℝ)|^4365 ≤ (12138841686543/100000000000000 : ℝ)^3341
        have hw : |(-398155919/2000000000 : ℝ)|=(398155919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246929923/10000000000 : ℝ)|^4365 ≤ (43058372500943/100000000000000 : ℝ)^3341
        have hw : |(5246929923/10000000000 : ℝ)|=(5246929923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408870017/10000000000 : ℝ)|^4365 ≤ (44802785801783/100000000000000 : ℝ)^3341
        have hw : |(5408870017/10000000000 : ℝ)|=(5408870017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s6_5 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652758907/5000000000 : ℝ)*x 0 + (-1911303409/10000000000 : ℝ)*x 1 + (42256797/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652758907/5000000000 : ℝ)^4365 ≤ (43687601311599/100000000000000 : ℝ)^3341 := by
    have hnat : (2652758907 : ℕ)^4365*100000000000000^3341 ≤ 43687601311599^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652758907 5000000000 43687601311599 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1911303409/10000000000 : ℝ)^4365 ≤ (2877403220073/25000000000000 : ℝ)^3341 := by
    have hnat : (1911303409 : ℕ)^4365*25000000000000^3341 ≤ 2877403220073^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911303409 10000000000 2877403220073 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42256797/78125000 : ℝ)^4365 ≤ (44802785790961/100000000000000 : ℝ)^3341 := by
    have hnat : (42256797 : ℕ)^4365*100000000000000^3341 ≤ 44802785790961^3341*78125000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42256797 78125000 44802785790961 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652758907/5000000000 : ℝ), (-1911303409/10000000000 : ℝ), (42256797/78125000 : ℝ)] ![(43687601311599/100000000000000 : ℝ), (2877403220073/25000000000000 : ℝ), (44802785790961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652758907/5000000000 : ℝ)|^4365 ≤ (43687601311599/100000000000000 : ℝ)^3341
        have hw : |(2652758907/5000000000 : ℝ)|=(2652758907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1911303409/10000000000 : ℝ)|^4365 ≤ (2877403220073/25000000000000 : ℝ)^3341
        have hw : |(-1911303409/10000000000 : ℝ)|=(1911303409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42256797/78125000 : ℝ)|^4365 ≤ (44802785790961/100000000000000 : ℝ)^3341
        have hw : |(42256797/78125000 : ℝ)|=(42256797/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s6_6 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305517817/10000000000 : ℝ)*x 0 + (5408870013/10000000000 : ℝ)*x 1 + (-191130341/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305517817/10000000000 : ℝ)^4365 ≤ (21843800671937/50000000000000 : ℝ)^3341 := by
    have hnat : (5305517817 : ℕ)^4365*50000000000000^3341 ≤ 21843800671937^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305517817 10000000000 21843800671937 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408870013/10000000000 : ℝ)^4365 ≤ (8960557151699/20000000000000 : ℝ)^3341 := by
    have hnat : (5408870013 : ℕ)^4365*20000000000000^3341 ≤ 8960557151699^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408870013 10000000000 8960557151699 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191130341/1000000000 : ℝ)^4365 ≤ (71935080551/625000000000 : ℝ)^3341 := by
    have hnat : (191130341 : ℕ)^4365*625000000000^3341 ≤ 71935080551^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191130341 1000000000 71935080551 625000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305517817/10000000000 : ℝ), (5408870013/10000000000 : ℝ), (-191130341/1000000000 : ℝ)] ![(21843800671937/50000000000000 : ℝ), (8960557151699/20000000000000 : ℝ), (71935080551/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305517817/10000000000 : ℝ)|^4365 ≤ (21843800671937/50000000000000 : ℝ)^3341
        have hw : |(5305517817/10000000000 : ℝ)|=(5305517817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408870013/10000000000 : ℝ)|^4365 ≤ (8960557151699/20000000000000 : ℝ)^3341
        have hw : |(5408870013/10000000000 : ℝ)|=(5408870013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-191130341/1000000000 : ℝ)|^4365 ≤ (71935080551/625000000000 : ℝ)^3341
        have hw : |(-191130341/1000000000 : ℝ)|=(191130341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_s6_7 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310435901/10000000000 : ℝ)*x 0 + (224363271/500000000 : ℝ)*x 1 + (4140013019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310435901/10000000000 : ℝ)^4365 ≤ (2081535196151/6250000000000 : ℝ)^3341 := by
    have hnat : (4310435901 : ℕ)^4365*6250000000000^3341 ≤ 2081535196151^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310435901 10000000000 2081535196151 6250000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224363271/500000000 : ℝ)^4365 ≤ (702014175999/2000000000000 : ℝ)^3341 := by
    have hnat : (224363271 : ℕ)^4365*2000000000000^3341 ≤ 702014175999^3341*500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224363271 500000000 702014175999 2000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4140013019/10000000000 : ℝ)^4365 ≤ (31594728044691/100000000000000 : ℝ)^3341 := by
    have hnat : (4140013019 : ℕ)^4365*100000000000000^3341 ≤ 31594728044691^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140013019 10000000000 31594728044691 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310435901/10000000000 : ℝ), (224363271/500000000 : ℝ), (4140013019/10000000000 : ℝ)] ![(2081535196151/6250000000000 : ℝ), (702014175999/2000000000000 : ℝ), (31594728044691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310435901/10000000000 : ℝ)|^4365 ≤ (2081535196151/6250000000000 : ℝ)^3341
        have hw : |(4310435901/10000000000 : ℝ)|=(4310435901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224363271/500000000 : ℝ)|^4365 ≤ (702014175999/2000000000000 : ℝ)^3341
        have hw : |(224363271/500000000 : ℝ)|=(224363271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4140013019/10000000000 : ℝ)|^4365 ≤ (31594728044691/100000000000000 : ℝ)^3341
        have hw : |(4140013019/10000000000 : ℝ)|=(4140013019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1405_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1129/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1843/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5643/50000 : ℝ) ^ (1091/256 : ℝ) ≤ (572891219768347/6250000000000000000 : ℝ) := by
    have hpowers : (5643/50000 : ℝ)^1091 ≤ (572891219768347/6250000000000000000 : ℝ)^256 := by
      have hnat : (5643 : ℕ)^1091*6250000000000000000^256 ≤ 572891219768347^256*50000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5643 50000 572891219768347 6250000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5643/50000 : ℝ)) (X := (572891219768347/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (1091/256 : ℝ) ≤ (5734953203881861/20000000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^1091 ≤ (5734953203881861/20000000000000000000 : ℝ)^256 := by
      have hnat : (14749 : ℕ)^1091*20000000000000000000^256 ≤ 5734953203881861^256*100000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 5734953203881861 20000000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (5734953203881861/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125572891219768347/3125000000000000000 : ℝ) ≤ (10000430137091227/10000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (3125572891219768347/3125000000000000000 : ℝ)^256 ≤ (10000430137091227/10000000000000000 : ℝ)^1091 := by
      have hnat : (3125572891219768347 : ℕ)^256*10000000000000000^1091 ≤ 10000430137091227^1091*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125572891219768347 3125000000000000000 10000430137091227 10000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000430137091227/10000000000000000 : ℝ)) (X := (3125572891219768347/3125000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037841025535702857/100000000000000000000 : ℝ) ≤ (1250110975023417/1250000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (100037841025535702857/100000000000000000000 : ℝ)^256 ≤ (1250110975023417/1250000000000000 : ℝ)^1091 := by
      have hnat : (100037841025535702857 : ℕ)^256*1250000000000000^1091 ≤ 1250110975023417^1091*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037841025535702857 100000000000000000000 1250110975023417 1250000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250110975023417/1250000000000000 : ℝ)) (X := (100037841025535702857/100000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005734953203881861/10000000000000000000 : ℝ) ≤ (2000269092656689/2000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (10005734953203881861/10000000000000000000 : ℝ)^256 ≤ (2000269092656689/2000000000000000 : ℝ)^1091 := by
      have hnat : (10005734953203881861 : ℕ)^256*2000000000000000^1091 ≤ 2000269092656689^1091*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005734953203881861 10000000000000000000 2000269092656689 2000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000269092656689/2000000000000000 : ℝ)) (X := (10005734953203881861/10000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(572891219768347/6250000000000000000 : ℝ) ≤ ((34621159193341546753/34630000000000000000 : ℝ)+2*(457663096109/346300000000000 : ℝ)*(5643/50000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (34621159193341546753/34630000000000000000 : ℝ)+2*(457663096109/346300000000000 : ℝ)*(5643/50000 : ℝ)=(10000430137091227/10000000000000000 : ℝ) by norm_num, show 1+2*(572891219768347/6250000000000000000 : ℝ)=(3125572891219768347/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5734953203881861/20000000000000000000 : ℝ)+(572891219768347/6250000000000000000 : ℝ) ≤ ((34621159193341546753/34630000000000000000 : ℝ)+(457663096109/346300000000000 : ℝ)*((14749/100000 : ℝ)+(5643/50000 : ℝ)))^(1091/256 : ℝ) := by
    rw [show (34621159193341546753/34630000000000000000 : ℝ)+(457663096109/346300000000000 : ℝ)*((14749/100000 : ℝ)+(5643/50000 : ℝ))=(1250110975023417/1250000000000000 : ℝ) by norm_num, show 1+(5734953203881861/20000000000000000000 : ℝ)+(572891219768347/6250000000000000000 : ℝ)=(100037841025535702857/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5734953203881861/20000000000000000000 : ℝ) ≤ ((34621159193341546753/34630000000000000000 : ℝ)+2*(457663096109/346300000000000 : ℝ)*(14749/100000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (34621159193341546753/34630000000000000000 : ℝ)+2*(457663096109/346300000000000 : ℝ)*(14749/100000 : ℝ)=(2000269092656689/2000000000000000 : ℝ) by norm_num, show 1+2*(5734953203881861/20000000000000000000 : ℝ)=(10005734953203881861/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34621159193341546753/34630000000000000000 : ℝ)*(X 1 0+X 2 0)+(457663096109/346300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (34621159193341546753/34630000000000000000 : ℝ)) (alpha := (457663096109/346300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34621159193341546753/34630000000000000000 : ℝ)*(X 0 1+X 2 1)+(457663096109/346300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (34621159193341546753/34630000000000000000 : ℝ)) (alpha := (457663096109/346300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34621159193341546753/34630000000000000000 : ℝ)*(X 0 2+X 1 2)+(457663096109/346300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (34621159193341546753/34630000000000000000 : ℝ)) (alpha := (457663096109/346300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-124422987/625000000 : ℝ)*X 0 0+(5409460347/10000000000 : ℝ)*X 0 1+(5246342817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66847777/125000000 : ℝ)*X 1 0+(-1036915239/5000000000 : ℝ)*X 1 1+(5246342911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347821967/10000000000 : ℝ)*X 2 0+(2623171477/5000000000 : ℝ)*X 2 1+(-2073830679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310410503/10000000000 : ℝ)*X 0 0+(2069373977/5000000000 : ℝ)*X 0 1+(4488524613/10000000000 : ℝ)*X 0 2+(4310410503/10000000000 : ℝ)*X 1 0+(2069373977/5000000000 : ℝ)*X 1 1+(4488524613/10000000000 : ℝ)*X 1 2+(4310410503/10000000000 : ℝ)*X 2 0+(2069373977/5000000000 : ℝ)*X 2 1+(4488524613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-398155919/2000000000 : ℝ)*X 0 0+(5246929923/10000000000 : ℝ)*X 0 1+(5408870017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652758907/5000000000 : ℝ)*X 1 0+(-1911303409/10000000000 : ℝ)*X 1 1+(42256797/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305517817/10000000000 : ℝ)*X 2 0+(5408870013/10000000000 : ℝ)*X 2 1+(-191130341/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310435901/10000000000 : ℝ)*X 0 0+(224363271/500000000 : ℝ)*X 0 1+(4140013019/10000000000 : ℝ)*X 0 2+(4310435901/10000000000 : ℝ)*X 1 0+(224363271/500000000 : ℝ)*X 1 1+(4140013019/10000000000 : ℝ)*X 1 2+(4310435901/10000000000 : ℝ)*X 2 0+(224363271/500000000 : ℝ)*X 2 1+(4140013019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1231807437649740518214957081/173150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (448619249/100000000000000 : ℝ)*(base19) + (214012093/100000000000000 : ℝ)*(base23) + (20617371/100000000000000 : ℝ)*(lower4) + (51920849/100000000000000 : ℝ)*(lower5) + (449478362293247/10000000000000 : ℝ)*(major0) + (449478362293247/10000000000000 : ℝ)*(major1) + (449478362293247/10000000000000 : ℝ)*(major2) + (95790155990883/1562500000000 : ℝ)*(sp0) + (1226117240379597/20000000000000 : ℝ)*(sp1) + (3065289937157653/50000000000000 : ℝ)*(sp2) + (1429486976368393/50000000000000 : ℝ)*(sp3) + (8333550361/50000000000000 : ℝ)*(sp4) + (3281094917/50000000000000 : ℝ)*(sp6) + (6405474041/100000000000000 : ℝ)*(sp7) + (2858980358210827/100000000000000 : ℝ)*(f.failure) + (3065293325258617/50000000000000 : ℝ)*(f.sum) + (3670093538069/3463000000000000000000000000 : ℝ)*base66 + (3388131490734776991/346300000000000000000000000000000 : ℝ)*base67 + (4442771504136476991/346300000000000000000000000000000 : ℝ)*base69 + (6972196320615276991/346300000000000000000000000000000 : ℝ)*base71 + (486617643937/432875000000000000000000000 : ℝ)*base74 + (2380663133887376991/346300000000000000000000000000000 : ℝ)*base75 + (4516218823831276991/346300000000000000000000000000000 : ℝ)*base77 + (14892997463609976991/346300000000000000000000000000000 : ℝ)*base79 + (6914265796017/3463000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (69535841/10000000000000000000000 : ℝ)*base90 + (69535841/10000000000000000000000 : ℝ)*base92 + (69535841/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2347302965255002880853104589/865750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (458545273/100000000000000 : ℝ)*(base19) + (498287321/100000000000000 : ℝ)*(base23) + (154967227/100000000000000 : ℝ)*(lower1) + (10987873/20000000000000 : ℝ)*(upper3) + (16701603/100000000000000 : ℝ)*(lower4) + (28665451/50000000000000 : ℝ)*(upper5) + (4527429179378129/100000000000000 : ℝ)*(major0) + (4527429179378129/100000000000000 : ℝ)*(major1) + (4527429179378129/100000000000000 : ℝ)*(major2) + (299152983/50000000000000 : ℝ)*(sp2) + (247004526883517/4000000000000 : ℝ)*(sp4) + (1543778178385663/25000000000000 : ℝ)*(sp5) + (3087556037747319/50000000000000 : ℝ)*(sp6) + (719936274072959/25000000000000 : ℝ)*(sp7) + (719936274072959/25000000000000 : ℝ)*(f.failure) + (247004526883517/4000000000000 : ℝ)*(f.sum) + (5006872951577/8657500000000000000000000000 : ℝ)*base66 + (91021221142140265137/3463000000000000000000000000000000 : ℝ)*base67 + (15778657611558265137/3463000000000000000000000000000000 : ℝ)*base69 + (177760657995193265137/3463000000000000000000000000000000 : ℝ)*base71 + (34227869623681/17315000000000000000000000000 : ℝ)*base73 + (297252413712217265137/3463000000000000000000000000000000 : ℝ)*base75 + (5566038607873265137/3463000000000000000000000000000000 : ℝ)*base77 + (35763621007288734863/3463000000000000000000000000000000 : ℝ)*base80 + (108121445442789/17315000000000000000000000000 : ℝ)*base82 + (21727997/2500000000000000000000 : ℝ)*base90 + (21727997/2500000000000000000000 : ℝ)*base92 + (21727997/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1405_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1405_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1405_box_0 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22854381/125000000 : ℝ)*x 0 + (5387283797/10000000000 : ℝ)*x 1 + (2693641457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22854381/125000000 : ℝ)^4365 ≤ (2715340671303/25000000000000 : ℝ)^3341 := by
    have hnat : (22854381 : ℕ)^4365*25000000000000^3341 ≤ 2715340671303^3341*125000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22854381 125000000 2715340671303 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387283797/10000000000 : ℝ)^4365 ≤ (696395678483/1562500000000 : ℝ)^3341 := by
    have hnat : (5387283797 : ℕ)^4365*1562500000000^3341 ≤ 696395678483^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387283797 10000000000 696395678483 1562500000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693641457/5000000000 : ℝ)^4365 ≤ (2228465693941/5000000000000 : ℝ)^3341 := by
    have hnat : (2693641457 : ℕ)^4365*5000000000000^3341 ≤ 2228465693941^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693641457 5000000000 2228465693941 5000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22854381/125000000 : ℝ), (5387283797/10000000000 : ℝ), (2693641457/5000000000 : ℝ)] ![(2715340671303/25000000000000 : ℝ), (696395678483/1562500000000 : ℝ), (2228465693941/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22854381/125000000 : ℝ)|^4365 ≤ (2715340671303/25000000000000 : ℝ)^3341
        have hw : |(-22854381/125000000 : ℝ)|=(22854381/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387283797/10000000000 : ℝ)|^4365 ≤ (696395678483/1562500000000 : ℝ)^3341
        have hw : |(5387283797/10000000000 : ℝ)|=(5387283797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693641457/5000000000 : ℝ)|^4365 ≤ (2228465693941/5000000000000 : ℝ)^3341
        have hw : |(2693641457/5000000000 : ℝ)|=(2693641457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_1 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285871811/10000000000 : ℝ)*x 0 + (-983787969/5000000000 : ℝ)*x 1 + (673410323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285871811/10000000000 : ℝ)^4365 ≤ (8695273282381/20000000000000 : ℝ)^3341 := by
    have hnat : (5285871811 : ℕ)^4365*20000000000000^3341 ≤ 8695273282381^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285871811 10000000000 8695273282381 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983787969/5000000000 : ℝ)^4365 ≤ (5977161628959/50000000000000 : ℝ)^3341 := by
    have hnat : (983787969 : ℕ)^4365*50000000000000^3341 ≤ 5977161628959^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983787969 5000000000 5977161628959 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673410323/1250000000 : ℝ)^4365 ≤ (8913862062389/20000000000000 : ℝ)^3341 := by
    have hnat : (673410323 : ℕ)^4365*20000000000000^3341 ≤ 8913862062389^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673410323 1250000000 8913862062389 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285871811/10000000000 : ℝ), (-983787969/5000000000 : ℝ), (673410323/1250000000 : ℝ)] ![(8695273282381/20000000000000 : ℝ), (5977161628959/50000000000000 : ℝ), (8913862062389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285871811/10000000000 : ℝ)|^4365 ≤ (8695273282381/20000000000000 : ℝ)^3341
        have hw : |(5285871811/10000000000 : ℝ)|=(5285871811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983787969/5000000000 : ℝ)|^4365 ≤ (5977161628959/50000000000000 : ℝ)^3341
        have hw : |(-983787969/5000000000 : ℝ)|=(983787969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673410323/1250000000 : ℝ)|^4365 ≤ (8913862062389/20000000000000 : ℝ)^3341
        have hw : |(673410323/1250000000 : ℝ)|=(673410323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_2 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642936357/5000000000 : ℝ)*x 0 + (673410353/1250000000 : ℝ)*x 1 + (-1967574389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642936357/5000000000 : ℝ)^4365 ≤ (1358636753609/3125000000000 : ℝ)^3341 := by
    have hnat : (2642936357 : ℕ)^4365*3125000000000^3341 ≤ 1358636753609^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642936357 5000000000 1358636753609 3125000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673410353/1250000000 : ℝ)^4365 ≤ (11142328226509/25000000000000 : ℝ)^3341 := by
    have hnat : (673410353 : ℕ)^4365*25000000000000^3341 ≤ 11142328226509^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673410353 1250000000 11142328226509 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1967574389/10000000000 : ℝ)^4365 ≤ (2390862192447/20000000000000 : ℝ)^3341 := by
    have hnat : (1967574389 : ℕ)^4365*20000000000000^3341 ≤ 2390862192447^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967574389 10000000000 2390862192447 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642936357/5000000000 : ℝ), (673410353/1250000000 : ℝ), (-1967574389/10000000000 : ℝ)] ![(1358636753609/3125000000000 : ℝ), (11142328226509/25000000000000 : ℝ), (2390862192447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642936357/5000000000 : ℝ)|^4365 ≤ (1358636753609/3125000000000 : ℝ)^3341
        have hw : |(2642936357/5000000000 : ℝ)|=(2642936357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673410353/1250000000 : ℝ)|^4365 ≤ (11142328226509/25000000000000 : ℝ)^3341
        have hw : |(673410353/1250000000 : ℝ)|=(673410353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1967574389/10000000000 : ℝ)|^4365 ≤ (2390862192447/20000000000000 : ℝ)^3341
        have hw : |(-1967574389/10000000000 : ℝ)|=(1967574389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_3 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (891441137/2000000000 : ℝ)*x 0 + (4240772853/10000000000 : ℝ)*x 1 + (1060193259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891441137/2000000000 : ℝ)^4365 ≤ (34793820533841/100000000000000 : ℝ)^3341 := by
    have hnat : (891441137 : ℕ)^4365*100000000000000^3341 ≤ 34793820533841^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891441137 2000000000 34793820533841 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240772853/10000000000 : ℝ)^4365 ≤ (16301544403467/50000000000000 : ℝ)^3341 := by
    have hnat : (4240772853 : ℕ)^4365*50000000000000^3341 ≤ 16301544403467^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240772853 10000000000 16301544403467 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060193259/2500000000 : ℝ)^4365 ≤ (32603090645049/100000000000000 : ℝ)^3341 := by
    have hnat : (1060193259 : ℕ)^4365*100000000000000^3341 ≤ 32603090645049^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060193259 2500000000 32603090645049 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(891441137/2000000000 : ℝ), (4240772853/10000000000 : ℝ), (1060193259/2500000000 : ℝ)] ![(34793820533841/100000000000000 : ℝ), (16301544403467/50000000000000 : ℝ), (32603090645049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(891441137/2000000000 : ℝ)|^4365 ≤ (34793820533841/100000000000000 : ℝ)^3341
        have hw : |(891441137/2000000000 : ℝ)|=(891441137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240772853/10000000000 : ℝ)|^4365 ≤ (16301544403467/50000000000000 : ℝ)^3341
        have hw : |(4240772853/10000000000 : ℝ)|=(4240772853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060193259/2500000000 : ℝ)|^4365 ≤ (32603090645049/100000000000000 : ℝ)^3341
        have hw : |(1060193259/2500000000 : ℝ)|=(1060193259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_4 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215593491/1000000000 : ℝ)*x 0 + (26330733/50000000 : ℝ)*x 1 + (2633073543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215593491/1000000000 : ℝ)^4365 ≤ (3367737785491/25000000000000 : ℝ)^3341 := by
    have hnat : (215593491 : ℕ)^4365*25000000000000^3341 ≤ 3367737785491^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215593491 1000000000 3367737785491 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26330733/50000000 : ℝ)^4365 ≤ (21632260906221/50000000000000 : ℝ)^3341 := by
    have hnat : (26330733 : ℕ)^4365*50000000000000^3341 ≤ 21632260906221^3341*50000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26330733 50000000 21632260906221 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633073543/5000000000 : ℝ)^4365 ≤ (10816131757247/25000000000000 : ℝ)^3341 := by
    have hnat : (2633073543 : ℕ)^4365*25000000000000^3341 ≤ 10816131757247^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633073543 5000000000 10816131757247 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215593491/1000000000 : ℝ), (26330733/50000000 : ℝ), (2633073543/5000000000 : ℝ)] ![(3367737785491/25000000000000 : ℝ), (21632260906221/50000000000000 : ℝ), (10816131757247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215593491/1000000000 : ℝ)|^4365 ≤ (3367737785491/25000000000000 : ℝ)^3341
        have hw : |(-215593491/1000000000 : ℝ)|=(215593491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26330733/50000000 : ℝ)|^4365 ≤ (21632260906221/50000000000000 : ℝ)^3341
        have hw : |(26330733/50000000 : ℝ)|=(26330733/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633073543/5000000000 : ℝ)|^4365 ≤ (10816131757247/25000000000000 : ℝ)^3341
        have hw : |(2633073543/5000000000 : ℝ)|=(2633073543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_5 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342683181/2500000000 : ℝ)*x 0 + (-1008301483/5000000000 : ℝ)*x 1 + (5266146383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342683181/2500000000 : ℝ)^4365 ≤ (5548813990287/12500000000000 : ℝ)^3341 := by
    have hnat : (1342683181 : ℕ)^4365*12500000000000^3341 ≤ 5548813990287^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342683181 2500000000 5548813990287 12500000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008301483/5000000000 : ℝ)^4365 ≤ (385780268139/3125000000000 : ℝ)^3341 := by
    have hnat : (1008301483 : ℕ)^4365*3125000000000^3341 ≤ 385780268139^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008301483 5000000000 385780268139 3125000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266146383/10000000000 : ℝ)^4365 ≤ (10816129870811/25000000000000 : ℝ)^3341 := by
    have hnat : (5266146383 : ℕ)^4365*25000000000000^3341 ≤ 10816129870811^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266146383 10000000000 10816129870811 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342683181/2500000000 : ℝ), (-1008301483/5000000000 : ℝ), (5266146383/10000000000 : ℝ)] ![(5548813990287/12500000000000 : ℝ), (385780268139/3125000000000 : ℝ), (10816129870811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342683181/2500000000 : ℝ)|^4365 ≤ (5548813990287/12500000000000 : ℝ)^3341
        have hw : |(1342683181/2500000000 : ℝ)|=(1342683181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1008301483/5000000000 : ℝ)|^4365 ≤ (385780268139/3125000000000 : ℝ)^3341
        have hw : |(-1008301483/5000000000 : ℝ)|=(1008301483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266146383/10000000000 : ℝ)|^4365 ≤ (10816129870811/25000000000000 : ℝ)^3341
        have hw : |(5266146383/10000000000 : ℝ)|=(5266146383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_6 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370732621/10000000000 : ℝ)*x 0 + (5266146831/10000000000 : ℝ)*x 1 + (-252075313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370732621/10000000000 : ℝ)^4365 ≤ (693601731407/1562500000000 : ℝ)^3341 := by
    have hnat : (5370732621 : ℕ)^4365*1562500000000^3341 ≤ 693601731407^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370732621 10000000000 693601731407 1562500000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266146831/10000000000 : ℝ)^4365 ≤ (43264524291911/100000000000000 : ℝ)^3341 := by
    have hnat : (5266146831 : ℕ)^4365*100000000000000^3341 ≤ 43264524291911^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266146831 10000000000 43264524291911 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252075313/1250000000 : ℝ)^4365 ≤ (6172482442703/50000000000000 : ℝ)^3341 := by
    have hnat : (252075313 : ℕ)^4365*50000000000000^3341 ≤ 6172482442703^3341*1250000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252075313 1250000000 6172482442703 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370732621/10000000000 : ℝ), (5266146831/10000000000 : ℝ), (-252075313/1250000000 : ℝ)] ![(693601731407/1562500000000 : ℝ), (43264524291911/100000000000000 : ℝ), (6172482442703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370732621/10000000000 : ℝ)|^4365 ≤ (693601731407/1562500000000 : ℝ)^3341
        have hw : |(5370732621/10000000000 : ℝ)|=(5370732621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266146831/10000000000 : ℝ)|^4365 ≤ (43264524291911/100000000000000 : ℝ)^3341
        have hw : |(5266146831/10000000000 : ℝ)|=(5266146831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-252075313/1250000000 : ℝ)|^4365 ≤ (6172482442703/50000000000000 : ℝ)^3341
        have hw : |(-252075313/1250000000 : ℝ)|=(252075313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_7 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4162604577/10000000000 : ℝ)*x 0 + (2194011011/5000000000 : ℝ)*x 1 + (1097005443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162604577/10000000000 : ℝ)^4365 ≤ (31820167248221/100000000000000 : ℝ)^3341 := by
    have hnat : (4162604577 : ℕ)^4365*100000000000000^3341 ≤ 31820167248221^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162604577 10000000000 31820167248221 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194011011/5000000000 : ℝ)^4365 ≤ (34089917635033/100000000000000 : ℝ)^3341 := by
    have hnat : (2194011011 : ℕ)^4365*100000000000000^3341 ≤ 34089917635033^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194011011 5000000000 34089917635033 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097005443/2500000000 : ℝ)^4365 ≤ (1704495754877/5000000000000 : ℝ)^3341 := by
    have hnat : (1097005443 : ℕ)^4365*5000000000000^3341 ≤ 1704495754877^3341*2500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097005443 2500000000 1704495754877 5000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162604577/10000000000 : ℝ), (2194011011/5000000000 : ℝ), (1097005443/2500000000 : ℝ)] ![(31820167248221/100000000000000 : ℝ), (34089917635033/100000000000000 : ℝ), (1704495754877/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162604577/10000000000 : ℝ)|^4365 ≤ (31820167248221/100000000000000 : ℝ)^3341
        have hw : |(4162604577/10000000000 : ℝ)|=(4162604577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2194011011/5000000000 : ℝ)|^4365 ≤ (34089917635033/100000000000000 : ℝ)^3341
        have hw : |(2194011011/5000000000 : ℝ)|=(2194011011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097005443/2500000000 : ℝ)|^4365 ≤ (1704495754877/5000000000000 : ℝ)^3341
        have hw : |(1097005443/2500000000 : ℝ)|=(1097005443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_8 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104349453/500000000 : ℝ)*x 0 + (1036493153/2000000000 : ℝ)*x 1 + (337579533/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104349453/500000000 : ℝ)^4365 ≤ (3227724618431/25000000000000 : ℝ)^3341 := by
    have hnat : (104349453 : ℕ)^4365*25000000000000^3341 ≤ 3227724618431^3341*500000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104349453 500000000 3227724618431 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036493153/2000000000 : ℝ)^4365 ≤ (10592129449323/25000000000000 : ℝ)^3341 := by
    have hnat : (1036493153 : ℕ)^4365*25000000000000^3341 ≤ 10592129449323^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036493153 2000000000 10592129449323 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337579533/625000000 : ℝ)^4365 ≤ (8944116744573/20000000000000 : ℝ)^3341 := by
    have hnat : (337579533 : ℕ)^4365*20000000000000^3341 ≤ 8944116744573^3341*625000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337579533 625000000 8944116744573 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104349453/500000000 : ℝ), (1036493153/2000000000 : ℝ), (337579533/625000000 : ℝ)] ![(3227724618431/25000000000000 : ℝ), (10592129449323/25000000000000 : ℝ), (8944116744573/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104349453/500000000 : ℝ)|^4365 ≤ (3227724618431/25000000000000 : ℝ)^3341
        have hw : |(-104349453/500000000 : ℝ)|=(104349453/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036493153/2000000000 : ℝ)|^4365 ≤ (10592129449323/25000000000000 : ℝ)^3341
        have hw : |(1036493153/2000000000 : ℝ)|=(1036493153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337579533/625000000 : ℝ)|^4365 ≤ (8944116744573/20000000000000 : ℝ)^3341
        have hw : |(337579533/625000000 : ℝ)|=(337579533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_9 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276067363/10000000000 : ℝ)*x 0 + (-196178541/1000000000 : ℝ)*x 1 + (5401272349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276067363/10000000000 : ℝ)^4365 ≤ (10842759592241/25000000000000 : ℝ)^3341 := by
    have hnat : (5276067363 : ℕ)^4365*25000000000000^3341 ≤ 10842759592241^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276067363 10000000000 10842759592241 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196178541/1000000000 : ℝ)^4365 ≤ (5954189915561/50000000000000 : ℝ)^3341 := by
    have hnat : (196178541 : ℕ)^4365*50000000000000^3341 ≤ 5954189915561^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196178541 1000000000 5954189915561 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401272349/10000000000 : ℝ)^4365 ≤ (44720581786567/100000000000000 : ℝ)^3341 := by
    have hnat : (5401272349 : ℕ)^4365*100000000000000^3341 ≤ 44720581786567^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401272349 10000000000 44720581786567 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276067363/10000000000 : ℝ), (-196178541/1000000000 : ℝ), (5401272349/10000000000 : ℝ)] ![(10842759592241/25000000000000 : ℝ), (5954189915561/50000000000000 : ℝ), (44720581786567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276067363/10000000000 : ℝ)|^4365 ≤ (10842759592241/25000000000000 : ℝ)^3341
        have hw : |(5276067363/10000000000 : ℝ)|=(5276067363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196178541/1000000000 : ℝ)|^4365 ≤ (5954189915561/50000000000000 : ℝ)^3341
        have hw : |(-196178541/1000000000 : ℝ)|=(196178541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401272349/10000000000 : ℝ)|^4365 ≤ (44720581786567/100000000000000 : ℝ)^3341
        have hw : |(5401272349/10000000000 : ℝ)|=(5401272349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_10 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055213547/2000000000 : ℝ)*x 0 + (1080254343/2000000000 : ℝ)*x 1 + (-196178577/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055213547/2000000000 : ℝ)^4365 ≤ (43371042364179/100000000000000 : ℝ)^3341 := by
    have hnat : (1055213547 : ℕ)^4365*100000000000000^3341 ≤ 43371042364179^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055213547 2000000000 43371042364179 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080254343/2000000000 : ℝ)^4365 ≤ (22360287464197/50000000000000 : ℝ)^3341 := by
    have hnat : (1080254343 : ℕ)^4365*50000000000000^3341 ≤ 22360287464197^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080254343 2000000000 22360287464197 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196178577/1000000000 : ℝ)^4365 ≤ (11908382686157/100000000000000 : ℝ)^3341 := by
    have hnat : (196178577 : ℕ)^4365*100000000000000^3341 ≤ 11908382686157^3341*1000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196178577 1000000000 11908382686157 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055213547/2000000000 : ℝ), (1080254343/2000000000 : ℝ), (-196178577/1000000000 : ℝ)] ![(43371042364179/100000000000000 : ℝ), (22360287464197/50000000000000 : ℝ), (11908382686157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055213547/2000000000 : ℝ)|^4365 ≤ (43371042364179/100000000000000 : ℝ)^3341
        have hw : |(1055213547/2000000000 : ℝ)|=(1055213547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080254343/2000000000 : ℝ)|^4365 ≤ (22360287464197/50000000000000 : ℝ)^3341
        have hw : |(1080254343/2000000000 : ℝ)|=(1080254343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-196178577/1000000000 : ℝ)|^4365 ≤ (11908382686157/100000000000000 : ℝ)^3341
        have hw : |(-196178577/1000000000 : ℝ)|=(196178577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_11 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (898133829/2000000000 : ℝ)*x 0 + (4223753843/10000000000 : ℝ)*x 1 + (2111877083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898133829/2000000000 : ℝ)^4365 ≤ (7027099638353/20000000000000 : ℝ)^3341 := by
    have hnat : (898133829 : ℕ)^4365*20000000000000^3341 ≤ 7027099638353^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898133829 2000000000 7027099638353 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4223753843/10000000000 : ℝ)^4365 ≤ (32432249274027/100000000000000 : ℝ)^3341 := by
    have hnat : (4223753843 : ℕ)^4365*100000000000000^3341 ≤ 32432249274027^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223753843 10000000000 32432249274027 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111877083/5000000000 : ℝ)^4365 ≤ (16216126257177/50000000000000 : ℝ)^3341 := by
    have hnat : (2111877083 : ℕ)^4365*50000000000000^3341 ≤ 16216126257177^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111877083 5000000000 16216126257177 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(898133829/2000000000 : ℝ), (4223753843/10000000000 : ℝ), (2111877083/5000000000 : ℝ)] ![(7027099638353/20000000000000 : ℝ), (32432249274027/100000000000000 : ℝ), (16216126257177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(898133829/2000000000 : ℝ)|^4365 ≤ (7027099638353/20000000000000 : ℝ)^3341
        have hw : |(898133829/2000000000 : ℝ)|=(898133829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4223753843/10000000000 : ℝ)|^4365 ≤ (32432249274027/100000000000000 : ℝ)^3341
        have hw : |(4223753843/10000000000 : ℝ)|=(4223753843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111877083/5000000000 : ℝ)|^4365 ≤ (16216126257177/50000000000000 : ℝ)^3341
        have hw : |(2111877083/5000000000 : ℝ)|=(2111877083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_12 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-948758773/5000000000 : ℝ)*x 0 + (170902909/312500000 : ℝ)*x 1 + (2627516561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (948758773/5000000000 : ℝ)^4365 ≤ (2280254433007/20000000000000 : ℝ)^3341 := by
    have hnat : (948758773 : ℕ)^4365*20000000000000^3341 ≤ 2280254433007^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948758773 5000000000 2280254433007 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170902909/312500000 : ℝ)^4365 ≤ (45453455398947/100000000000000 : ℝ)^3341 := by
    have hnat : (170902909 : ℕ)^4365*100000000000000^3341 ≤ 45453455398947^3341*312500000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170902909 312500000 45453455398947 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627516561/5000000000 : ℝ)^4365 ≤ (168536220381/390625000000 : ℝ)^3341 := by
    have hnat : (2627516561 : ℕ)^4365*390625000000^3341 ≤ 168536220381^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627516561 5000000000 168536220381 390625000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-948758773/5000000000 : ℝ), (170902909/312500000 : ℝ), (2627516561/5000000000 : ℝ)] ![(2280254433007/20000000000000 : ℝ), (45453455398947/100000000000000 : ℝ), (168536220381/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-948758773/5000000000 : ℝ)|^4365 ≤ (2280254433007/20000000000000 : ℝ)^3341
        have hw : |(-948758773/5000000000 : ℝ)|=(948758773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170902909/312500000 : ℝ)|^4365 ≤ (45453455398947/100000000000000 : ℝ)^3341
        have hw : |(170902909/312500000 : ℝ)|=(170902909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627516561/5000000000 : ℝ)|^4365 ≤ (168536220381/390625000000 : ℝ)^3341
        have hw : |(2627516561/5000000000 : ℝ)|=(2627516561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_13 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378515409/10000000000 : ℝ)*x 0 + (-1010499991/5000000000 : ℝ)*x 1 + (5255033881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378515409/10000000000 : ℝ)^4365 ≤ (22237286043767/50000000000000 : ℝ)^3341 := by
    have hnat : (5378515409 : ℕ)^4365*50000000000000^3341 ≤ 22237286043767^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378515409 10000000000 22237286043767 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010499991/5000000000 : ℝ)^4365 ≤ (12380147332127/100000000000000 : ℝ)^3341 := by
    have hnat : (1010499991 : ℕ)^4365*100000000000000^3341 ≤ 12380147332127^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010499991 5000000000 12380147332127 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255033881/10000000000 : ℝ)^4365 ≤ (4314528055909/10000000000000 : ℝ)^3341 := by
    have hnat : (5255033881 : ℕ)^4365*10000000000000^3341 ≤ 4314528055909^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255033881 10000000000 4314528055909 10000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378515409/10000000000 : ℝ), (-1010499991/5000000000 : ℝ), (5255033881/10000000000 : ℝ)] ![(22237286043767/50000000000000 : ℝ), (12380147332127/100000000000000 : ℝ), (4314528055909/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378515409/10000000000 : ℝ)|^4365 ≤ (22237286043767/50000000000000 : ℝ)^3341
        have hw : |(5378515409/10000000000 : ℝ)|=(5378515409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1010499991/5000000000 : ℝ)|^4365 ≤ (12380147332127/100000000000000 : ℝ)^3341
        have hw : |(-1010499991/5000000000 : ℝ)|=(1010499991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255033881/10000000000 : ℝ)|^4365 ≤ (4314528055909/10000000000000 : ℝ)^3341
        have hw : |(5255033881/10000000000 : ℝ)|=(5255033881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_14 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075703277/2000000000 : ℝ)*x 0 + (2627516617/5000000000 : ℝ)*x 1 + (-2020999533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075703277/2000000000 : ℝ)^4365 ≤ (11118645657893/25000000000000 : ℝ)^3341 := by
    have hnat : (1075703277 : ℕ)^4365*25000000000000^3341 ≤ 11118645657893^3341*2000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075703277 2000000000 11118645657893 25000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627516617/5000000000 : ℝ)^4365 ≤ (1725810944757/4000000000000 : ℝ)^3341 := by
    have hnat : (2627516617 : ℕ)^4365*4000000000000^3341 ≤ 1725810944757^3341*5000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627516617 5000000000 1725810944757 4000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020999533/10000000000 : ℝ)^4365 ≤ (12380143738661/100000000000000 : ℝ)^3341 := by
    have hnat : (2020999533 : ℕ)^4365*100000000000000^3341 ≤ 12380143738661^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020999533 10000000000 12380143738661 100000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075703277/2000000000 : ℝ), (2627516617/5000000000 : ℝ), (-2020999533/10000000000 : ℝ)] ![(11118645657893/25000000000000 : ℝ), (1725810944757/4000000000000 : ℝ), (12380143738661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075703277/2000000000 : ℝ)|^4365 ≤ (11118645657893/25000000000000 : ℝ)^3341
        have hw : |(1075703277/2000000000 : ℝ)|=(1075703277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627516617/5000000000 : ℝ)|^4365 ≤ (1725810944757/4000000000000 : ℝ)^3341
        have hw : |(2627516617/5000000000 : ℝ)|=(2627516617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2020999533/10000000000 : ℝ)|^4365 ≤ (12380143738661/100000000000000 : ℝ)^3341
        have hw : |(-2020999533/10000000000 : ℝ)|=(2020999533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1405_box_15 (p : ℝ) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4135126847/10000000000 : ℝ)*x 0 + (4401520151/10000000000 : ℝ)*x 1 + (275095043/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135126847/10000000000 : ℝ)^4365 ≤ (15773009430049/50000000000000 : ℝ)^3341 := by
    have hnat : (4135126847 : ℕ)^4365*50000000000000^3341 ≤ 15773009430049^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135126847 10000000000 15773009430049 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4401520151/10000000000 : ℝ)^4365 ≤ (6845397566417/20000000000000 : ℝ)^3341 := by
    have hnat : (4401520151 : ℕ)^4365*20000000000000^3341 ≤ 6845397566417^3341*10000000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401520151 10000000000 6845397566417 20000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275095043/625000000 : ℝ)^4365 ≤ (17113496643877/50000000000000 : ℝ)^3341 := by
    have hnat : (275095043 : ℕ)^4365*50000000000000^3341 ≤ 17113496643877^3341*625000000^4365 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275095043 625000000 17113496643877 50000000000000 4365 3341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4365/1024 : ℝ)) 4365 3341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135126847/10000000000 : ℝ), (4401520151/10000000000 : ℝ), (275095043/625000000 : ℝ)] ![(15773009430049/50000000000000 : ℝ), (6845397566417/20000000000000 : ℝ), (17113496643877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135126847/10000000000 : ℝ)|^4365 ≤ (15773009430049/50000000000000 : ℝ)^3341
        have hw : |(4135126847/10000000000 : ℝ)|=(4135126847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4401520151/10000000000 : ℝ)|^4365 ≤ (6845397566417/20000000000000 : ℝ)^3341
        have hw : |(4401520151/10000000000 : ℝ)|=(4401520151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275095043/625000000 : ℝ)|^4365 ≤ (17113496643877/50000000000000 : ℝ)^3341
        have hw : |(275095043/625000000 : ℝ)|=(275095043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1405_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12577/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11813/20000 : ℝ) ∧ (16063/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42297/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1843/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1843/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1843/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1843/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1843/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1843/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1129/10000 : ℝ) ^ (1091/256 : ℝ) ≤ (9180112646023729/100000000000000000000 : ℝ) := by
    have hpowers : (1129/10000 : ℝ)^1091 ≤ (9180112646023729/100000000000000000000 : ℝ)^256 := by
      have hnat : (1129 : ℕ)^1091*100000000000000000000^256 ≤ 9180112646023729^256*10000^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1129 10000 9180112646023729 100000000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1129/10000 : ℝ)) (X := (9180112646023729/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1843/12500 : ℝ) ^ (1091/256 : ℝ) ≤ (1789585068516131/6250000000000000000 : ℝ) := by
    have hpowers : (1843/12500 : ℝ)^1091 ≤ (1789585068516131/6250000000000000000 : ℝ)^256 := by
      have hnat : (1843 : ℕ)^1091*6250000000000000000^256 ≤ 1789585068516131^256*12500^1091 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1843 12500 1789585068516131 6250000000000000000 1091 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1843/12500 : ℝ)) (X := (1789585068516131/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009180112646023729/50000000000000000000 : ℝ) ≤ (2000086157423867/2000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (50009180112646023729/50000000000000000000 : ℝ)^256 ≤ (2000086157423867/2000000000000000 : ℝ)^1091 := by
      have hnat : (50009180112646023729 : ℕ)^256*2000000000000000^1091 ≤ 2000086157423867^1091*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009180112646023729 50000000000000000000 2000086157423867 2000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000086157423867/2000000000000000 : ℝ)) (X := (50009180112646023729/50000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001512538949691273/4000000000000000000 : ℝ) ≤ (2500221788469891/2500000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (4001512538949691273/4000000000000000000 : ℝ)^256 ≤ (2500221788469891/2500000000000000 : ℝ)^1091 := by
      have hnat : (4001512538949691273 : ℕ)^256*2500000000000000^1091 ≤ 2500221788469891^1091*4000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001512538949691273 4000000000000000000 2500221788469891 2500000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500221788469891/2500000000000000 : ℝ)) (X := (4001512538949691273/4000000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126789585068516131/3125000000000000000 : ℝ) ≤ (10001343520639793/10000000000000000 : ℝ) ^ (1091/256 : ℝ) := by
    have hpowers : (3126789585068516131/3125000000000000000 : ℝ)^256 ≤ (10001343520639793/10000000000000000 : ℝ)^1091 := by
      have hnat : (3126789585068516131 : ℕ)^256*10000000000000000^1091 ≤ 10001343520639793^1091*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126789585068516131 3125000000000000000 10001343520639793 10000000000000000 256 1091 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001343520639793/10000000000000000 : ℝ)) (X := (3126789585068516131/3125000000000000000 : ℝ)) (by norm_num) 1091 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9180112646023729/100000000000000000000 : ℝ) ≤ ((3453118317726421227/3454000000000000000 : ℝ)+2*(456366760229/345400000000000 : ℝ)*(1129/10000 : ℝ))^(1091/256 : ℝ) := by
    rw [show (3453118317726421227/3454000000000000000 : ℝ)+2*(456366760229/345400000000000 : ℝ)*(1129/10000 : ℝ)=(2000086157423867/2000000000000000 : ℝ) by norm_num, show 1+2*(9180112646023729/100000000000000000000 : ℝ)=(50009180112646023729/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1789585068516131/6250000000000000000 : ℝ)+(9180112646023729/100000000000000000000 : ℝ) ≤ ((3453118317726421227/3454000000000000000 : ℝ)+(456366760229/345400000000000 : ℝ)*((1843/12500 : ℝ)+(1129/10000 : ℝ)))^(1091/256 : ℝ) := by
    rw [show (3453118317726421227/3454000000000000000 : ℝ)+(456366760229/345400000000000 : ℝ)*((1843/12500 : ℝ)+(1129/10000 : ℝ))=(2500221788469891/2500000000000000 : ℝ) by norm_num, show 1+(1789585068516131/6250000000000000000 : ℝ)+(9180112646023729/100000000000000000000 : ℝ)=(4001512538949691273/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1789585068516131/6250000000000000000 : ℝ) ≤ ((3453118317726421227/3454000000000000000 : ℝ)+2*(456366760229/345400000000000 : ℝ)*(1843/12500 : ℝ))^(1091/256 : ℝ) := by
    rw [show (3453118317726421227/3454000000000000000 : ℝ)+2*(456366760229/345400000000000 : ℝ)*(1843/12500 : ℝ)=(10001343520639793/10000000000000000 : ℝ) by norm_num, show 1+2*(1789585068516131/6250000000000000000 : ℝ)=(3126789585068516131/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3453118317726421227/3454000000000000000 : ℝ)*(X 1 0+X 2 0)+(456366760229/345400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (3453118317726421227/3454000000000000000 : ℝ)) (alpha := (456366760229/345400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3453118317726421227/3454000000000000000 : ℝ)*(X 0 1+X 2 1)+(456366760229/345400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (3453118317726421227/3454000000000000000 : ℝ)) (alpha := (456366760229/345400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3453118317726421227/3454000000000000000 : ℝ)*(X 0 2+X 1 2)+(456366760229/345400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1091/256 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (1843/12500 : ℝ)) (c := (3453118317726421227/3454000000000000000 : ℝ)) (alpha := (456366760229/345400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-22854381/125000000 : ℝ)*X 0 0+(5387283797/10000000000 : ℝ)*X 0 1+(2693641457/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285871811/10000000000 : ℝ)*X 1 0+(-983787969/5000000000 : ℝ)*X 1 1+(673410323/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642936357/5000000000 : ℝ)*X 2 0+(673410353/1250000000 : ℝ)*X 2 1+(-1967574389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((891441137/2000000000 : ℝ)*X 0 0+(4240772853/10000000000 : ℝ)*X 0 1+(1060193259/2500000000 : ℝ)*X 0 2+(891441137/2000000000 : ℝ)*X 1 0+(4240772853/10000000000 : ℝ)*X 1 1+(1060193259/2500000000 : ℝ)*X 1 2+(891441137/2000000000 : ℝ)*X 2 0+(4240772853/10000000000 : ℝ)*X 2 1+(1060193259/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-215593491/1000000000 : ℝ)*X 0 0+(26330733/50000000 : ℝ)*X 0 1+(2633073543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1342683181/2500000000 : ℝ)*X 1 0+(-1008301483/5000000000 : ℝ)*X 1 1+(5266146383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370732621/10000000000 : ℝ)*X 2 0+(5266146831/10000000000 : ℝ)*X 2 1+(-252075313/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4162604577/10000000000 : ℝ)*X 0 0+(2194011011/5000000000 : ℝ)*X 0 1+(1097005443/2500000000 : ℝ)*X 0 2+(4162604577/10000000000 : ℝ)*X 1 0+(2194011011/5000000000 : ℝ)*X 1 1+(1097005443/2500000000 : ℝ)*X 1 2+(4162604577/10000000000 : ℝ)*X 2 0+(2194011011/5000000000 : ℝ)*X 2 1+(1097005443/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-104349453/500000000 : ℝ)*X 0 0+(1036493153/2000000000 : ℝ)*X 0 1+(337579533/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276067363/10000000000 : ℝ)*X 1 0+(-196178541/1000000000 : ℝ)*X 1 1+(5401272349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1055213547/2000000000 : ℝ)*X 2 0+(1080254343/2000000000 : ℝ)*X 2 1+(-196178577/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((898133829/2000000000 : ℝ)*X 0 0+(4223753843/10000000000 : ℝ)*X 0 1+(2111877083/5000000000 : ℝ)*X 0 2+(898133829/2000000000 : ℝ)*X 1 0+(4223753843/10000000000 : ℝ)*X 1 1+(2111877083/5000000000 : ℝ)*X 1 2+(898133829/2000000000 : ℝ)*X 2 0+(4223753843/10000000000 : ℝ)*X 2 1+(2111877083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-948758773/5000000000 : ℝ)*X 0 0+(170902909/312500000 : ℝ)*X 0 1+(2627516561/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378515409/10000000000 : ℝ)*X 1 0+(-1010499991/5000000000 : ℝ)*X 1 1+(5255033881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1075703277/2000000000 : ℝ)*X 2 0+(2627516617/5000000000 : ℝ)*X 2 1+(-2020999533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4135126847/10000000000 : ℝ)*X 0 0+(4401520151/10000000000 : ℝ)*X 0 1+(275095043/625000000 : ℝ)*X 0 2+(4135126847/10000000000 : ℝ)*X 1 0+(4401520151/10000000000 : ℝ)*X 1 1+(275095043/625000000 : ℝ)*X 1 2+(4135126847/10000000000 : ℝ)*X 2 0+(4401520151/10000000000 : ℝ)*X 2 1+(275095043/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1405_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12577/20000 : ℝ) ≤ (-1085987600995146357973040420109/1727000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7861711/12500000000000 : ℝ)*(lower0) + (5379057/5000000000000 : ℝ)*(lower2) + (7929127/6250000000000 : ℝ)*(lower3) + (14499871/100000000000000 : ℝ)*(lower4) + (2990451242131101/100000000000000 : ℝ)*(major0) + (2990451242131101/100000000000000 : ℝ)*(major1) + (1495225621065551/50000000000000 : ℝ)*(major2) + (13319351531/100000000000000 : ℝ)*(sp1) + (16398952849913/400000000000 : ℝ)*(sp4) + (12811640291021/312500000000 : ℝ)*(sp5) + (4099709589643327/100000000000000 : ℝ)*(sp6) + (1902075228932603/100000000000000 : ℝ)*(sp7) + (28622834923/100000000000000 : ℝ)*(sp14) + (5000793521/10000000000000 : ℝ)*(sp15) + (1902125236867813/100000000000000 : ℝ)*(f.failure) + (16398952849913/400000000000 : ℝ)*(f.sum) + (149152475532053/34540000000000000000000000000 : ℝ)*base66 + (2692884360803539073/345400000000000000000000000000000 : ℝ)*base68 + (1161291022656296077/172700000000000000000000000000000 : ℝ)*base69 + (4348260402071939073/345400000000000000000000000000000 : ℝ)*base72 + (116077142288367/34540000000000000000000000000 : ℝ)*base73 + (100427672793496077/172700000000000000000000000000000 : ℝ)*base75 + (1687788649719629073/345400000000000000000000000000000 : ℝ)*base78 + (884349382548429073/345400000000000000000000000000000 : ℝ)*base80 + (72384478422701/17270000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (75704721/10000000000000000000000 : ℝ)*base89 + (75704721/10000000000000000000000 : ℝ)*base91 + (24295279/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11813/20000 : ℝ) ≤ (2040193235971748152472358146709/3454000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42971217/10000000000000 : ℝ)*(lower1) + (237061729/100000000000000 : ℝ)*(lower2) + (11219981/2000000000000 : ℝ)*(upper4) + (122450552212189/4000000000000 : ℝ)*(major0) + (122450552212189/4000000000000 : ℝ)*(major1) + (122450552212189/4000000000000 : ℝ)*(major2) + (4155651560134951/100000000000000 : ℝ)*(sp0) + (259702898234187/6250000000000 : ℝ)*(sp1) + (129864719476421/3125000000000 : ℝ)*(sp2) + (194716294070321/10000000000000 : ℝ)*(sp3) + (682017001/100000000000000 : ℝ)*(sp6) + (3780741311/100000000000000 : ℝ)*(sp7) + (20145127523/100000000000000 : ℝ)*(sp8) + (212666757741/50000000000000 : ℝ)*(sp9) + (1947166721444521/100000000000000 : ℝ)*(f.failure) + (2077835852631237/50000000000000 : ℝ)*(f.sum) + (23582053368993/3454000000000000000000000000 : ℝ)*base66 + (61701974150878097/13816000000000000000000000000000 : ℝ)*base68 + (27618399471614097/13816000000000000000000000000000 : ℝ)*base70 + (192664359856854097/13816000000000000000000000000000 : ℝ)*base72 + (7602356551781/3454000000000000000000000000 : ℝ)*base73 + (130587378333022097/13816000000000000000000000000000 : ℝ)*base76 + (41294663287070097/13816000000000000000000000000000 : ℝ)*base78 + (43531628031049903/13816000000000000000000000000000 : ℝ)*base79 + (3790791936551/690800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11449157/10000000000000000000000 : ℝ)*base89 + (11449157/10000000000000000000000 : ℝ)*base91 + (11449157/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16063/20000 : ℝ) ≤ (69354219405277002170125449481569/86350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55410973/50000000000000 : ℝ)*(upper0) + (70544787/100000000000000 : ℝ)*(upper1) + (29749197/50000000000000 : ℝ)*(upper2) + (3370429271609501/100000000000000 : ℝ)*(major0) + (3370429271609501/100000000000000 : ℝ)*(major1) + (1685214635804751/50000000000000 : ℝ)*(major2) + (286395111641/100000000000000 : ℝ)*(sp1) + (26151089149/50000000000000 : ℝ)*(sp2) + (20088365499/50000000000000 : ℝ)*(sp3) + (3048449373/10000000000000 : ℝ)*(sp4) + (4570239082663377/100000000000000 : ℝ)*(sp8) + (4569983172045467/100000000000000 : ℝ)*(sp9) + (457021726497881/10000000000000 : ℝ)*(sp10) + (267972034610181/12500000000000 : ℝ)*(sp11) + (1071908226806223/50000000000000 : ℝ)*(f.failure) + (1142567391789277/25000000000000 : ℝ)*(f.sum) + (392269450891/220000000000000000000000000 : ℝ)*base65 + (1403903179360657727/345400000000000000000000000000000 : ℝ)*base67 + (2375791574236094477/172700000000000000000000000000000 : ℝ)*base69 + (1068084070333942273/345400000000000000000000000000000 : ℝ)*base72 + (1645325572309/220000000000000000000000000 : ℝ)*base74 + (1808251969640394477/172700000000000000000000000000000 : ℝ)*base75 + (834394530986232273/345400000000000000000000000000000 : ℝ)*base78 + (71032556774567727/345400000000000000000000000000000 : ℝ)*base79 + (119628724435749/17270000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2740691/5000000000000000000000 : ℝ)*base89 + (2740691/5000000000000000000000 : ℝ)*base91 + (47259309/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42297/50000 : ℝ) ≤ (-13280922387886490019495661936551/15700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44470693/20000000000000 : ℝ)*(lower1) + (181800353/50000000000000 : ℝ)*(lower2) + (156383971/100000000000000 : ℝ)*(upper5) + (170381165765401/5000000000000 : ℝ)*(major0) + (170381165765401/5000000000000 : ℝ)*(major1) + (3407623315308021/100000000000000 : ℝ)*(major2) + (17478606777/100000000000000 : ℝ)*(sp0) + (88730318883/100000000000000 : ℝ)*(sp5) + (103953522821/50000000000000 : ℝ)*(sp6) + (59964528827/50000000000000 : ℝ)*(sp7) + (2337976054168251/50000000000000 : ℝ)*(sp12) + (1168970214156099/25000000000000 : ℝ)*(sp13) + (2337880839948819/50000000000000 : ℝ)*(sp14) + (1083677201031419/50000000000000 : ℝ)*(sp15) + (2167474331120491/100000000000000 : ℝ)*(f.failure) + (58449619836791/1250000000000 : ℝ)*(f.sum) + (266697751524291/34540000000000000000000000000 : ℝ)*base66 + (22560006120018043/1570000000000000000000000000000 : ℝ)*base68 + (1427170875091961767/345400000000000000000000000000000 : ℝ)*base69 + (16468946245548043/1570000000000000000000000000000 : ℝ)*base72 + (434179102371651/34540000000000000000000000000 : ℝ)*base74 + (795129064799761767/345400000000000000000000000000000 : ℝ)*base75 + (299453656118262973/17270000000000000000000000000000 : ℝ)*base78 + (88923483897542973/17270000000000000000000000000000 : ℝ)*base80 + (1693300903303/431750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (78251647/10000000000000000000000 : ℝ)*base89 + (78251647/10000000000000000000000 : ℝ)*base91 + (21748353/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1405_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1843/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12577/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(11813/20000 : ℝ) else (16063/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42297/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1405_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1405_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12577/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(11813/20000 : ℝ) else (16063/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42297/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1405_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1405_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1091/256 : ℝ) ≤ p) (hpb : p ≤ (4365/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157216317/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12577/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(11813/20000 : ℝ) else (16063/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42297/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1405_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
